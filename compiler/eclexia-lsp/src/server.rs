// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! LSP server implementation for Eclexia.

use dashmap::DashMap;
use eclexia_ast::span::Span;
use eclexia_ast::{Item, SourceFile, TypeId, TypeKind};
use std::collections::HashMap;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer};

use crate::symbols::SymbolTable;

/// Convert LSP line:column position to byte offset
fn line_col_to_offset(text: &str, line: u32, character: u32) -> u32 {
    let mut current_line = 0u32;
    let mut current_col = 0u32;
    let mut offset = 0u32;

    for ch in text.chars() {
        if current_line == line && current_col == character {
            return offset;
        }

        if ch == '\n' {
            current_line += 1;
            current_col = 0;
        } else {
            current_col += 1;
        }

        offset += ch.len_utf8() as u32;
    }

    offset
}

/// Format a syntactic type expression from the AST for display.
fn format_type(ty_id: TypeId, file: &SourceFile) -> String {
    let ty = &file.types[ty_id];
    match &ty.kind {
        TypeKind::Named { name, args } => {
            if args.is_empty() {
                name.to_string()
            } else {
                let arg_strs: Vec<_> = args.iter().map(|a| format_type(*a, file)).collect();
                format!("{}<{}>", name, arg_strs.join(", "))
            }
        }
        TypeKind::Function { params, ret } => {
            let param_strs: Vec<_> = params.iter().map(|p| format_type(*p, file)).collect();
            format!(
                "fn({}) -> {}",
                param_strs.join(", "),
                format_type(*ret, file)
            )
        }
        TypeKind::Tuple(elems) => {
            let elem_strs: Vec<_> = elems.iter().map(|e| format_type(*e, file)).collect();
            format!("({})", elem_strs.join(", "))
        }
        TypeKind::Array { elem, size } => match size {
            Some(s) => format!("[{}; {}]", format_type(*elem, file), s),
            None => format!("[{}]", format_type(*elem, file)),
        },
        TypeKind::Resource { base, .. } => base.to_string(),
        TypeKind::Reference { ty, mutable } => {
            if *mutable {
                format!("&mut {}", format_type(*ty, file))
            } else {
                format!("&{}", format_type(*ty, file))
            }
        }
        TypeKind::Optional(ty) => format!("{}?", format_type(*ty, file)),
        TypeKind::Infer => "_".to_string(),
        TypeKind::Error => "?".to_string(),
    }
}

/// Find the function name and active parameter index at cursor position.
/// Scans backwards from the cursor to find the nearest unmatched `(` and counts commas.
fn find_call_context(text: &str, offset: usize) -> Option<(String, usize)> {
    let bytes = text.as_bytes();
    let end = offset.min(bytes.len());
    let mut depth: i32 = 0;
    let mut comma_count = 0;
    let mut i = end;

    while i > 0 {
        i -= 1;
        match bytes[i] {
            b')' => depth += 1,
            b'(' => {
                if depth == 0 {
                    // Found unmatched opening paren — extract function name before it
                    let mut name_end = i;
                    while name_end > 0 && bytes[name_end - 1] == b' ' {
                        name_end -= 1;
                    }
                    let mut name_start = name_end;
                    while name_start > 0
                        && (bytes[name_start - 1].is_ascii_alphanumeric()
                            || bytes[name_start - 1] == b'_')
                    {
                        name_start -= 1;
                    }
                    if name_start < name_end {
                        let name =
                            String::from_utf8_lossy(&bytes[name_start..name_end]).to_string();
                        return Some((name, comma_count));
                    }
                    return None;
                }
                depth -= 1;
            }
            b',' if depth == 0 => comma_count += 1,
            _ => {}
        }
    }

    None
}

/// Extract the identifier prefix before the cursor position.
/// Scans backwards from offset to find the start of an identifier.
fn extract_prefix(text: &str, offset: usize) -> String {
    let bytes = text.as_bytes();
    let end = offset.min(bytes.len());

    // Scan backwards to find the start of the identifier
    let mut start = end;
    while start > 0 && (bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_') {
        start -= 1;
    }

    if start < end {
        String::from_utf8_lossy(&bytes[start..end]).to_string()
    } else {
        String::new()
    }
}

/// Document state stored in memory.
struct Document {
    /// The document text
    text: String,
    /// Document version
    #[allow(dead_code)]
    version: i32,
    /// Symbol table for this document
    symbols: Option<SymbolTable>,
    /// Parsed AST (available when parsing succeeds)
    parsed: Option<SourceFile>,
}

/// The Eclexia language server.
pub struct EclexiaLanguageServer {
    /// LSP client handle for sending messages to the editor
    client: Client,
    /// In-memory document storage
    documents: DashMap<Url, Document>,
}

impl EclexiaLanguageServer {
    /// Create a new language server instance.
    pub fn new(client: Client) -> Self {
        Self {
            client,
            documents: DashMap::new(),
        }
    }

    /// Analyze a document and publish diagnostics.
    /// Returns the symbol table if parsing succeeded.
    async fn analyze_document(
        &self,
        uri: &Url,
        text: &str,
    ) -> (Option<SymbolTable>, Option<SourceFile>) {
        let mut diagnostics = Vec::new();

        // Parse the document
        let (file, parse_errors) = eclexia_parser::parse(text);

        // Build symbol table if parsing succeeded
        let symbols = if parse_errors.is_empty() {
            Some(SymbolTable::build(&file, text))
        } else {
            None
        };

        // Convert parse errors to diagnostics
        for error in &parse_errors {
            let span = error.span();
            let start_lc = span.start_linecol(text);
            let end_lc = span.end_linecol(text);

            let diagnostic = Diagnostic {
                range: Range {
                    start: Position {
                        line: start_lc.line.saturating_sub(1), // LSP uses 0-indexed lines
                        character: start_lc.col.saturating_sub(1), // LSP uses 0-indexed columns
                    },
                    end: Position {
                        line: end_lc.line.saturating_sub(1),
                        character: end_lc.col.saturating_sub(1),
                    },
                },
                severity: Some(DiagnosticSeverity::ERROR),
                code: None,
                code_description: None,
                source: Some("eclexia-parser".to_string()),
                message: error.to_string(), // Use Display implementation, not format_with_source
                related_information: None,
                tags: None,
                data: None,
            };
            diagnostics.push(diagnostic);
        }

        // If parsing succeeded, run type checker and linter
        if parse_errors.is_empty() {
            let type_errors = eclexia_typeck::check(&file);

            // Convert type errors to diagnostics
            for error in type_errors {
                let span = error.span();
                let start_lc = span.start_linecol(text);
                let end_lc = span.end_linecol(text);

                let diagnostic = Diagnostic {
                    range: Range {
                        start: Position {
                            line: start_lc.line.saturating_sub(1), // LSP uses 0-indexed lines
                            character: start_lc.col.saturating_sub(1), // LSP uses 0-indexed columns
                        },
                        end: Position {
                            line: end_lc.line.saturating_sub(1),
                            character: end_lc.col.saturating_sub(1),
                        },
                    },
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: None,
                    code_description: None,
                    source: Some("eclexia-typeck".to_string()),
                    message: error.to_string(), // Use Display implementation
                    related_information: None,
                    tags: None,
                    data: None,
                };
                diagnostics.push(diagnostic);
            }

            // Run linter
            let linter = eclexia_lint::Linter::new();
            let lint_diagnostics = linter.lint(&file, text);

            // Convert lint diagnostics to LSP diagnostics
            for lint_diag in lint_diagnostics {
                let start_lc = lint_diag.span.start_linecol(text);
                let end_lc = lint_diag.span.end_linecol(text);

                let severity = match lint_diag.severity {
                    eclexia_lint::diagnostics::Severity::Error => DiagnosticSeverity::ERROR,
                    eclexia_lint::diagnostics::Severity::Warning => DiagnosticSeverity::WARNING,
                    eclexia_lint::diagnostics::Severity::Info => DiagnosticSeverity::INFORMATION,
                };

                let diagnostic = Diagnostic {
                    range: Range {
                        start: Position {
                            line: start_lc.line.saturating_sub(1),
                            character: start_lc.col.saturating_sub(1),
                        },
                        end: Position {
                            line: end_lc.line.saturating_sub(1),
                            character: end_lc.col.saturating_sub(1),
                        },
                    },
                    severity: Some(severity),
                    code: Some(tower_lsp::lsp_types::NumberOrString::String(
                        lint_diag.rule.clone(),
                    )),
                    code_description: None,
                    source: Some("eclexia-lint".to_string()),
                    message: lint_diag.message,
                    related_information: None,
                    tags: None,
                    data: None,
                };
                diagnostics.push(diagnostic);
            }
        }

        // Publish diagnostics to the client
        self.client
            .publish_diagnostics(uri.clone(), diagnostics, None)
            .await;

        let parsed = if parse_errors.is_empty() {
            Some(file)
        } else {
            None
        };

        (symbols, parsed)
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for EclexiaLanguageServer {
    async fn initialize(&self, _params: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                completion_provider: Some(CompletionOptions {
                    resolve_provider: Some(false),
                    trigger_characters: Some(vec![".".to_string()]),
                    ..Default::default()
                }),
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                document_symbol_provider: Some(OneOf::Left(true)),
                document_formatting_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Left(true)),
                signature_help_provider: Some(SignatureHelpOptions {
                    trigger_characters: Some(vec!["(".to_string(), ",".to_string()]),
                    retrigger_characters: None,
                    work_done_progress_options: Default::default(),
                }),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "eclexia-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _params: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "Eclexia language server initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let version = params.text_document.version;

        // Analyze and publish diagnostics, get symbol table
        let (symbols, parsed) = self.analyze_document(&uri, &text).await;

        // Store document with symbol table
        self.documents.insert(
            uri.clone(),
            Document {
                text: text.clone(),
                version,
                symbols,
                parsed,
            },
        );
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;

        if let Some(change) = params.content_changes.first() {
            let text = change.text.clone();

            // Analyze and publish diagnostics, get symbol table
            let (symbols, parsed) = self.analyze_document(&uri, &text).await;

            // Update document with symbol table
            self.documents.insert(
                uri.clone(),
                Document {
                    text: text.clone(),
                    version,
                    symbols,
                    parsed,
                },
            );
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let uri = params.text_document.uri;

        if let Some(doc) = self.documents.get(&uri) {
            let text = doc.text.clone();
            drop(doc); // Release the lock before async call

            // Re-analyze and update symbol table
            let (symbols, parsed) = self.analyze_document(&uri, &text).await;

            // Update stored symbols and parsed AST
            if let Some(mut doc) = self.documents.get_mut(&uri) {
                doc.symbols = symbols;
                doc.parsed = parsed;
            }
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;

        // Remove document from storage
        self.documents.remove(&uri);

        // Clear diagnostics
        self.client.publish_diagnostics(uri, Vec::new(), None).await;
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        if let Some(doc) = self.documents.get(&uri) {
            if let Some(ref symbols) = doc.symbols {
                // Convert LSP position to byte offset
                let byte_offset = line_col_to_offset(&doc.text, position.line, position.character);
                let position_span = Span::new(byte_offset, byte_offset + 1);

                // Find the symbol at cursor position
                if let Some(symbol) = symbols.symbol_at_position(position_span) {
                    let mut hover_text = String::new();

                    // Symbol name and kind
                    hover_text.push_str(&format!("**{}**", symbol.name));

                    // Add kind information
                    let kind_str = match symbol.kind {
                        crate::symbols::SymbolKind::Function => "function",
                        crate::symbols::SymbolKind::AdaptiveFunction => "adaptive function",
                        crate::symbols::SymbolKind::TypeDef => "type",
                        crate::symbols::SymbolKind::Const => "constant",
                        crate::symbols::SymbolKind::Variable => "variable",
                        crate::symbols::SymbolKind::Parameter => "parameter",
                        crate::symbols::SymbolKind::Method => "method",
                        crate::symbols::SymbolKind::Field => "field",
                        crate::symbols::SymbolKind::EnumVariant => "enum variant",
                        crate::symbols::SymbolKind::Module => "module",
                        crate::symbols::SymbolKind::Static => "static",
                        crate::symbols::SymbolKind::Effect => "effect",
                        crate::symbols::SymbolKind::Trait => "trait",
                    };
                    hover_text.push_str(&format!("\n\n*{}*", kind_str));

                    // Add documentation if available
                    if let Some(ref doc) = symbol.doc {
                        hover_text.push_str("\n\n---\n\n");
                        hover_text.push_str(doc);
                    }

                    return Ok(Some(Hover {
                        contents: HoverContents::Markup(MarkupContent {
                            kind: MarkupKind::Markdown,
                            value: hover_text,
                        }),
                        range: None,
                    }));
                }
            }
        }

        Ok(None)
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        if let Some(doc) = self.documents.get(&uri) {
            if let Some(ref symbols) = doc.symbols {
                let mut completions = Vec::new();

                // Extract prefix by scanning backwards from cursor
                let byte_offset = line_col_to_offset(&doc.text, position.line, position.character);
                let prefix = extract_prefix(&doc.text, byte_offset as usize);

                // Add keyword completions
                let keywords = vec![
                    "fn",
                    "let",
                    "if",
                    "else",
                    "match",
                    "return",
                    "true",
                    "false",
                    "resource",
                    "adaptive",
                    "shadow",
                    "budget",
                    "dimension",
                    "@requires",
                    "@provides",
                    "@builtin",
                    "@test",
                    "@bench",
                    "import",
                    "type",
                    "const",
                    "for",
                    "while",
                    "break",
                    "continue",
                ];

                for keyword in keywords {
                    if prefix.is_empty() || keyword.starts_with(&prefix) {
                        completions.push(CompletionItem {
                            label: keyword.to_string(),
                            label_details: None,
                            kind: Some(CompletionItemKind::KEYWORD),
                            detail: Some("keyword".to_string()),
                            documentation: None,
                            deprecated: Some(false),
                            preselect: None,
                            sort_text: Some(format!("0_{}", keyword)), // Keywords first
                            filter_text: None,
                            insert_text: None,
                            insert_text_format: None,
                            insert_text_mode: None,
                            text_edit: None,
                            additional_text_edits: None,
                            command: None,
                            commit_characters: None,
                            data: None,
                            tags: None,
                        });
                    }
                }

                // Suggest symbols filtered by prefix
                for symbol in symbols.global_symbols() {
                    let name = symbol.name.as_str();

                    // Filter by prefix
                    if !prefix.is_empty() && !name.starts_with(&prefix) {
                        continue;
                    }

                    let kind = match symbol.kind {
                        crate::symbols::SymbolKind::Function => CompletionItemKind::FUNCTION,
                        crate::symbols::SymbolKind::AdaptiveFunction => {
                            CompletionItemKind::FUNCTION
                        }
                        crate::symbols::SymbolKind::TypeDef => CompletionItemKind::CLASS,
                        crate::symbols::SymbolKind::Const => CompletionItemKind::CONSTANT,
                        crate::symbols::SymbolKind::Variable => CompletionItemKind::VARIABLE,
                        crate::symbols::SymbolKind::Parameter => CompletionItemKind::VARIABLE,
                        crate::symbols::SymbolKind::Method => CompletionItemKind::METHOD,
                        crate::symbols::SymbolKind::Field => CompletionItemKind::FIELD,
                        crate::symbols::SymbolKind::EnumVariant => CompletionItemKind::ENUM_MEMBER,
                        crate::symbols::SymbolKind::Module => CompletionItemKind::MODULE,
                        crate::symbols::SymbolKind::Static => CompletionItemKind::VARIABLE,
                        crate::symbols::SymbolKind::Effect => CompletionItemKind::INTERFACE,
                        crate::symbols::SymbolKind::Trait => CompletionItemKind::INTERFACE,
                    };

                    let detail = symbol.doc.clone();

                    // Sort: exact match > prefix match
                    let sort_text = if name == prefix {
                        format!("1_{}", name) // Exact match
                    } else {
                        format!("2_{}", name) // Prefix match
                    };

                    completions.push(CompletionItem {
                        label: symbol.name.to_string(),
                        label_details: None,
                        kind: Some(kind),
                        detail,
                        documentation: None,
                        deprecated: Some(false),
                        preselect: None,
                        sort_text: Some(sort_text),
                        filter_text: None,
                        insert_text: None,
                        insert_text_format: None,
                        insert_text_mode: None,
                        text_edit: None,
                        additional_text_edits: None,
                        command: None,
                        commit_characters: None,
                        data: None,
                        tags: None,
                    });
                }

                return Ok(Some(CompletionResponse::Array(completions)));
            }
        }

        Ok(Some(CompletionResponse::Array(Vec::new())))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        if let Some(doc) = self.documents.get(&uri) {
            if let Some(ref symbols) = doc.symbols {
                // Convert LSP position to byte offset
                let byte_offset = line_col_to_offset(&doc.text, position.line, position.character);
                let position_span = Span::new(byte_offset, byte_offset + 1);

                // Find symbol at this position
                if let Some(symbol) = symbols.symbol_at_position(position_span) {
                    let def_start = symbol.definition_span.start_linecol(&doc.text);
                    let def_end = symbol.definition_span.end_linecol(&doc.text);

                    return Ok(Some(GotoDefinitionResponse::Scalar(Location {
                        uri: uri.clone(),
                        range: Range {
                            start: Position {
                                line: def_start.line.saturating_sub(1),
                                character: def_start.col.saturating_sub(1),
                            },
                            end: Position {
                                line: def_end.line.saturating_sub(1),
                                character: def_end.col.saturating_sub(1),
                            },
                        },
                    })));
                }
            }
        }

        Ok(None)
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;

        if let Some(doc) = self.documents.get(&uri) {
            if let Some(ref symbols) = doc.symbols {
                // Convert LSP position to byte offset
                let byte_offset = line_col_to_offset(&doc.text, position.line, position.character);
                let position_span = Span::new(byte_offset, byte_offset + 1);

                // Find symbol at this position
                if let Some(symbol) = symbols.symbol_at_position(position_span) {
                    // Find all references to this symbol
                    let reference_spans = symbols.find_references(symbol);

                    let mut locations = Vec::new();
                    for span in reference_spans {
                        let start_lc = span.start_linecol(&doc.text);
                        let end_lc = span.end_linecol(&doc.text);

                        locations.push(Location {
                            uri: uri.clone(),
                            range: Range {
                                start: Position {
                                    line: start_lc.line.saturating_sub(1),
                                    character: start_lc.col.saturating_sub(1),
                                },
                                end: Position {
                                    line: end_lc.line.saturating_sub(1),
                                    character: end_lc.col.saturating_sub(1),
                                },
                            },
                        });
                    }

                    // Include the definition if requested
                    if params.context.include_declaration {
                        let def_start = symbol.definition_span.start_linecol(&doc.text);
                        let def_end = symbol.definition_span.end_linecol(&doc.text);

                        locations.push(Location {
                            uri: uri.clone(),
                            range: Range {
                                start: Position {
                                    line: def_start.line.saturating_sub(1),
                                    character: def_start.col.saturating_sub(1),
                                },
                                end: Position {
                                    line: def_end.line.saturating_sub(1),
                                    character: def_end.col.saturating_sub(1),
                                },
                            },
                        });
                    }

                    return Ok(Some(locations));
                }
            }
        }

        Ok(None)
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let uri = params.text_document.uri;

        if let Some(doc) = self.documents.get(&uri) {
            if let Some(ref symbols) = doc.symbols {
                let mut document_symbols = Vec::new();

                for sym in symbols.global_symbols() {
                    let start_lc = sym.definition_span.start_linecol(&doc.text);
                    let end_lc = sym.definition_span.end_linecol(&doc.text);

                    let symbol_kind = match sym.kind {
                        crate::symbols::SymbolKind::Function => SymbolKind::FUNCTION,
                        crate::symbols::SymbolKind::AdaptiveFunction => SymbolKind::FUNCTION,
                        crate::symbols::SymbolKind::TypeDef => SymbolKind::CLASS,
                        crate::symbols::SymbolKind::Const => SymbolKind::CONSTANT,
                        crate::symbols::SymbolKind::Variable => SymbolKind::VARIABLE,
                        crate::symbols::SymbolKind::Parameter => SymbolKind::VARIABLE,
                        crate::symbols::SymbolKind::Method => SymbolKind::METHOD,
                        crate::symbols::SymbolKind::Field => SymbolKind::FIELD,
                        crate::symbols::SymbolKind::EnumVariant => SymbolKind::ENUM_MEMBER,
                        crate::symbols::SymbolKind::Module => SymbolKind::MODULE,
                        crate::symbols::SymbolKind::Static => SymbolKind::VARIABLE,
                        crate::symbols::SymbolKind::Effect => SymbolKind::INTERFACE,
                        crate::symbols::SymbolKind::Trait => SymbolKind::INTERFACE,
                    };

                    #[allow(deprecated)]
                    let doc_symbol = DocumentSymbol {
                        name: sym.name.to_string(),
                        detail: sym.doc.clone(),
                        kind: symbol_kind,
                        tags: None,
                        deprecated: None,
                        range: Range {
                            start: Position {
                                line: start_lc.line.saturating_sub(1),
                                character: start_lc.col.saturating_sub(1),
                            },
                            end: Position {
                                line: end_lc.line.saturating_sub(1),
                                character: end_lc.col.saturating_sub(1),
                            },
                        },
                        selection_range: Range {
                            start: Position {
                                line: start_lc.line.saturating_sub(1),
                                character: start_lc.col.saturating_sub(1),
                            },
                            end: Position {
                                line: end_lc.line.saturating_sub(1),
                                character: end_lc.col.saturating_sub(1),
                            },
                        },
                        children: None,
                    };

                    document_symbols.push(doc_symbol);
                }

                return Ok(Some(DocumentSymbolResponse::Nested(document_symbols)));
            }
        }

        Ok(None)
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        let uri = params.text_document.uri;

        if let Some(doc) = self.documents.get(&uri) {
            let original = &doc.text;

            // Use the new formatter
            let formatter = eclexia_fmt::Formatter::new();
            let formatted = match formatter.format(original) {
                Ok(f) => f,
                Err(_) => {
                    // If formatting fails (e.g., parse errors), return None
                    return Ok(None);
                }
            };

            if formatted != *original {
                // Count total lines in original
                let line_count = original.lines().count();
                let last_line_len = original.lines().last().map_or(0, |l| l.len());

                return Ok(Some(vec![TextEdit {
                    range: Range {
                        start: Position {
                            line: 0,
                            character: 0,
                        },
                        end: Position {
                            line: line_count as u32,
                            character: last_line_len as u32,
                        },
                    },
                    new_text: formatted,
                }]));
            }

            return Ok(Some(Vec::new()));
        }

        Ok(None)
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let new_name = params.new_name;

        if let Some(doc) = self.documents.get(&uri) {
            if let Some(ref symbols) = doc.symbols {
                let byte_offset = line_col_to_offset(&doc.text, position.line, position.character);
                let position_span = Span::new(byte_offset, byte_offset + 1);

                if let Some(symbol) = symbols.symbol_at_position(position_span) {
                    let mut edits = Vec::new();

                    // Rename at the definition site
                    let def_start = symbol.definition_span.start_linecol(&doc.text);
                    let def_end = symbol.definition_span.end_linecol(&doc.text);
                    edits.push(TextEdit {
                        range: Range {
                            start: Position {
                                line: def_start.line.saturating_sub(1),
                                character: def_start.col.saturating_sub(1),
                            },
                            end: Position {
                                line: def_end.line.saturating_sub(1),
                                character: def_end.col.saturating_sub(1),
                            },
                        },
                        new_text: new_name.clone(),
                    });

                    // Rename at all reference sites
                    for span in symbols.find_references(symbol) {
                        let start_lc = span.start_linecol(&doc.text);
                        let end_lc = span.end_linecol(&doc.text);
                        edits.push(TextEdit {
                            range: Range {
                                start: Position {
                                    line: start_lc.line.saturating_sub(1),
                                    character: start_lc.col.saturating_sub(1),
                                },
                                end: Position {
                                    line: end_lc.line.saturating_sub(1),
                                    character: end_lc.col.saturating_sub(1),
                                },
                            },
                            new_text: new_name.clone(),
                        });
                    }

                    let mut changes = HashMap::new();
                    changes.insert(uri, edits);

                    return Ok(Some(WorkspaceEdit {
                        changes: Some(changes),
                        ..Default::default()
                    }));
                }
            }
        }

        Ok(None)
    }

    async fn signature_help(&self, params: SignatureHelpParams) -> Result<Option<SignatureHelp>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        if let Some(doc) = self.documents.get(&uri) {
            if let Some(ref parsed) = doc.parsed {
                let byte_offset =
                    line_col_to_offset(&doc.text, position.line, position.character) as usize;

                if let Some((func_name, active_param)) = find_call_context(&doc.text, byte_offset) {
                    // Find the function in parsed items
                    for item in &parsed.items {
                        let (name, params, return_type) = match item {
                            Item::Function(f) => (f.name.as_str(), &f.params, &f.return_type),
                            Item::AdaptiveFunction(f) => {
                                (f.name.as_str(), &f.params, &f.return_type)
                            }
                            _ => continue,
                        };

                        if name != func_name {
                            continue;
                        }

                        // Build parameter labels
                        let mut param_labels = Vec::new();
                        let mut param_infos = Vec::new();

                        for param in params {
                            let label = match param.ty {
                                Some(ty_id) => {
                                    format!("{}: {}", param.name, format_type(ty_id, parsed))
                                }
                                None => param.name.to_string(),
                            };
                            param_infos.push(ParameterInformation {
                                label: ParameterLabel::Simple(label.clone()),
                                documentation: None,
                            });
                            param_labels.push(label);
                        }

                        // Build full signature label
                        let ret_str = match return_type {
                            Some(ty_id) => {
                                format!(" -> {}", format_type(*ty_id, parsed))
                            }
                            None => String::new(),
                        };
                        let sig_label = format!("{}({}){}", name, param_labels.join(", "), ret_str);

                        return Ok(Some(SignatureHelp {
                            signatures: vec![SignatureInformation {
                                label: sig_label,
                                documentation: None,
                                parameters: Some(param_infos),
                                active_parameter: Some(active_param as u32),
                            }],
                            active_signature: Some(0),
                            active_parameter: Some(active_param as u32),
                        }));
                    }
                }
            }
        }

        Ok(None)
    }
}
