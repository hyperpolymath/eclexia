// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! LSP server implementation for Eclexia.

use dashmap::DashMap;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer};
use eclexia_ast::span::Span;

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

/// Document state stored in memory.
struct Document {
    /// The document text
    text: String,
    /// Document version
    version: i32,
    /// Symbol table for this document
    symbols: Option<SymbolTable>,
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
    async fn analyze_document(&self, uri: &Url, text: &str) -> Option<SymbolTable> {
        let mut diagnostics = Vec::new();

        // Parse the document
        let (file, parse_errors) = eclexia_parser::parse(text);

        // Build symbol table if parsing succeeded
        let symbols = if parse_errors.is_empty() {
            Some(SymbolTable::build(&file))
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

        // If parsing succeeded, run type checker
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
        }

        // Publish diagnostics to the client
        self.client
            .publish_diagnostics(uri.clone(), diagnostics, None)
            .await;

        symbols
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
        let symbols = self.analyze_document(&uri, &text).await;

        // Store document with symbol table
        self.documents.insert(
            uri.clone(),
            Document {
                text: text.clone(),
                version,
                symbols,
            },
        );
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;

        if let Some(change) = params.content_changes.first() {
            let text = change.text.clone();

            // Analyze and publish diagnostics, get symbol table
            let symbols = self.analyze_document(&uri, &text).await;

            // Update document with symbol table
            self.documents.insert(
                uri.clone(),
                Document {
                    text: text.clone(),
                    version,
                    symbols,
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
            let symbols = self.analyze_document(&uri, &text).await;

            // Update stored symbols
            if let Some(mut doc) = self.documents.get_mut(&uri) {
                doc.symbols = symbols;
            }
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;

        // Remove document from storage
        self.documents.remove(&uri);

        // Clear diagnostics
        self.client
            .publish_diagnostics(uri, Vec::new(), None)
            .await;
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;

        if let Some(doc) = self.documents.get(&uri) {
            if let Some(ref symbols) = doc.symbols {
                // Get all symbols and show them as hover info
                let global_syms = symbols.global_symbols();

                if !global_syms.is_empty() {
                    let mut hover_text = String::from("## Symbols in this file:\n\n");
                    for sym in global_syms {
                        hover_text.push_str(&format!(
                            "- **{}** ({:?})\n",
                            sym.name,
                            sym.kind
                        ));
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

        if let Some(doc) = self.documents.get(&uri) {
            if let Some(ref symbols) = doc.symbols {
                let mut completions = Vec::new();

                // Suggest all global symbols
                for symbol in symbols.global_symbols() {
                    let kind = match symbol.kind {
                        crate::symbols::SymbolKind::Function => CompletionItemKind::FUNCTION,
                        crate::symbols::SymbolKind::AdaptiveFunction => CompletionItemKind::FUNCTION,
                        crate::symbols::SymbolKind::TypeDef => CompletionItemKind::CLASS,
                        crate::symbols::SymbolKind::Const => CompletionItemKind::CONSTANT,
                        crate::symbols::SymbolKind::Variable => CompletionItemKind::VARIABLE,
                        crate::symbols::SymbolKind::Parameter => CompletionItemKind::VARIABLE,
                    };

                    let detail = symbol.doc.clone();

                    completions.push(CompletionItem {
                        label: symbol.name.to_string(),
                        label_details: None,
                        kind: Some(kind),
                        detail,
                        documentation: None,
                        deprecated: Some(false),
                        preselect: None,
                        sort_text: None,
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
            // Parse to check for errors
            let (_file, errors) = eclexia_parser::parse(&doc.text);

            if errors.is_empty() {
                // TODO: Implement pretty-printing formatter
                // For now, just return no edits (document is already formatted)
                return Ok(Some(Vec::new()));
            }
        }

        Ok(None)
    }

    async fn rename(&self, _params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        // TODO: Implement symbol renaming
        // Requires symbol table and find-all-references
        Ok(None)
    }
}
