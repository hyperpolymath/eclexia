// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Documentation generator for Eclexia.
//!
//! Generates HTML documentation from Eclexia source files,
//! similar to rustdoc for Rust.

use eclexia_ast::{Function, Item, SourceFile, TypeDef};
use smol_str::SmolStr;

/// Documentation for a single item
#[derive(Debug, Clone)]
pub struct DocItem {
    pub name: SmolStr,
    pub kind: DocItemKind,
    pub doc_comment: String,
    pub signature: String,
}

#[derive(Debug, Clone)]
pub enum DocItemKind {
    Function,
    Type,
    Constant,
    Module,
}

/// Documentation generator
pub struct DocGenerator {
    items: Vec<DocItem>,
}

impl DocGenerator {
    pub fn new() -> Self {
        Self { items: Vec::new() }
    }

    /// Generate documentation for a source file
    pub fn document_file(&mut self, file: &SourceFile, source: &str) {
        for item in &file.items {
            if let Some(doc_item) = self.document_item(item, source) {
                self.items.push(doc_item);
            }
        }
    }

    fn document_item(&self, item: &Item, source: &str) -> Option<DocItem> {
        match item {
            Item::Function(func) => Some(self.document_function(func, source)),
            Item::TypeDef(typedef) => Some(self.document_typedef(typedef, source)),
            Item::Const(const_item) => Some(DocItem {
                name: const_item.name.clone(),
                kind: DocItemKind::Constant,
                doc_comment: self.extract_doc_comment(const_item.span, source),
                signature: format!("const {}: {:?}", const_item.name, const_item.ty),
            }),
            _ => None,
        }
    }

    fn document_function(&self, func: &Function, source: &str) -> DocItem {
        let params: Vec<String> = func
            .params
            .iter()
            .map(|p| {
                if let Some(ty) = p.ty {
                    format!("{}: {:?}", p.name, ty)
                } else {
                    p.name.to_string()
                }
            })
            .collect();

        let signature = if let Some(ret_ty) = func.return_type {
            format!("fn {}({}) -> {:?}", func.name, params.join(", "), ret_ty)
        } else {
            format!("fn {}({})", func.name, params.join(", "))
        };

        DocItem {
            name: func.name.clone(),
            kind: DocItemKind::Function,
            doc_comment: self.extract_doc_comment(func.span, source),
            signature,
        }
    }

    fn document_typedef(&self, typedef: &TypeDef, source: &str) -> DocItem {
        DocItem {
            name: typedef.name.clone(),
            kind: DocItemKind::Type,
            doc_comment: self.extract_doc_comment(typedef.span, source),
            signature: format!("type {} = {:?}", typedef.name, typedef.kind),
        }
    }

    /// Extract doc comment from source text before an item
    fn extract_doc_comment(&self, span: eclexia_ast::span::Span, source: &str) -> String {
        let start = span.start as usize;
        if start == 0 {
            return String::new();
        }

        // Look backwards for doc comments (///)
        let before = &source[..start];
        let lines: Vec<&str> = before.lines().collect();

        let mut doc_lines = Vec::new();
        for line in lines.iter().rev() {
            let trimmed = line.trim();
            if trimmed.starts_with("///") {
                doc_lines.push(trimmed.trim_start_matches("///").trim());
            } else if trimmed.is_empty() {
                continue;
            } else {
                break;
            }
        }

        doc_lines.reverse();
        doc_lines.join("\n")
    }

    /// Generate HTML documentation
    pub fn generate_html(&self, module_name: &str) -> String {
        let mut html = String::new();

        html.push_str("<!DOCTYPE html>\n");
        html.push_str("<html>\n<head>\n");
        html.push_str(&format!("<title>{} - Eclexia Documentation</title>\n", module_name));
        html.push_str("<style>\n");
        html.push_str(include_str!("style.css"));
        html.push_str("</style>\n");
        html.push_str("</head>\n<body>\n");

        html.push_str(&format!("<h1>Module: {}</h1>\n", module_name));

        // Table of contents
        html.push_str("<h2>Table of Contents</h2>\n<ul>\n");
        for item in &self.items {
            html.push_str(&format!(
                "<li><a href=\"#{}\">{}</a> - {:?}</li>\n",
                item.name, item.name, item.kind
            ));
        }
        html.push_str("</ul>\n");

        // Item documentation
        for item in &self.items {
            html.push_str(&format!("<div class=\"item\" id=\"{}\">\n", item.name));
            html.push_str(&format!("<h3>{}</h3>\n", item.name));
            html.push_str(&format!("<pre class=\"signature\">{}</pre>\n", item.signature));

            if !item.doc_comment.is_empty() {
                html.push_str("<div class=\"doc-comment\">\n");
                // Convert markdown-style formatting
                let formatted = self.format_doc_comment(&item.doc_comment);
                html.push_str(&formatted);
                html.push_str("</div>\n");
            }

            html.push_str("</div>\n");
        }

        html.push_str("</body>\n</html>\n");
        html
    }

    fn format_doc_comment(&self, comment: &str) -> String {
        // Simple markdown-like formatting
        let mut result = String::new();
        let mut in_code_block = false;

        for line in comment.lines() {
            if line.trim().starts_with("```") {
                if in_code_block {
                    result.push_str("</pre>\n");
                } else {
                    result.push_str("<pre><code>\n");
                }
                in_code_block = !in_code_block;
            } else if in_code_block {
                result.push_str(line);
                result.push('\n');
            } else {
                result.push_str("<p>");
                result.push_str(&html_escape(line));
                result.push_str("</p>\n");
            }
        }

        result
    }

    /// Generate Markdown documentation
    pub fn generate_markdown(&self, module_name: &str) -> String {
        let mut md = String::new();

        md.push_str(&format!("# Module: {}\n\n", module_name));

        // Table of contents
        md.push_str("## Table of Contents\n\n");
        for item in &self.items {
            md.push_str(&format!(
                "- [{}](#{})\n",
                item.name,
                item.name.to_lowercase()
            ));
        }
        md.push_str("\n");

        // Item documentation
        for item in &self.items {
            md.push_str(&format!("## {}\n\n", item.name));
            md.push_str(&format!("```eclexia\n{}\n```\n\n", item.signature));

            if !item.doc_comment.is_empty() {
                md.push_str(&item.doc_comment);
                md.push_str("\n\n");
            }
        }

        md
    }
}

impl Default for DocGenerator {
    fn default() -> Self {
        Self::new()
    }
}

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_doc_comment_extraction() {
        let source = r#"
/// This is a function
/// that does something
fn test() {}
"#;

        let (file, _) = eclexia_parser::parse(source);
        let mut gen = DocGenerator::new();
        gen.document_file(&file, source);

        assert_eq!(gen.items.len(), 1);
        assert!(gen.items[0].doc_comment.contains("This is a function"));
    }
}
