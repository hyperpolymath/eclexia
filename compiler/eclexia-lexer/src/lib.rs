// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Lexer for the Eclexia programming language.
//!
//! This crate provides lexical analysis for Eclexia source code,
//! converting a string of characters into a stream of tokens.
//! The lexer handles:
//!
//! - Keywords and identifiers
//! - Numeric literals with dimensional units (e.g., `100J`, `5ms`)
//! - String and character literals
//! - Operators and punctuation
//! - Comments (line and block)
//! - Annotation syntax (@requires, @provides, etc.)

use eclexia_ast::span::Span;
use logos::Logos;
use smol_str::SmolStr;

/// A token with its span in the source.
#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }
}

/// Token kinds produced by the lexer.
#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(skip r"[ \t\r\n\f]+")]
#[logos(skip r"//[^\n]*")]
#[logos(skip r"/\*([^*]|\*[^/])*\*/")]
pub enum TokenKind {
    // === Keywords ===
    #[token("adaptive")]
    Adaptive,
    #[token("def")]
    Def,
    #[token("fn")]
    Fn,
    #[token("let")]
    Let,
    #[token("mut")]
    Mut,
    #[token("const")]
    Const,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("else")]
    Else,
    #[token("match")]
    Match,
    #[token("while")]
    While,
    #[token("for")]
    For,
    #[token("in")]
    In,
    #[token("return")]
    Return,
    #[token("break")]
    Break,
    #[token("continue")]
    Continue,
    #[token("type")]
    Type,
    #[token("struct")]
    Struct,
    #[token("enum")]
    Enum,
    #[token("impl")]
    Impl,
    #[token("trait")]
    Trait,
    #[token("import")]
    Import,
    #[token("export")]
    Export,
    #[token("async")]
    Async,
    #[token("await")]
    Await,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("and")]
    And,
    #[token("or")]
    Or,
    #[token("not")]
    Not,

    // === Eclexia-specific keywords ===
    #[token("@solution")]
    AtSolution,
    #[token("@when")]
    AtWhen,
    #[token("@requires")]
    AtRequires,
    #[token("@provides")]
    AtProvides,
    #[token("@optimize")]
    AtOptimize,
    #[token("@observe")]
    AtObserve,
    #[token("@defer_until")]
    AtDeferUntil,
    #[token("minimize")]
    Minimize,
    #[token("maximize")]
    Maximize,

    // === Literals ===
    /// Integer literal (possibly with unit suffix)
    #[regex(r"[0-9][0-9_]*", |lex| parse_int(lex.slice()))]
    Integer(i64),

    /// Float literal (possibly with unit suffix)
    #[regex(r"[0-9][0-9_]*\.[0-9][0-9_]*([eE][+-]?[0-9]+)?", |lex| parse_float(lex.slice()))]
    Float(f64),

    /// Resource literal: number followed by unit suffix
    /// Examples: 100J, 5ms, 10gCO2e, 1.5kWh
    #[regex(r"[0-9][0-9_]*(\.[0-9][0-9_]*)?[a-zA-Z][a-zA-Z0-9]*", |lex| parse_resource(lex.slice()))]
    Resource(ResourceLiteral),

    /// String literal
    #[regex(r#""([^"\\]|\\.)*""#, |lex| parse_string(lex.slice()))]
    String(SmolStr),

    /// Character literal
    #[regex(r"'([^'\\]|\\.)'", |lex| parse_char(lex.slice()))]
    Char(char),

    // === Identifiers ===
    // Note: Keywords take priority. Single underscore is handled separately.
    // Support Unicode XID_Start and XID_Continue properties for mathematical notation (π, τ, etc.)
    #[regex(r"[a-zA-Z_\u{80}-\u{10FFFF}][a-zA-Z0-9_\u{80}-\u{10FFFF}]*", |lex| {
        let s = lex.slice();
        // Verify first char is XID_Start, rest are XID_Continue
        if s.chars().next().map_or(false, is_xid_start) &&
           s.chars().skip(1).all(is_xid_continue) {
            Some(SmolStr::new(s))
        } else {
            None
        }
    })]
    Ident(SmolStr),

    // === Operators ===
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,
    #[token("**")]
    StarStar,
    #[token("==")]
    EqEq,
    #[token("!=")]
    BangEq,
    #[token("<")]
    Lt,
    #[token("<=")]
    Le,
    #[token(">")]
    Gt,
    #[token(">=")]
    Ge,
    #[token("&&")]
    AmpAmp,
    #[token("||")]
    PipePipe,
    #[token("!")]
    Bang,
    #[token("&")]
    Amp,
    #[token("|")]
    Pipe,
    #[token("^")]
    Caret,
    #[token("~")]
    Tilde,
    #[token("<<")]
    LtLt,
    #[token(">>")]
    GtGt,

    // === Punctuation ===
    #[token("=")]
    Eq,
    #[token(":")]
    Colon,
    #[token("::")]
    ColonColon,
    #[token(";")]
    Semi,
    #[token(",")]
    Comma,
    #[token(".")]
    Dot,
    #[token("..")]
    DotDot,
    #[token("...")]
    DotDotDot,
    #[token("->")]
    Arrow,
    #[token("=>")]
    FatArrow,
    #[token("@")]
    At,
    #[token("#")]
    Hash,
    #[token("?")]
    Question,
    #[token("_", priority = 10)]
    Underscore,

    // === Delimiters ===
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,

    // === Special ===
    /// End of file
    Eof,

    /// Error token
    Error,
}

/// A resource literal with value and unit.
#[derive(Debug, Clone, PartialEq)]
pub struct ResourceLiteral {
    pub value: f64,
    pub unit: SmolStr,
}

fn parse_int(s: &str) -> i64 {
    s.replace('_', "").parse().unwrap_or(0)
}

fn parse_float(s: &str) -> f64 {
    s.replace('_', "").parse().unwrap_or(0.0)
}

fn parse_resource(s: &str) -> ResourceLiteral {
    // Find where the number ends and unit begins
    let unit_start = s
        .char_indices()
        .find(|(_, c)| c.is_alphabetic())
        .map(|(i, _)| i)
        .unwrap_or(s.len());

    let num_part = &s[..unit_start];
    let unit_part = &s[unit_start..];

    let value = num_part.replace('_', "").parse().unwrap_or(0.0);

    ResourceLiteral {
        value,
        unit: SmolStr::new(unit_part),
    }
}

fn parse_string(s: &str) -> SmolStr {
    // Remove quotes and process escapes
    let inner = &s[1..s.len() - 1];
    let mut result = String::with_capacity(inner.len());
    let mut chars = inner.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => result.push('\n'),
                Some('r') => result.push('\r'),
                Some('t') => result.push('\t'),
                Some('\\') => result.push('\\'),
                Some('"') => result.push('"'),
                Some('0') => result.push('\0'),
                Some(c) => result.push(c),
                None => break,
            }
        } else {
            result.push(c);
        }
    }

    SmolStr::new(&result)
}

fn parse_char(s: &str) -> char {
    let inner = &s[1..s.len() - 1];
    let mut chars = inner.chars();

    match chars.next() {
        Some('\\') => match chars.next() {
            Some('n') => '\n',
            Some('r') => '\r',
            Some('t') => '\t',
            Some('\\') => '\\',
            Some('\'') => '\'',
            Some('0') => '\0',
            Some(c) => c,
            None => '\0',
        },
        Some(c) => c,
        None => '\0',
    }
}

/// Check if a character is valid as the first character of an identifier (XID_Start).
/// This includes ASCII letters, underscore, and Unicode letter/ideograph characters.
fn is_xid_start(c: char) -> bool {
    c == '_' || c.is_alphabetic()
}

/// Check if a character is valid in the continuation of an identifier (XID_Continue).
/// This includes XID_Start characters plus digits.
fn is_xid_continue(c: char) -> bool {
    is_xid_start(c) || c.is_numeric()
}

/// Lexer for Eclexia source code.
pub struct Lexer<'src> {
    inner: logos::Lexer<'src, TokenKind>,
    peeked: Option<Token>,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer for the given source.
    pub fn new(source: &'src str) -> Self {
        Self {
            inner: TokenKind::lexer(source),
            peeked: None,
        }
    }

    /// Get the next token.
    pub fn next(&mut self) -> Token {
        if let Some(token) = self.peeked.take() {
            return token;
        }

        match self.inner.next() {
            Some(Ok(kind)) => {
                let span = self.inner.span();
                Token::new(kind, Span::new(span.start as u32, span.end as u32))
            }
            Some(Err(())) => {
                let span = self.inner.span();
                Token::new(TokenKind::Error, Span::new(span.start as u32, span.end as u32))
            }
            None => Token::new(TokenKind::Eof, Span::empty(self.inner.span().end as u32)),
        }
    }

    /// Peek at the next token without consuming it.
    pub fn peek(&mut self) -> &Token {
        if self.peeked.is_none() {
            self.peeked = Some(self.next());
        }
        self.peeked.as_ref().unwrap()
    }

    /// Check if we've reached the end of input.
    pub fn is_eof(&mut self) -> bool {
        matches!(self.peek().kind, TokenKind::Eof)
    }

    /// Get the current source slice for a span.
    pub fn slice(&self) -> &'src str {
        self.inner.slice()
    }

    /// Get the source string.
    pub fn source(&self) -> &'src str {
        self.inner.source()
    }
}

impl Iterator for Lexer<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let token = Lexer::next(self);
        if matches!(token.kind, TokenKind::Eof) {
            None
        } else {
            Some(token)
        }
    }
}

/// Tokenize a source string into a vector of tokens.
pub fn tokenize(source: &str) -> Vec<Token> {
    let mut lexer = Lexer::new(source);
    let mut tokens = Vec::new();

    loop {
        let token = lexer.next();
        let is_eof = matches!(token.kind, TokenKind::Eof);
        tokens.push(token);
        if is_eof {
            break;
        }
    }

    tokens
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keywords() {
        let source = "adaptive def fn let if else match while for return";
        let tokens: Vec<_> = Lexer::new(source).collect();

        assert!(matches!(tokens[0].kind, TokenKind::Adaptive));
        assert!(matches!(tokens[1].kind, TokenKind::Def));
        assert!(matches!(tokens[2].kind, TokenKind::Fn));
        assert!(matches!(tokens[3].kind, TokenKind::Let));
        assert!(matches!(tokens[4].kind, TokenKind::If));
    }

    #[test]
    fn test_resource_literals() {
        let source = "100J 5ms 10gCO2e 1.5kWh 500mW";
        let tokens: Vec<_> = Lexer::new(source).collect();

        if let TokenKind::Resource(r) = &tokens[0].kind {
            assert_eq!(r.value, 100.0);
            assert_eq!(r.unit.as_str(), "J");
        } else {
            panic!("Expected resource literal");
        }

        if let TokenKind::Resource(r) = &tokens[1].kind {
            assert_eq!(r.value, 5.0);
            assert_eq!(r.unit.as_str(), "ms");
        } else {
            panic!("Expected resource literal");
        }

        if let TokenKind::Resource(r) = &tokens[2].kind {
            assert_eq!(r.value, 10.0);
            assert_eq!(r.unit.as_str(), "gCO2e");
        } else {
            panic!("Expected resource literal");
        }
    }

    #[test]
    fn test_annotations() {
        let source = "@requires @provides @optimize @solution @when";
        let tokens: Vec<_> = Lexer::new(source).collect();

        assert!(matches!(tokens[0].kind, TokenKind::AtRequires));
        assert!(matches!(tokens[1].kind, TokenKind::AtProvides));
        assert!(matches!(tokens[2].kind, TokenKind::AtOptimize));
        assert!(matches!(tokens[3].kind, TokenKind::AtSolution));
        assert!(matches!(tokens[4].kind, TokenKind::AtWhen));
    }

    #[test]
    fn test_operators() {
        let source = "+ - * / % ** == != < <= > >= && ||";
        let tokens: Vec<_> = Lexer::new(source).collect();

        assert!(matches!(tokens[0].kind, TokenKind::Plus));
        assert!(matches!(tokens[1].kind, TokenKind::Minus));
        assert!(matches!(tokens[2].kind, TokenKind::Star));
        assert!(matches!(tokens[3].kind, TokenKind::Slash));
        assert!(matches!(tokens[4].kind, TokenKind::Percent));
        assert!(matches!(tokens[5].kind, TokenKind::StarStar));
        assert!(matches!(tokens[6].kind, TokenKind::EqEq));
    }

    #[test]
    fn test_string_literal() {
        let source = r#""hello world" "with\nescape""#;
        let tokens: Vec<_> = Lexer::new(source).collect();

        if let TokenKind::String(s) = &tokens[0].kind {
            assert_eq!(s.as_str(), "hello world");
        } else {
            panic!("Expected string literal");
        }

        if let TokenKind::String(s) = &tokens[1].kind {
            assert_eq!(s.as_str(), "with\nescape");
        } else {
            panic!("Expected string literal");
        }
    }

    #[test]
    fn test_comments_skipped() {
        let source = "let // this is a comment\nx /* block */ = 5";
        let tokens: Vec<_> = Lexer::new(source).collect();

        // Comments should be skipped
        assert!(matches!(tokens[0].kind, TokenKind::Let));
        assert!(matches!(tokens[1].kind, TokenKind::Ident(_)));
        assert!(matches!(tokens[2].kind, TokenKind::Eq));
        assert!(matches!(tokens[3].kind, TokenKind::Integer(5)));
    }

    #[test]
    fn test_full_adaptive_function() {
        let source = r#"
            adaptive def sort(arr: Array[Int]) -> Array[Int]
                @requires: energy < 100J
                @optimize: minimize energy
            {
                @solution "quick":
                    @when: length(arr) > 100
                    @provides: energy: 50J
                { quicksort(arr) }
            }
        "#;

        let tokens: Vec<_> = Lexer::new(source).collect();

        // Just verify it tokenizes without error
        assert!(!tokens.is_empty());
        assert!(matches!(tokens[0].kind, TokenKind::Adaptive));
    }
}
