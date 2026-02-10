// SPDX-License-Identifier: PMPL-1.0-or-later
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
    /// The kind of this token.
    pub kind: TokenKind,
    /// The source span of this token.
    pub span: Span,
}

impl Token {
    /// Create a new token with the given kind and span.
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
    /// The `adaptive` keyword for adaptive function definitions.
    #[token("adaptive")]
    Adaptive,
    /// The `def` keyword for function definitions.
    #[token("def")]
    Def,
    /// The `fn` keyword for function definitions.
    #[token("fn")]
    Fn,
    /// The `let` keyword for variable bindings.
    #[token("let")]
    Let,
    /// The `mut` keyword for mutable bindings.
    #[token("mut")]
    Mut,
    /// The `const` keyword for constant declarations.
    #[token("const")]
    Const,
    /// The `if` keyword for conditional expressions.
    #[token("if")]
    If,
    /// The `then` keyword for if-then syntax.
    #[token("then")]
    Then,
    /// The `else` keyword for else branches.
    #[token("else")]
    Else,
    /// The `match` keyword for pattern matching.
    #[token("match")]
    Match,
    /// The `while` keyword for while loops.
    #[token("while")]
    While,
    /// The `for` keyword for for-in loops.
    #[token("for")]
    For,
    /// The `in` keyword used in for-in loops.
    #[token("in")]
    In,
    /// The `return` keyword for early returns.
    #[token("return")]
    Return,
    /// The `break` keyword for breaking out of loops.
    #[token("break")]
    Break,
    /// The `continue` keyword for skipping to the next loop iteration.
    #[token("continue")]
    Continue,
    /// The `type` keyword for type definitions.
    #[token("type")]
    Type,
    /// The `struct` keyword for struct definitions.
    #[token("struct")]
    Struct,
    /// The `enum` keyword for enum definitions.
    #[token("enum")]
    Enum,
    /// The `impl` keyword for implementation blocks.
    #[token("impl")]
    Impl,
    /// The `trait` keyword for trait declarations.
    #[token("trait")]
    Trait,
    /// The `import` keyword for module imports.
    #[token("import")]
    Import,
    /// The `export` keyword for module exports.
    #[token("export")]
    Export,
    /// The `async` keyword for asynchronous blocks and functions.
    #[token("async")]
    Async,
    /// The `await` keyword for awaiting async expressions.
    #[token("await")]
    Await,
    /// The `true` boolean literal.
    #[token("true")]
    True,
    /// The `false` boolean literal.
    #[token("false")]
    False,
    /// The `and` logical operator keyword.
    #[token("and")]
    And,
    /// The `or` logical operator keyword.
    #[token("or")]
    Or,
    /// The `not` logical negation keyword.
    #[token("not")]
    Not,
    /// The `as` keyword for type casts.
    #[token("as")]
    As,
    /// The `pub` keyword for visibility modifiers.
    #[token("pub")]
    Pub,
    /// The `module` keyword for module declarations.
    #[token("module")]
    Module,
    /// The `mod` keyword for module declarations (short form).
    #[token("mod")]
    Mod,
    /// The `loop` keyword for infinite loops.
    #[token("loop")]
    Loop,
    /// The `effect` keyword for algebraic effect declarations.
    #[token("effect")]
    Effect,
    /// The `handle` keyword for effect handler expressions.
    #[token("handle")]
    Handle,
    /// The `use` keyword for imports.
    #[token("use")]
    Use,
    /// The `where` keyword for where clauses.
    #[token("where")]
    Where,
    /// The `self` keyword (lowercase) for the current instance.
    #[token("self", priority = 5)]
    SelfLower,
    /// The `Self` keyword (uppercase) for the current type.
    #[token("Self", priority = 5)]
    SelfUpper,
    /// The `static` keyword for static declarations.
    #[token("static")]
    Static,
    /// The `extern` keyword for external function blocks.
    #[token("extern")]
    Extern,
    /// The `case` keyword for case expressions.
    #[token("case")]
    Case,
    /// The `do` keyword for do-notation blocks.
    #[token("do")]
    Do,
    /// The `energy` keyword for energy resource constraints.
    #[token("energy")]
    Energy,
    /// The `latency` keyword for latency resource constraints.
    #[token("latency")]
    Latency,
    /// The `memory` keyword for memory resource constraints.
    #[token("memory")]
    Memory,
    /// The `unit` keyword for unit type or unit dimensions.
    #[token("unit")]
    Unit,
    /// The `carbon` keyword for carbon emission constraints.
    #[token("carbon")]
    Carbon,
    /// The `ref` keyword for reference bindings.
    #[token("ref")]
    Ref,
    /// The `super` keyword for parent module access.
    #[token("super")]
    Super,
    /// The `comptime` keyword for compile-time evaluation.
    #[token("comptime")]
    Comptime,
    /// The `spawn` keyword for launching concurrent tasks.
    #[token("spawn")]
    Spawn,
    /// The `select` keyword for waiting on multiple channels.
    #[token("select")]
    Select,
    /// The `chan` keyword for channel creation.
    #[token("chan")]
    Chan,
    /// The `send` keyword for sending on channels.
    #[token("send")]
    Send,
    /// The `recv` keyword for receiving from channels.
    #[token("recv")]
    Recv,
    /// The `yield` keyword for yielding from async tasks.
    #[token("yield")]
    Yield,
    /// The `macro` keyword for macro definitions.
    #[token("macro")]
    Macro,

    // === Eclexia-specific keywords ===
    /// The `@solution` annotation for adaptive solution alternatives.
    #[token("@solution")]
    AtSolution,
    /// The `@when` annotation for conditional solution guards.
    #[token("@when")]
    AtWhen,
    /// The `@requires` annotation for resource requirement constraints.
    #[token("@requires")]
    AtRequires,
    /// The `@provides` annotation for resource provision declarations.
    #[token("@provides")]
    AtProvides,
    /// The `@optimize` annotation for optimization directives.
    #[token("@optimize")]
    AtOptimize,
    /// The `@observe` annotation for runtime observation hooks.
    #[token("@observe")]
    AtObserve,
    /// The `@defer_until` annotation for deferred evaluation.
    #[token("@defer_until")]
    AtDeferUntil,
    /// The `minimize` keyword for optimization direction.
    #[token("minimize")]
    Minimize,
    /// The `maximize` keyword for optimization direction.
    #[token("maximize")]
    Maximize,

    // === Literals ===
    /// Hex integer literal (0xFF)
    #[regex(r"0[xX][0-9a-fA-F][0-9a-fA-F_]*", |lex| parse_hex(lex.slice()), priority = 5)]
    HexInteger(i64),

    /// Octal integer literal (0o77)
    #[regex(r"0[oO][0-7][0-7_]*", |lex| parse_octal(lex.slice()), priority = 5)]
    OctalInteger(i64),

    /// Binary integer literal (0b1010)
    #[regex(r"0[bB][01][01_]*", |lex| parse_binary(lex.slice()), priority = 5)]
    BinaryInteger(i64),

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

    /// Raw string literal: r"..." (no escape processing)
    #[regex(r#"r"[^"]*""#, |lex| {
        let s = lex.slice();
        SmolStr::new(&s[2..s.len()-1])
    })]
    RawString(SmolStr),

    /// Raw string literal with hashes: r#"..."#
    #[regex(r####"r#"([^"]|"[^#])*"#"####, |lex| {
        let s = lex.slice();
        SmolStr::new(&s[3..s.len()-2])
    })]
    RawStringHash(SmolStr),

    /// Character literal
    #[regex(r"'([^'\\]|\\.)'", |lex| parse_char(lex.slice()))]
    Char(char),

    /// Doc comment (///)
    #[regex(r"///[^\n]*", |lex| {
        let s = lex.slice();
        SmolStr::new(s[3..].trim())
    })]
    DocComment(SmolStr),

    /// Block doc comment (/** ... */)
    #[regex(r"/\*\*([^*]|\*[^/])*\*/", |lex| {
        let s = lex.slice();
        SmolStr::new(s[3..s.len()-2].trim())
    })]
    BlockDocComment(SmolStr),

    // === Identifiers ===
    /// An identifier (variable, function, or type name) supporting Unicode XID properties.
    // Note: Keywords take priority. Single underscore is handled separately.
    // Support Unicode XID_Start and XID_Continue properties for mathematical notation (π, τ, etc.)
    #[regex(r"[a-zA-Z_\u{80}-\u{10FFFF}][a-zA-Z0-9_\u{80}-\u{10FFFF}]*", |lex| {
        let s = lex.slice();
        // Verify first char is XID_Start, rest are XID_Continue
        if s.chars().next().is_some_and(is_xid_start) &&
           s.chars().skip(1).all(is_xid_continue) {
            Some(SmolStr::new(s))
        } else {
            None
        }
    })]
    Ident(SmolStr),

    // === Operators ===
    /// The `+` addition operator.
    #[token("+")]
    Plus,
    /// The `-` subtraction or negation operator.
    #[token("-")]
    Minus,
    /// The `*` multiplication or dereference operator.
    #[token("*")]
    Star,
    /// The `/` division operator.
    #[token("/")]
    Slash,
    /// The `%` remainder operator.
    #[token("%")]
    Percent,
    /// The `**` exponentiation operator.
    #[token("**")]
    StarStar,
    /// The `==` equality comparison operator.
    #[token("==")]
    EqEq,
    /// The `!=` inequality comparison operator.
    #[token("!=")]
    BangEq,
    /// The `<` less-than comparison operator.
    #[token("<")]
    Lt,
    /// The `<=` less-than-or-equal comparison operator.
    #[token("<=")]
    Le,
    /// The `>` greater-than comparison operator.
    #[token(">")]
    Gt,
    /// The `>=` greater-than-or-equal comparison operator.
    #[token(">=")]
    Ge,
    /// The `&&` logical AND operator.
    #[token("&&")]
    AmpAmp,
    /// The `||` logical OR operator.
    #[token("||")]
    PipePipe,
    /// The `!` logical NOT operator.
    #[token("!")]
    Bang,
    /// The `&` bitwise AND or borrow operator.
    #[token("&")]
    Amp,
    /// The `|` bitwise OR or pipe operator.
    #[token("|")]
    Pipe,
    /// The `^` bitwise XOR operator.
    #[token("^")]
    Caret,
    /// The `~` bitwise NOT operator.
    #[token("~")]
    Tilde,
    /// The `<<` left shift operator.
    #[token("<<")]
    LtLt,
    /// The `>>` right shift operator.
    #[token(">>")]
    GtGt,

    // === Compound assignment ===
    /// The `+=` addition assignment operator.
    #[token("+=")]
    PlusEq,
    /// The `-=` subtraction assignment operator.
    #[token("-=")]
    MinusEq,
    /// The `*=` multiplication assignment operator.
    #[token("*=")]
    StarEq,
    /// The `/=` division assignment operator.
    #[token("/=")]
    SlashEq,
    /// The `%=` remainder assignment operator.
    #[token("%=")]
    PercentEq,
    /// The `^=` bitwise XOR assignment operator.
    #[token("^=")]
    CaretEq,
    /// The `<<=` left shift assignment operator.
    #[token("<<=")]
    LtLtEq,
    /// The `>>=` right shift assignment operator.
    #[token(">>=")]
    GtGtEq,
    /// The `&=` bitwise AND assignment operator.
    #[token("&=")]
    AmpEq,
    /// The `|=` bitwise OR assignment operator.
    #[token("|=")]
    PipeEq,
    /// The `**=` exponentiation assignment operator.
    #[token("**=")]
    StarStarEq,

    // === Punctuation ===
    /// The `=` assignment operator.
    #[token("=")]
    Eq,
    /// The `:` colon separator.
    #[token(":")]
    Colon,
    /// The `::` path separator.
    #[token("::")]
    ColonColon,
    /// The `;` semicolon statement terminator.
    #[token(";")]
    Semi,
    /// The `,` comma separator.
    #[token(",")]
    Comma,
    /// The `.` field access operator.
    #[token(".")]
    Dot,
    /// The `..=` inclusive range operator.
    #[token("..=")]
    DotDotEq,
    /// The `..` exclusive range operator.
    #[token("..")]
    DotDot,
    /// The `...` rest/spread operator.
    #[token("...")]
    DotDotDot,
    /// The `->` return type arrow.
    #[token("->")]
    Arrow,
    /// The `=>` fat arrow for match arms and lambdas.
    #[token("=>")]
    FatArrow,
    /// The `@` annotation prefix.
    #[token("@")]
    At,
    /// The `#` attribute prefix.
    #[token("#")]
    Hash,
    /// The `?` try/optional operator.
    #[token("?")]
    Question,
    /// The `$` dollar sign (macro metavariables).
    #[token("$")]
    Dollar,
    /// The `_` wildcard/discard pattern.
    #[token("_", priority = 10)]
    Underscore,

    // === Delimiters ===
    /// The `(` opening parenthesis.
    #[token("(")]
    LParen,
    /// The `)` closing parenthesis.
    #[token(")")]
    RParen,
    /// The `[` opening square bracket.
    #[token("[")]
    LBracket,
    /// The `]` closing square bracket.
    #[token("]")]
    RBracket,
    /// The `{` opening curly brace.
    #[token("{")]
    LBrace,
    /// The `}` closing curly brace.
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
    /// The numeric value of the resource literal.
    pub value: f64,
    /// The unit suffix (e.g., "J", "ms", "gCO2e").
    pub unit: SmolStr,
}

/// Parses a decimal integer string slice, removing underscores.
fn parse_int(s: &str) -> i64 {
    s.replace('_', "").parse().unwrap_or(0)
}

/// Parses a hexadecimal integer string slice (e.g., "0xFF"), removing underscores.
fn parse_hex(s: &str) -> i64 {
    let s = &s[2..]; // skip 0x/0X
    i64::from_str_radix(&s.replace('_', ""), 16).unwrap_or(0)
}

/// Parses an octal integer string slice (e.g., "0o77"), removing underscores.
fn parse_octal(s: &str) -> i64 {
    let s = &s[2..]; // skip 0o/0O
    i64::from_str_radix(&s.replace('_', ""), 8).unwrap_or(0)
}

/// Parses a binary integer string slice (e.g., "0b1010"), removing underscores.
fn parse_binary(s: &str) -> i64 {
    let s = &s[2..]; // skip 0b/0B
    i64::from_str_radix(&s.replace('_', ""), 2).unwrap_or(0)
}

/// Parses a floating-point number string slice, removing underscores.
fn parse_float(s: &str) -> f64 {
    s.replace('_', "").parse().unwrap_or(0.0)
}

/// Parses a resource literal string slice (e.g., "100J", "5ms").
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

/// Parses a string literal, including processing escape sequences like `\n`, `\t`, `\xHH`, `\u{XXXX}`.
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
                Some('x') => {
                    // Hex escape: \xHH
                    let mut hex = String::new();
                    for _ in 0..2 {
                        if let Some(&c) = chars.peek() {
                            if c.is_ascii_hexdigit() {
                                hex.push(c);
                                chars.next();
                            }
                        }
                    }
                    if let Ok(val) = u32::from_str_radix(&hex, 16) {
                        if let Some(ch) = char::from_u32(val) {
                            result.push(ch);
                        }
                    }
                }
                Some('u') => {
                    // Unicode escape: \u{XXXX}
                    if chars.peek() == Some(&'{') {
                        chars.next(); // consume {
                        let mut hex = String::new();
                        while let Some(&c) = chars.peek() {
                            if c == '}' {
                                chars.next();
                                break;
                            }
                            if c.is_ascii_hexdigit() {
                                hex.push(c);
                                chars.next();
                            } else {
                                break;
                            }
                        }
                        if let Ok(val) = u32::from_str_radix(&hex, 16) {
                            if let Some(ch) = char::from_u32(val) {
                                result.push(ch);
                            }
                        }
                    }
                }
                Some(c) => result.push(c),
                None => break,
            }
        } else {
            result.push(c);
        }
    }

    SmolStr::new(&result)
}

/// Parses a character literal, including processing escape sequences.
fn parse_char(s: &str) -> char {
    let inner = &s[1..s.len() - 1];
    let mut chars = inner.chars().peekable();

    match chars.next() {
        Some('\\') => match chars.next() {
            Some('n') => '\n',
            Some('r') => '\r',
            Some('t') => '\t',
            Some('\\') => '\\',
            Some('\'') => '\'',
            Some('0') => '\0',
            Some('x') => {
                // Hex escape: \xHH
                let mut hex = String::new();
                for _ in 0..2 {
                    if let Some(&c) = chars.peek() {
                        if c.is_ascii_hexdigit() {
                            hex.push(c);
                            chars.next();
                        }
                    }
                }
                u32::from_str_radix(&hex, 16)
                    .ok()
                    .and_then(char::from_u32)
                    .unwrap_or('\0')
            }
            Some('u') => {
                // Unicode escape: \u{XXXX}
                if chars.peek() == Some(&'{') {
                    chars.next();
                    let mut hex = String::new();
                    while let Some(&c) = chars.peek() {
                        if c == '}' {
                            chars.next();
                            break;
                        }
                        if c.is_ascii_hexdigit() {
                            hex.push(c);
                            chars.next();
                        } else {
                            break;
                        }
                    }
                    u32::from_str_radix(&hex, 16)
                        .ok()
                        .and_then(char::from_u32)
                        .unwrap_or('\0')
                } else {
                    'u'
                }
            }
            Some(c) => c,
            None => '\0',
        },
        Some(c) => c,
        None => '\0',
    }
}

/// Check if a character is valid as the first character of an identifier (XID_Start).
/// This includes ASCII letters, underscore, and Unicode letter/ideograph characters.
/// Check if a character is valid as the first character of an identifier (XID_Start).
/// This includes ASCII letters, underscore, and Unicode letter/ideograph characters.
fn is_xid_start(c: char) -> bool {
    c == '_' || c.is_alphabetic()
}

/// Check if a character is valid in the continuation of an identifier (XID_Continue).
/// This includes XID_Start characters plus digits.
/// Check if a character is valid in the continuation of an identifier (XID_Continue).
/// This includes XID_Start characters plus digits.
fn is_xid_continue(c: char) -> bool {
    is_xid_start(c) || c.is_numeric()
}

/// Lexer for Eclexia source code.
/// Lexer for Eclexia source code.
///
/// It wraps the `logos::Lexer` and provides methods for peeking and advancing
/// tokens, as well as checking for EOF.
pub struct Lexer<'src> {
    inner: logos::Lexer<'src, TokenKind>,
    peeked: Option<Token>,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer for the given source.
    /// Create a new lexer for the given source.
    pub fn new(source: &'src str) -> Self {
        Self {
            inner: TokenKind::lexer(source),
            peeked: None,
        }
    }

    /// Get the next token.
    /// Get the next token.
    ///
    /// This consumes the peeked token if available, otherwise it advances the inner lexer.
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
                Token::new(
                    TokenKind::Error,
                    Span::new(span.start as u32, span.end as u32),
                )
            }
            None => Token::new(TokenKind::Eof, Span::empty(self.inner.span().end as u32)),
        }
    }

    /// Peek at the next token without consuming it.
    /// Peek at the next token without consuming it.
    ///
    /// The peeked token is cached and returned on subsequent calls to `peek`.
    pub fn peek(&mut self) -> &Token {
        if self.peeked.is_none() {
            self.peeked = Some(self.next());
        }
        self.peeked.as_ref().unwrap()
    }

    /// Check if we've reached the end of input.
    /// Check if we've reached the end of input.
    pub fn is_eof(&mut self) -> bool {
        matches!(self.peek().kind, TokenKind::Eof)
    }

    /// Get the current source slice for a span.
    /// Get the current source slice for a span.
    pub fn slice(&self) -> &'src str {
        self.inner.slice()
    }

    /// Get the source string.
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
    fn test_new_keywords() {
        let source = "pub module mod loop effect handle use where static extern";
        let tokens: Vec<_> = Lexer::new(source).collect();
        assert!(matches!(tokens[0].kind, TokenKind::Pub));
        assert!(matches!(tokens[1].kind, TokenKind::Module));
        assert!(matches!(tokens[2].kind, TokenKind::Mod));
        assert!(matches!(tokens[3].kind, TokenKind::Loop));
        assert!(matches!(tokens[4].kind, TokenKind::Effect));
        assert!(matches!(tokens[5].kind, TokenKind::Handle));
        assert!(matches!(tokens[6].kind, TokenKind::Use));
        assert!(matches!(tokens[7].kind, TokenKind::Where));
        assert!(matches!(tokens[8].kind, TokenKind::Static));
        assert!(matches!(tokens[9].kind, TokenKind::Extern));
    }

    #[test]
    fn test_self_tokens() {
        let source = "self Self";
        let tokens: Vec<_> = Lexer::new(source).collect();
        assert!(matches!(tokens[0].kind, TokenKind::SelfLower));
        assert!(matches!(tokens[1].kind, TokenKind::SelfUpper));
    }

    #[test]
    fn test_compound_assignment() {
        let source = "+= -= *= /= %=";
        let tokens: Vec<_> = Lexer::new(source).collect();
        assert!(matches!(tokens[0].kind, TokenKind::PlusEq));
        assert!(matches!(tokens[1].kind, TokenKind::MinusEq));
        assert!(matches!(tokens[2].kind, TokenKind::StarEq));
        assert!(matches!(tokens[3].kind, TokenKind::SlashEq));
        assert!(matches!(tokens[4].kind, TokenKind::PercentEq));
    }

    #[test]
    fn test_inclusive_range() {
        let source = ".. ..=";
        let tokens: Vec<_> = Lexer::new(source).collect();
        assert!(matches!(tokens[0].kind, TokenKind::DotDot));
        assert!(matches!(tokens[1].kind, TokenKind::DotDotEq));
    }

    #[test]
    fn test_hex_octal_binary_literals() {
        let source = "0xFF 0o77 0b1010 0x1A_2B";
        let tokens: Vec<_> = Lexer::new(source).collect();
        assert!(matches!(tokens[0].kind, TokenKind::HexInteger(255)));
        assert!(matches!(tokens[1].kind, TokenKind::OctalInteger(63)));
        assert!(matches!(tokens[2].kind, TokenKind::BinaryInteger(10)));
        assert!(matches!(tokens[3].kind, TokenKind::HexInteger(6699)));
    }

    #[test]
    fn test_new_keywords_stage1() {
        let source = "case do energy latency memory unit carbon ref super";
        let tokens: Vec<_> = Lexer::new(source).collect();
        assert!(matches!(tokens[0].kind, TokenKind::Case));
        assert!(matches!(tokens[1].kind, TokenKind::Do));
        assert!(matches!(tokens[2].kind, TokenKind::Energy));
        assert!(matches!(tokens[3].kind, TokenKind::Latency));
        assert!(matches!(tokens[4].kind, TokenKind::Memory));
        assert!(matches!(tokens[5].kind, TokenKind::Unit));
        assert!(matches!(tokens[6].kind, TokenKind::Carbon));
        assert!(matches!(tokens[7].kind, TokenKind::Ref));
        assert!(matches!(tokens[8].kind, TokenKind::Super));
    }

    #[test]
    fn test_caret_eq_compound_assignment() {
        let source = "^= <<= >>= &= |= **=";
        let tokens: Vec<_> = Lexer::new(source).collect();
        assert!(matches!(tokens[0].kind, TokenKind::CaretEq));
        assert!(matches!(tokens[1].kind, TokenKind::LtLtEq));
        assert!(matches!(tokens[2].kind, TokenKind::GtGtEq));
        assert!(matches!(tokens[3].kind, TokenKind::AmpEq));
        assert!(matches!(tokens[4].kind, TokenKind::PipeEq));
        assert!(matches!(tokens[5].kind, TokenKind::StarStarEq));
    }

    #[test]
    fn test_raw_strings() {
        let source = r##"r"hello\nworld" r#"hash"raw"#"##;
        let tokens: Vec<_> = Lexer::new(source).collect();
        if let TokenKind::RawString(s) = &tokens[0].kind {
            assert_eq!(s.as_str(), "hello\\nworld");
        } else {
            panic!("Expected raw string, got {:?}", tokens[0].kind);
        }
        if let TokenKind::RawStringHash(s) = &tokens[1].kind {
            assert_eq!(s.as_str(), "hash\"raw");
        } else {
            panic!("Expected raw string hash, got {:?}", tokens[1].kind);
        }
    }

    #[test]
    fn test_hex_escape_in_string() {
        let source = r#""\x41\x42""#;
        let tokens: Vec<_> = Lexer::new(source).collect();
        if let TokenKind::String(s) = &tokens[0].kind {
            assert_eq!(s.as_str(), "AB");
        } else {
            panic!("Expected string literal");
        }
    }

    #[test]
    fn test_unicode_escape_in_string() {
        let source = r#""\u{03C0}""#;
        let tokens: Vec<_> = Lexer::new(source).collect();
        if let TokenKind::String(s) = &tokens[0].kind {
            assert_eq!(s.as_str(), "\u{03C0}"); // π
        } else {
            panic!("Expected string literal");
        }
    }

    #[test]
    fn test_doc_comments() {
        let source = "/// This is a doc comment\nlet x = 5";
        let tokens: Vec<_> = Lexer::new(source).collect();
        if let TokenKind::DocComment(s) = &tokens[0].kind {
            assert_eq!(s.as_str(), "This is a doc comment");
        } else {
            panic!("Expected doc comment, got {:?}", tokens[0].kind);
        }
        assert!(matches!(tokens[1].kind, TokenKind::Let));
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
