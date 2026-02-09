// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Expression parsing using Pratt parsing for operators.

use eclexia_ast::*;
use eclexia_lexer::{TokenKind, ResourceLiteral};
use smol_str::SmolStr;

use crate::{Parser, ParseResult, ParseError};

/// Operator precedence levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
#[allow(dead_code)]
pub enum Precedence {
    /// No precedence (lowest).
    None = 0,
    /// Assignment precedence (`=`).
    Assignment = 1,
    /// Logical OR precedence (`or`, `||`).
    Or = 2,
    /// Logical AND precedence (`and`, `&&`).
    And = 3,
    /// Equality comparison precedence (`==`, `!=`).
    Equality = 4,
    /// Type cast precedence (`as`).
    Cast = 5,
    /// Relational comparison precedence (`<`, `>`, `<=`, `>=`).
    Comparison = 6,
    /// Bitwise OR precedence (`|`).
    BitOr = 7,
    /// Bitwise XOR precedence (`^`).
    BitXor = 8,
    /// Bitwise AND precedence (`&`).
    BitAnd = 9,
    /// Bit shift precedence (`<<`, `>>`).
    Shift = 10,
    /// Additive precedence (`+`, `-`).
    Term = 11,
    /// Multiplicative precedence (`*`, `/`, `%`).
    Factor = 12,
    /// Exponentiation precedence (`**`).
    Power = 13,
    /// Unary operator precedence (`!`, `-`, `~`).
    Unary = 14,
    /// Call and member access precedence (`()`, `[]`, `.`).
    Call = 15,
    /// Primary expression precedence (highest).
    Primary = 16,
}

impl<'src> Parser<'src> {
    /// Parse an expression.
    pub fn parse_expr(&mut self, file: &mut SourceFile) -> ParseResult<ExprId> {
        self.parse_expr_prec(file, Precedence::None)
    }

    /// Parse an expression without struct literals (for contexts where { starts a block).
    pub fn parse_expr_no_struct(&mut self, file: &mut SourceFile) -> ParseResult<ExprId> {
        // Set flag to disable struct literals
        let old_flag = self.no_struct_literals;
        self.no_struct_literals = true;

        let result = self.parse_expr_prec(file, Precedence::None);

        // Restore flag
        self.no_struct_literals = old_flag;

        result
    }

    /// Parse an expression with a minimum precedence.
    fn parse_expr_prec(&mut self, file: &mut SourceFile, min_prec: Precedence) -> ParseResult<ExprId> {
        let mut lhs = self.parse_prefix(file)?;

        loop {
            let prec = self.current_precedence();
            if prec <= min_prec {
                break;
            }

            lhs = self.parse_infix(file, lhs, prec)?;
        }

        Ok(lhs)
    }

    /// Parse a prefix expression (primary or unary).
    fn parse_prefix(&mut self, file: &mut SourceFile) -> ParseResult<ExprId> {
        let token = self.peek().clone();

        match &token.kind {
            // Unary operators
            TokenKind::Minus | TokenKind::Bang | TokenKind::Tilde | TokenKind::Not => {
                self.advance();
                let op = match token.kind {
                    TokenKind::Minus => UnaryOp::Neg,
                    TokenKind::Bang | TokenKind::Not => UnaryOp::Not,
                    TokenKind::Tilde => UnaryOp::BitNot,
                    _ => return Err(ParseError::custom(token.span, "internal error: unexpected unary operator")),
                };
                let operand = self.parse_expr_prec(file, Precedence::Unary)?;
                let span = token.span.merge(file.exprs[operand].span);
                let expr = Expr {
                    span,
                    kind: ExprKind::Unary { op, operand },
                };
                Ok(file.exprs.alloc(expr))
            }

            // Borrow: &expr or &mut expr
            TokenKind::Amp => {
                self.advance();
                let mutable = if self.check(TokenKind::Mut) {
                    self.advance();
                    true
                } else {
                    false
                };
                let operand = self.parse_expr_prec(file, Precedence::Unary)?;
                let span = token.span.merge(file.exprs[operand].span);
                let expr = Expr {
                    span,
                    kind: ExprKind::Borrow { expr: operand, mutable },
                };
                Ok(file.exprs.alloc(expr))
            }

            // Dereference: *expr
            TokenKind::Star => {
                self.advance();
                let operand = self.parse_expr_prec(file, Precedence::Unary)?;
                let span = token.span.merge(file.exprs[operand].span);
                let expr = Expr {
                    span,
                    kind: ExprKind::Deref(operand),
                };
                Ok(file.exprs.alloc(expr))
            }

            // Open range prefix: ..expr or ..=expr
            TokenKind::DotDot | TokenKind::DotDotEq => {
                let inclusive = matches!(token.kind, TokenKind::DotDotEq);
                self.advance();
                let op = if inclusive { BinaryOp::RangeInclusive } else { BinaryOp::Range };
                // Check if there's an operand (..b vs just ..)
                if self.check(TokenKind::Semi) || self.check(TokenKind::RBrace)
                    || self.check(TokenKind::RParen) || self.check(TokenKind::RBracket)
                    || self.check(TokenKind::Comma) || self.is_eof()
                {
                    // Full range: ..
                    let unit = file.exprs.alloc(Expr {
                        span: token.span,
                        kind: ExprKind::Literal(Literal::Unit),
                    });
                    let range_expr = Expr {
                        span: token.span,
                        kind: ExprKind::Binary { op, lhs: unit, rhs: unit },
                    };
                    return Ok(file.exprs.alloc(range_expr));
                }
                let rhs = self.parse_expr_prec(file, Precedence::Comparison)?;
                let lhs = file.exprs.alloc(Expr {
                    span: token.span,
                    kind: ExprKind::Literal(Literal::Unit),
                });
                let span = token.span.merge(file.exprs[rhs].span);
                let range_expr = Expr {
                    span,
                    kind: ExprKind::Binary { op, lhs, rhs },
                };
                return Ok(file.exprs.alloc(range_expr));
            }

            // Primary expressions
            _ => self.parse_primary(file),
        }
    }

    /// Parse a primary expression.
    fn parse_primary(&mut self, file: &mut SourceFile) -> ParseResult<ExprId> {
        let token = self.advance();

        let kind = match token.kind {
            // Literals
            TokenKind::Integer(n) | TokenKind::HexInteger(n)
            | TokenKind::OctalInteger(n) | TokenKind::BinaryInteger(n) => ExprKind::Literal(Literal::Int(n)),
            TokenKind::Float(f) => ExprKind::Literal(Literal::Float(f)),
            TokenKind::String(s) => ExprKind::Literal(Literal::String(s)),
            TokenKind::Char(c) => ExprKind::Literal(Literal::Char(c)),
            TokenKind::True => ExprKind::Literal(Literal::Bool(true)),
            TokenKind::False => ExprKind::Literal(Literal::Bool(false)),

            // Resource literal
            TokenKind::Resource(ResourceLiteral { value, unit }) => {
                ExprKind::Resource(ResourceAmount {
                    value,
                    unit: Some(unit),
                })
            }

            // Identifier
            // NOTE: Struct literals (Name { field: value }) are currently NOT supported
            // in expression position due to ambiguity with blocks in contexts like:
            //   for x in arr { body }
            // Where `arr {` could be mistaken for a struct literal.
            //
            // Workaround: Use explicit constructor functions or parse struct literals
            // only in unambiguous contexts (future enhancement).
            TokenKind::Ident(name) => ExprKind::Var(name),
            // Resource keywords are contextual — valid as variable names
            TokenKind::Energy => ExprKind::Var(SmolStr::new("energy")),
            TokenKind::Latency => ExprKind::Var(SmolStr::new("latency")),
            TokenKind::Memory => ExprKind::Var(SmolStr::new("memory")),
            TokenKind::Carbon => ExprKind::Var(SmolStr::new("carbon")),

            // Parenthesized expression or tuple
            TokenKind::LParen => {
                if self.check(TokenKind::RParen) {
                    self.advance();
                    ExprKind::Literal(Literal::Unit)
                } else {
                    let first = match self.parse_expr(file) {
                        Ok(expr) => expr,
                        Err(e) => {
                            self.errors.push(e);
                            let end = self.recover_to_closing_delimiter(TokenKind::RParen);
                            return Ok(file.exprs.alloc(Expr {
                                span: token.span.merge(end),
                                kind: ExprKind::Error,
                            }));
                        }
                    };

                    if self.check(TokenKind::Comma) {
                        // Tuple
                        let mut elems = vec![first];
                        while self.check(TokenKind::Comma) {
                            self.advance();
                            if self.check(TokenKind::RParen) {
                                break;
                            }
                            match self.parse_expr(file) {
                                Ok(expr) => elems.push(expr),
                                Err(e) => {
                                    self.errors.push(e);
                                    // Skip to comma or closing paren
                                    while !self.is_eof()
                                        && !self.check(TokenKind::Comma)
                                        && !self.check(TokenKind::RParen)
                                    {
                                        self.advance();
                                    }
                                }
                            }
                        }
                        self.expect(TokenKind::RParen)?;
                        ExprKind::Tuple(elems)
                    } else {
                        self.expect(TokenKind::RParen)?;
                        // Just return the inner expression
                        return Ok(first);
                    }
                }
            }

            // Array literal or array repeat [value; count]
            TokenKind::LBracket => {
                if self.check(TokenKind::RBracket) {
                    self.advance();
                    ExprKind::Array(Vec::new())
                } else {
                    let first = match self.parse_expr(file) {
                        Ok(expr) => expr,
                        Err(e) => {
                            self.errors.push(e);
                            let end = self.recover_to_closing_delimiter(TokenKind::RBracket);
                            return Ok(file.exprs.alloc(Expr {
                                span: token.span.merge(end),
                                kind: ExprKind::Error,
                            }));
                        }
                    };
                    if self.check(TokenKind::Semi) {
                        // Array repeat: [value; count]
                        self.advance();
                        let count = match self.parse_expr(file) {
                            Ok(expr) => expr,
                            Err(e) => {
                                self.errors.push(e);
                                let end = self.recover_to_closing_delimiter(TokenKind::RBracket);
                                return Ok(file.exprs.alloc(Expr {
                                    span: token.span.merge(end),
                                    kind: ExprKind::Error,
                                }));
                            }
                        };
                        self.expect(TokenKind::RBracket)?;
                        ExprKind::ArrayRepeat { value: first, count }
                    } else {
                        // Array literal: [a, b, c]
                        let mut elems = vec![first];
                        while self.check(TokenKind::Comma) {
                            self.advance();
                            if self.check(TokenKind::RBracket) {
                                break;
                            }
                            match self.parse_expr(file) {
                                Ok(expr) => elems.push(expr),
                                Err(e) => {
                                    self.errors.push(e);
                                    // Skip to comma or closing bracket
                                    while !self.is_eof()
                                        && !self.check(TokenKind::Comma)
                                        && !self.check(TokenKind::RBracket)
                                    {
                                        self.advance();
                                    }
                                }
                            }
                        }
                        self.expect(TokenKind::RBracket)?;
                        ExprKind::Array(elems)
                    }
                }
            }

            // Block expression
            TokenKind::LBrace => {
                // Put token back (hacky but works for now)
                // Actually we need to handle this differently
                let block = self.parse_block_inner(file, token.span)?;
                ExprKind::Block(block)
            }

            // If expression
            TokenKind::If => {
                // Parse condition without struct literals to avoid ambiguity with then block
                let condition = self.parse_expr_no_struct(file)?;

                // Optional 'then' keyword
                if self.check(TokenKind::Then) {
                    self.advance();
                }

                let then_branch = self.parse_block(file)?;

                let else_branch = if self.check(TokenKind::Else) {
                    self.advance();
                    Some(self.parse_block(file)?)
                } else {
                    None
                };

                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                }
            }

            // Match expression
            TokenKind::Match => {
                let scrutinee = self.parse_expr_no_struct(file)?;
                self.expect(TokenKind::LBrace)?;

                let mut arms = Vec::new();
                while !self.check(TokenKind::RBrace) && !self.is_eof() {
                    match self.parse_match_arm(file) {
                        Ok(arm) => arms.push(arm),
                        Err(e) => {
                            self.errors.push(e);
                            // Skip to next arm (comma) or end of match (})
                            while !self.is_eof()
                                && !self.check(TokenKind::Comma)
                                && !self.check(TokenKind::RBrace)
                            {
                                self.advance();
                            }
                        }
                    }

                    if !self.check(TokenKind::Comma) {
                        break;
                    }
                    self.advance();
                }

                self.expect(TokenKind::RBrace)?;
                ExprKind::Match { scrutinee, arms }
            }

            // Lambda with fn syntax: fn(x, y) -> expr
            TokenKind::Fn => {
                self.expect(TokenKind::LParen)?;
                let params = self.parse_params(file)?;
                self.expect(TokenKind::RParen)?;
                self.expect(TokenKind::Arrow)?;
                let body = self.parse_expr(file)?;
                ExprKind::Lambda { params, body }
            }

            // Async block: async { ... }
            TokenKind::Async => {
                let block = self.parse_block(file)?;
                ExprKind::AsyncBlock(block)
            }

            // Handle expression: handle expr { effect_name::op(params) => body, ... }
            TokenKind::Handle => {
                let expr = self.parse_expr_no_struct(file)?;
                self.expect(TokenKind::LBrace)?;
                let mut handlers = Vec::new();
                while !self.check(TokenKind::RBrace) && !self.is_eof() {
                    let handler_start = self.peek().span;
                    let effect_name = self.expect_ident()?;
                    // Optional :: separator
                    let op_name = if self.check(TokenKind::ColonColon) {
                        self.advance();
                        self.expect_ident()?
                    } else {
                        effect_name.clone()
                    };
                    self.expect(TokenKind::LParen)?;
                    let params = self.parse_params(file)?;
                    self.expect(TokenKind::RParen)?;
                    // Optional resume parameter: resume k =>
                    let resume_param = if self.check_ident("resume") {
                        self.advance();
                        Some(self.expect_ident()?)
                    } else {
                        None
                    };
                    self.expect(TokenKind::FatArrow)?;
                    let handler_body = self.parse_block(file)?;
                    handlers.push(EffectHandler {
                        span: handler_start.merge(handler_body.span),
                        effect_name,
                        op_name,
                        params,
                        resume_param,
                        body: handler_body,
                    });
                    if !self.check(TokenKind::Comma) { break; }
                    self.advance();
                }
                self.expect(TokenKind::RBrace)?;
                ExprKind::Handle { expr, handlers }
            }

            // Return as expression
            TokenKind::Return => {
                let value = if !self.check(TokenKind::Semi) && !self.check(TokenKind::RBrace)
                    && !self.check(TokenKind::Comma)
                {
                    Some(self.parse_expr(file)?)
                } else {
                    None
                };
                ExprKind::ReturnExpr(value)
            }

            // Break as expression
            TokenKind::Break => {
                let label = if matches!(self.peek().kind, TokenKind::Ident(ref s) if s.starts_with('\'')) {
                    let s = self.expect_ident()?;
                    Some(s)
                } else {
                    None
                };
                let value = if !self.check(TokenKind::Semi) && !self.check(TokenKind::RBrace)
                    && !self.check(TokenKind::Comma)
                {
                    Some(self.parse_expr(file)?)
                } else {
                    None
                };
                ExprKind::BreakExpr { label, value }
            }

            // Continue as expression
            TokenKind::Continue => {
                let label = if matches!(self.peek().kind, TokenKind::Ident(ref s) if s.starts_with('\'')) {
                    let s = self.expect_ident()?;
                    Some(s)
                } else {
                    None
                };
                ExprKind::ContinueExpr { label }
            }

            // Lambda with pipe syntax: |x, y| expr  or  |x: T| -> U { body }
            TokenKind::Pipe => {
                let mut params = Vec::new();

                // Parse parameters between pipes
                if !self.check(TokenKind::Pipe) {
                    loop {
                        let name = self.expect_ident()?;
                        // Optional type annotation
                        let ty = if self.check(TokenKind::Colon) {
                            self.advance();
                            Some(self.parse_type(file)?)
                        } else {
                            None
                        };
                        params.push(Param {
                            span: token.span,
                            name,
                            ty,
                        });

                        if !self.check(TokenKind::Comma) {
                            break;
                        }
                        self.advance();
                    }
                }

                self.expect(TokenKind::Pipe)?;

                // Optional return type: -> Type
                if self.check(TokenKind::Arrow) {
                    self.advance();
                    let _return_ty = self.parse_type(file)?;
                    // Return type is consumed but not stored in Lambda AST
                    // (type checker infers it; stored type is informational)
                }

                let body = self.parse_expr(file)?;
                ExprKind::Lambda { params, body }
            }

            _ => {
                return Err(ParseError::unexpected_token(token, "expression"));
            }
        };

        let expr = Expr {
            span: token.span,
            kind,
        };
        let id = file.exprs.alloc(expr);

        // Parse postfix operations
        self.parse_postfix(file, id)
    }

    /// Parse a block expression when we've already consumed the opening brace.
    fn parse_block_inner(&mut self, file: &mut SourceFile, start: eclexia_ast::span::Span) -> ParseResult<Block> {
        let mut stmts = Vec::new();
        let mut expr = None;

        while !self.check(TokenKind::RBrace) && !self.is_eof() {
            match self.parse_stmt(file) {
                Ok(stmt) => {
                    let stmt_id = file.stmts.alloc(stmt);
                    stmts.push(stmt_id);
                }
                Err(e) => {
                    self.errors.push(e);
                    self.recover_to_stmt();
                }
            }
        }

        // Check if last statement can be a trailing expression
        if let Some(&last_id) = stmts.last() {
            if let StmtKind::Expr(expr_id) = file.stmts[last_id].kind {
                stmts.pop();
                expr = Some(expr_id);
            }
        }

        let end = self.expect(TokenKind::RBrace)?;
        let span = start.merge(end);

        Ok(Block { span, stmts, expr })
    }

    /// Parse postfix operations WITHOUT struct literals (for use in contexts where { starts a block).
    #[allow(dead_code)]
    fn parse_postfix_no_struct(&mut self, file: &mut SourceFile, mut expr: ExprId) -> ParseResult<ExprId> {
        loop {
            match self.peek().kind {
                // Try operator: expr?
                TokenKind::Question => {
                    self.advance();
                    let span = file.exprs[expr].span.merge(self.previous_span());
                    let try_expr = Expr {
                        span,
                        kind: ExprKind::Try(expr),
                    };
                    expr = file.exprs.alloc(try_expr);
                }

                // Function call
                TokenKind::LParen => {
                    self.advance();
                    let mut args = Vec::new();
                    if !self.check(TokenKind::RParen) {
                        loop {
                            args.push(self.parse_expr(file)?);
                            if !self.check(TokenKind::Comma) {
                                break;
                            }
                            self.advance();
                        }
                    }
                    let end = self.expect(TokenKind::RParen)?;

                    let span = file.exprs[expr].span.merge(end);
                    let call_expr = Expr {
                        span,
                        kind: ExprKind::Call { func: expr, args },
                    };
                    expr = file.exprs.alloc(call_expr);
                }

                // Field access, method call, or .await
                TokenKind::Dot => {
                    self.advance();
                    if self.check_ident("await") {
                        self.advance();
                        let span = file.exprs[expr].span.merge(self.previous_span());
                        let await_expr = Expr {
                            span,
                            kind: ExprKind::Await(expr),
                        };
                        expr = file.exprs.alloc(await_expr);
                    } else {
                        let field = self.expect_ident()?;

                        if self.check(TokenKind::LParen) {
                            // Method call
                            self.advance();
                            let mut args = Vec::new();
                            if !self.check(TokenKind::RParen) {
                                loop {
                                    args.push(self.parse_expr(file)?);
                                    if !self.check(TokenKind::Comma) {
                                        break;
                                    }
                                    self.advance();
                                }
                            }
                            let end = self.expect(TokenKind::RParen)?;

                            let span = file.exprs[expr].span.merge(end);
                            let method_expr = Expr {
                                span,
                                kind: ExprKind::MethodCall {
                                    receiver: expr,
                                    method: field,
                                    args,
                                },
                            };
                            expr = file.exprs.alloc(method_expr);
                        } else {
                            // Field access
                            let span = file.exprs[expr].span.merge(self.previous_span());
                            let field_expr = Expr {
                                span,
                                kind: ExprKind::Field { expr, field },
                            };
                            expr = file.exprs.alloc(field_expr);
                        }
                    }
                }

                // Index access
                TokenKind::LBracket => {
                    self.advance();
                    let index = self.parse_expr(file)?;
                    let end = self.expect(TokenKind::RBracket)?;

                    let span = file.exprs[expr].span.merge(end);
                    let index_expr = Expr {
                        span,
                        kind: ExprKind::Index { expr, index },
                    };
                    expr = file.exprs.alloc(index_expr);
                }

                // SKIP LBrace (struct literals) - that's the whole point of this function!
                _ => break,
            }
        }

        Ok(expr)
    }

    /// Parse postfix operations (calls, field access, indexing).
    fn parse_postfix(&mut self, file: &mut SourceFile, mut expr: ExprId) -> ParseResult<ExprId> {
        loop {
            match self.peek().kind {
                // Function call
                TokenKind::LParen => {
                    self.advance();
                    let mut args = Vec::new();
                    if !self.check(TokenKind::RParen) {
                        loop {
                            match self.parse_expr(file) {
                                Ok(arg) => args.push(arg),
                                Err(e) => {
                                    self.errors.push(e);
                                    // Skip to comma or closing paren
                                    while !self.is_eof()
                                        && !self.check(TokenKind::Comma)
                                        && !self.check(TokenKind::RParen)
                                    {
                                        self.advance();
                                    }
                                }
                            }
                            if !self.check(TokenKind::Comma) {
                                break;
                            }
                            self.advance();
                        }
                    }
                    let end = self.expect(TokenKind::RParen)?;

                    let span = file.exprs[expr].span.merge(end);
                    let call_expr = Expr {
                        span,
                        kind: ExprKind::Call { func: expr, args },
                    };
                    expr = file.exprs.alloc(call_expr);
                }

                // Try operator: expr?
                TokenKind::Question => {
                    self.advance();
                    let span = file.exprs[expr].span.merge(self.previous_span());
                    let try_expr = Expr {
                        span,
                        kind: ExprKind::Try(expr),
                    };
                    expr = file.exprs.alloc(try_expr);
                }

                // Field access, method call, or .await
                TokenKind::Dot => {
                    self.advance();
                    // Check for .await
                    if self.check_ident("await") {
                        self.advance();
                        let span = file.exprs[expr].span.merge(self.previous_span());
                        let await_expr = Expr {
                            span,
                            kind: ExprKind::Await(expr),
                        };
                        expr = file.exprs.alloc(await_expr);
                    } else {
                        let field = self.expect_ident()?;

                        if self.check(TokenKind::LParen) {
                            // Method call
                            self.advance();
                            let mut args = Vec::new();
                            if !self.check(TokenKind::RParen) {
                                loop {
                                    args.push(self.parse_expr(file)?);
                                    if !self.check(TokenKind::Comma) {
                                        break;
                                    }
                                    self.advance();
                                }
                            }
                            let end = self.expect(TokenKind::RParen)?;

                            let span = file.exprs[expr].span.merge(end);
                            let method_expr = Expr {
                                span,
                                kind: ExprKind::MethodCall {
                                    receiver: expr,
                                    method: field,
                                    args,
                                },
                            };
                            expr = file.exprs.alloc(method_expr);
                        } else {
                            // Field access
                            let span = file.exprs[expr].span.merge(self.previous_span());
                            let field_expr = Expr {
                                span,
                                kind: ExprKind::Field { expr, field },
                            };
                            expr = file.exprs.alloc(field_expr);
                        }
                    }
                }

                // Index access
                TokenKind::LBracket => {
                    self.advance();
                    let index = self.parse_expr(file)?;
                    let end = self.expect(TokenKind::RBracket)?;

                    let span = file.exprs[expr].span.merge(end);
                    let index_expr = Expr {
                        span,
                        kind: ExprKind::Index { expr, index },
                    };
                    expr = file.exprs.alloc(index_expr);
                }

                // Struct literal: Name { field: value, ... }
                // Only parse if expr is a Var (identifier) AND struct literals are enabled
                TokenKind::LBrace => {
                    // Skip if struct literals are disabled (for loop context)
                    if self.no_struct_literals {
                        break;
                    }

                    // Check if the current expression is an identifier
                    if !matches!(file.exprs[expr].kind, ExprKind::Var(_)) {
                        break;
                    }

                    // Extract the struct name - safe: guarded by matches! check above
                    let name = match &file.exprs[expr].kind {
                        ExprKind::Var(n) => n.clone(),
                        _ => return Err(ParseError::custom(file.exprs[expr].span, "internal error: expected identifier for struct literal")),
                    };

                    self.advance(); // consume {
                    let mut fields = Vec::new();

                    if !self.check(TokenKind::RBrace) {
                        loop {
                            let field_name = self.expect_ident()?;
                            self.expect(TokenKind::Colon)?;
                            let field_value = self.parse_expr(file)?;
                            fields.push((field_name, field_value));

                            if !self.check(TokenKind::Comma) {
                                break;
                            }
                            self.advance();

                            // Allow trailing comma
                            if self.check(TokenKind::RBrace) {
                                break;
                            }
                        }
                    }

                    let end = self.expect(TokenKind::RBrace)?;
                    let span = file.exprs[expr].span.merge(end);
                    let struct_expr = Expr {
                        span,
                        kind: ExprKind::Struct { name, fields },
                    };
                    expr = file.exprs.alloc(struct_expr);
                }

                _ => break,
            }
        }

        Ok(expr)
    }

    /// Parse an infix expression.
    fn parse_infix(
        &mut self,
        file: &mut SourceFile,
        lhs: ExprId,
        prec: Precedence,
    ) -> ParseResult<ExprId> {
        let token = self.advance();

        // Handle type cast specially (requires type, not expression)
        if matches!(token.kind, TokenKind::As) {
            let target_ty = self.parse_type(file)?;
            let span = file.exprs[lhs].span.merge(file.types[target_ty].span);
            let cast_expr = Expr {
                span,
                kind: ExprKind::Cast {
                    expr: lhs,
                    target_ty,
                },
            };
            return Ok(file.exprs.alloc(cast_expr));
        }

        let op = match token.kind {
            // Arithmetic
            TokenKind::Plus => BinaryOp::Add,
            TokenKind::Minus => BinaryOp::Sub,
            TokenKind::Star => BinaryOp::Mul,
            TokenKind::Slash => BinaryOp::Div,
            TokenKind::Percent => BinaryOp::Rem,
            TokenKind::StarStar => BinaryOp::Pow,

            // Comparison
            TokenKind::EqEq => BinaryOp::Eq,
            TokenKind::BangEq => BinaryOp::Ne,
            TokenKind::Lt => BinaryOp::Lt,
            TokenKind::Le => BinaryOp::Le,
            TokenKind::Gt => BinaryOp::Gt,
            TokenKind::Ge => BinaryOp::Ge,

            // Logical
            TokenKind::AmpAmp | TokenKind::And => BinaryOp::And,
            TokenKind::PipePipe | TokenKind::Or => BinaryOp::Or,

            // Bitwise
            TokenKind::Amp => BinaryOp::BitAnd,
            TokenKind::Pipe => BinaryOp::BitOr,
            TokenKind::Caret => BinaryOp::BitXor,
            TokenKind::LtLt => BinaryOp::Shl,
            TokenKind::GtGt => BinaryOp::Shr,

            // Range
            TokenKind::DotDot => BinaryOp::Range,
            TokenKind::DotDotEq => BinaryOp::RangeInclusive,

            _ => return Err(ParseError::unexpected_token(token, "operator")),
        };

        // Right associativity for ** (power)
        let next_prec = if matches!(op, BinaryOp::Pow) {
            Precedence::Power
        } else {
            prec
        };

        let rhs = self.parse_expr_prec(file, next_prec)?;

        let span = file.exprs[lhs].span.merge(file.exprs[rhs].span);
        let expr = Expr {
            span,
            kind: ExprKind::Binary { op, lhs, rhs },
        };
        Ok(file.exprs.alloc(expr))
    }

    /// Parse a match arm.
    fn parse_match_arm(&mut self, file: &mut SourceFile) -> ParseResult<MatchArm> {
        let start = self.peek().span;
        let pattern = self.parse_pattern()?;

        let guard = if self.check(TokenKind::If) {
            self.advance();
            Some(self.parse_expr(file)?)
        } else {
            None
        };

        self.expect(TokenKind::FatArrow)?;
        let body = self.parse_expr(file)?;

        let span = start.merge(file.exprs[body].span);

        Ok(MatchArm {
            span,
            pattern,
            guard,
            body,
        })
    }

    /// Parse a pattern.
    pub(crate) fn parse_pattern(&mut self) -> ParseResult<Pattern> {
        let mut pat = self.parse_single_pattern()?;

        // Check for or-pattern: pat1 | pat2 | pat3
        if self.check(TokenKind::Pipe) {
            let mut alternatives = vec![pat];
            while self.check(TokenKind::Pipe) {
                self.advance();
                alternatives.push(self.parse_single_pattern()?);
            }
            pat = Pattern::Or(alternatives);
        }

        Ok(pat)
    }

    /// Parse a single pattern (without or).
    fn parse_single_pattern(&mut self) -> ParseResult<Pattern> {
        let token = self.advance();

        let pat = match token.kind {
            TokenKind::Underscore => Pattern::Wildcard,
            // Rest pattern: ..
            TokenKind::DotDot => Pattern::Rest,
            // Ref pattern: ref name or ref mut name
            TokenKind::Ref => {
                let mutable = if self.check(TokenKind::Mut) {
                    self.advance();
                    true
                } else {
                    false
                };
                let name = self.expect_ident()?;
                Pattern::Reference { pattern: Box::new(Pattern::Var(name)), mutable }
            }
            // Reference pattern: &pat or &mut pat
            TokenKind::Amp => {
                let mutable = if self.check(TokenKind::Mut) {
                    self.advance();
                    true
                } else {
                    false
                };
                let inner = self.parse_single_pattern()?;
                Pattern::Reference { pattern: Box::new(inner), mutable }
            }
            TokenKind::Ident(name) => {
                if self.check(TokenKind::LParen) {
                    // Constructor pattern: Name(p1, p2)
                    self.advance();
                    let mut fields = Vec::new();
                    if !self.check(TokenKind::RParen) {
                        loop {
                            fields.push(self.parse_pattern()?);
                            if !self.check(TokenKind::Comma) {
                                break;
                            }
                            self.advance();
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    Pattern::Constructor { name, fields }
                } else if self.check(TokenKind::LBrace) {
                    // Struct pattern: Name { x, y: pat, .. }
                    self.advance();
                    let mut field_pats = Vec::new();
                    let mut rest = false;
                    if !self.check(TokenKind::RBrace) {
                        loop {
                            if self.check(TokenKind::DotDot) {
                                self.advance();
                                rest = true;
                                break;
                            }
                            let field_start = self.peek().span;
                            let field_name = self.expect_ident()?;
                            let field_pattern = if self.check(TokenKind::Colon) {
                                self.advance();
                                Some(self.parse_pattern()?)
                            } else {
                                None
                            };
                            field_pats.push(FieldPattern {
                                span: field_start.merge(self.previous_span()),
                                name: field_name,
                                pattern: field_pattern,
                            });
                            if !self.check(TokenKind::Comma) {
                                break;
                            }
                            self.advance();
                        }
                    }
                    self.expect(TokenKind::RBrace)?;
                    Pattern::Struct { name, fields: field_pats, rest }
                } else if self.check(TokenKind::At) {
                    // Binding pattern: name @ pattern
                    self.advance();
                    let inner = self.parse_single_pattern()?;
                    Pattern::Binding { name, pattern: Box::new(inner) }
                } else {
                    Pattern::Var(name)
                }
            }
            TokenKind::Integer(n) | TokenKind::HexInteger(n)
            | TokenKind::OctalInteger(n) | TokenKind::BinaryInteger(n) => {
                let lit_pat = Pattern::Literal(Literal::Int(n));
                // Check for range pattern: 1..5 or 1..=5
                if self.check(TokenKind::DotDot) || self.check(TokenKind::DotDotEq) {
                    let inclusive = self.check(TokenKind::DotDotEq);
                    self.advance();
                    let end_pat = self.parse_single_pattern()?;
                    Pattern::Range {
                        start: Some(Box::new(lit_pat)),
                        end: Some(Box::new(end_pat)),
                        inclusive,
                    }
                } else {
                    lit_pat
                }
            }
            TokenKind::Float(f) => Pattern::Literal(Literal::Float(f)),
            TokenKind::String(s) => Pattern::Literal(Literal::String(s)),
            TokenKind::Char(c) => Pattern::Literal(Literal::Char(c)),
            TokenKind::True => Pattern::Literal(Literal::Bool(true)),
            TokenKind::False => Pattern::Literal(Literal::Bool(false)),
            TokenKind::LParen => {
                let mut patterns = Vec::new();
                if !self.check(TokenKind::RParen) {
                    loop {
                        patterns.push(self.parse_pattern()?);
                        if !self.check(TokenKind::Comma) {
                            break;
                        }
                        self.advance();
                    }
                }
                self.expect(TokenKind::RParen)?;
                Pattern::Tuple(patterns)
            }
            // Slice pattern: [a, b, ..]
            TokenKind::LBracket => {
                let mut patterns = Vec::new();
                if !self.check(TokenKind::RBracket) {
                    loop {
                        patterns.push(self.parse_pattern()?);
                        if !self.check(TokenKind::Comma) {
                            break;
                        }
                        self.advance();
                    }
                }
                self.expect(TokenKind::RBracket)?;
                Pattern::Slice(patterns)
            }
            // Resource keywords are contextual — valid as variable names in patterns
            TokenKind::Energy => Pattern::Var(SmolStr::new("energy")),
            TokenKind::Latency => Pattern::Var(SmolStr::new("latency")),
            TokenKind::Memory => Pattern::Var(SmolStr::new("memory")),
            TokenKind::Carbon => Pattern::Var(SmolStr::new("carbon")),
            _ => return Err(ParseError::unexpected_token(token, "pattern")),
        };

        Ok(pat)
    }

    /// Get the precedence of the current token.
    fn current_precedence(&mut self) -> Precedence {
        match self.peek().kind {
            TokenKind::PipePipe | TokenKind::Or => Precedence::Or,
            TokenKind::AmpAmp | TokenKind::And => Precedence::And,
            TokenKind::EqEq | TokenKind::BangEq => Precedence::Equality,
            TokenKind::As => Precedence::Cast,
            TokenKind::Lt | TokenKind::Le | TokenKind::Gt | TokenKind::Ge => Precedence::Comparison,
            TokenKind::DotDot | TokenKind::DotDotEq => Precedence::Comparison,
            TokenKind::Pipe => Precedence::BitOr,
            TokenKind::Caret => Precedence::BitXor,
            TokenKind::Amp => Precedence::BitAnd,
            TokenKind::LtLt | TokenKind::GtGt => Precedence::Shift,
            TokenKind::Plus | TokenKind::Minus => Precedence::Term,
            TokenKind::Star | TokenKind::Slash | TokenKind::Percent => Precedence::Factor,
            TokenKind::StarStar => Precedence::Power,
            TokenKind::LParen | TokenKind::LBracket | TokenKind::Dot => Precedence::Call,
            _ => Precedence::None,
        }
    }
}
