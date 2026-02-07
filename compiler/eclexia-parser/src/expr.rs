// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Expression parsing using Pratt parsing for operators.

use eclexia_ast::*;
use eclexia_lexer::{TokenKind, ResourceLiteral};

use crate::{Parser, ParseResult, ParseError};

/// Operator precedence levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Precedence {
    None = 0,
    Assignment = 1,   // =
    Or = 2,           // or, ||
    And = 3,          // and, &&
    Equality = 4,     // ==, !=
    Comparison = 5,   // <, >, <=, >=
    BitOr = 6,        // |
    BitXor = 7,       // ^
    BitAnd = 8,       // &
    Shift = 9,        // <<, >>
    Term = 10,        // +, -
    Factor = 11,      // *, /, %
    Power = 12,       // **
    Unary = 13,       // !, -, ~
    Call = 14,        // (), [], .
    Primary = 15,
}

impl<'src> Parser<'src> {
    /// Parse an expression.
    pub fn parse_expr(&mut self, file: &mut SourceFile) -> ParseResult<ExprId> {
        self.parse_expr_prec(file, Precedence::None)
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
                    _ => unreachable!(),
                };
                let operand = self.parse_expr_prec(file, Precedence::Unary)?;
                let span = token.span.merge(file.exprs[operand].span);
                let expr = Expr {
                    span,
                    kind: ExprKind::Unary { op, operand },
                };
                Ok(file.exprs.alloc(expr))
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
            TokenKind::Integer(n) => ExprKind::Literal(Literal::Int(n)),
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
            TokenKind::Ident(name) => ExprKind::Var(name),

            // Parenthesized expression or tuple
            TokenKind::LParen => {
                if self.check(TokenKind::RParen) {
                    self.advance();
                    ExprKind::Literal(Literal::Unit)
                } else {
                    let first = self.parse_expr(file)?;

                    if self.check(TokenKind::Comma) {
                        // Tuple
                        let mut elems = vec![first];
                        while self.check(TokenKind::Comma) {
                            self.advance();
                            if self.check(TokenKind::RParen) {
                                break;
                            }
                            elems.push(self.parse_expr(file)?);
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

            // Array literal
            TokenKind::LBracket => {
                let mut elems = Vec::new();
                if !self.check(TokenKind::RBracket) {
                    loop {
                        elems.push(self.parse_expr(file)?);
                        if !self.check(TokenKind::Comma) {
                            break;
                        }
                        self.advance();
                    }
                }
                self.expect(TokenKind::RBracket)?;
                ExprKind::Array(elems)
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
                let condition = self.parse_expr(file)?;

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
                let scrutinee = self.parse_expr(file)?;
                self.expect(TokenKind::LBrace)?;

                let mut arms = Vec::new();
                while !self.check(TokenKind::RBrace) && !self.is_eof() {
                    let arm = self.parse_match_arm(file)?;
                    arms.push(arm);

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

            // Lambda with pipe syntax: |x, y| expr
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

                // Field access or method call
                TokenKind::Dot => {
                    self.advance();
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
    fn parse_pattern(&mut self) -> ParseResult<Pattern> {
        let token = self.advance();

        match token.kind {
            TokenKind::Underscore => Ok(Pattern::Wildcard),
            TokenKind::Ident(name) => {
                if self.check(TokenKind::LParen) {
                    // Constructor pattern
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
                    Ok(Pattern::Constructor { name, fields })
                } else {
                    Ok(Pattern::Var(name))
                }
            }
            TokenKind::Integer(n) => Ok(Pattern::Literal(Literal::Int(n))),
            TokenKind::Float(f) => Ok(Pattern::Literal(Literal::Float(f))),
            TokenKind::String(s) => Ok(Pattern::Literal(Literal::String(s))),
            TokenKind::True => Ok(Pattern::Literal(Literal::Bool(true))),
            TokenKind::False => Ok(Pattern::Literal(Literal::Bool(false))),
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
                Ok(Pattern::Tuple(patterns))
            }
            _ => Err(ParseError::unexpected_token(token, "pattern")),
        }
    }

    /// Get the precedence of the current token.
    fn current_precedence(&mut self) -> Precedence {
        match self.peek().kind {
            TokenKind::PipePipe | TokenKind::Or => Precedence::Or,
            TokenKind::AmpAmp | TokenKind::And => Precedence::And,
            TokenKind::EqEq | TokenKind::BangEq => Precedence::Equality,
            TokenKind::Lt | TokenKind::Le | TokenKind::Gt | TokenKind::Ge => Precedence::Comparison,
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
