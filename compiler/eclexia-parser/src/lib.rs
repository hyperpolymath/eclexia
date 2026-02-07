// SPDX-License-Identifier: AGPL-3.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Parser for the Eclexia programming language.
//!
//! This crate provides a hand-written recursive descent parser for Eclexia.
//! The parser is designed for:
//!
//! - Good error messages with recovery
//! - Incremental parsing support (future)
//! - Full source span preservation

mod error;
mod expr;

use eclexia_ast::span::Span;
use eclexia_ast::*;
use eclexia_lexer::{Lexer, Token, TokenKind, ResourceLiteral};
use smol_str::SmolStr;

pub use error::{ParseError, ParseResult};

/// Parser for Eclexia source code.
pub struct Parser<'src> {
    lexer: Lexer<'src>,
    source: &'src str,
    errors: Vec<ParseError>,
}

impl<'src> Parser<'src> {
    /// Create a new parser for the given source.
    pub fn new(source: &'src str) -> Self {
        Self {
            lexer: Lexer::new(source),
            source,
            errors: Vec::new(),
        }
    }

    /// Parse a complete source file.
    pub fn parse_file(&mut self) -> (SourceFile, Vec<ParseError>) {
        let mut file = SourceFile::new();

        while !self.is_eof() {
            match self.parse_item(&mut file) {
                Ok(item) => file.items.push(item),
                Err(e) => {
                    self.errors.push(e);
                    self.recover_to_item();
                }
            }
        }

        (file, std::mem::take(&mut self.errors))
    }

    /// Parse a single top-level item.
    fn parse_item(&mut self, file: &mut SourceFile) -> ParseResult<Item> {
        // Parse attributes (#[test], #[bench], etc.)
        let attributes = self.parse_attributes()?;

        let token = self.peek();

        match &token.kind {
            TokenKind::Adaptive => {
                let mut func = self.parse_adaptive_function(file)?;
                func.attributes = attributes;
                Ok(Item::AdaptiveFunction(func))
            }
            TokenKind::Def | TokenKind::Fn => {
                let mut func = self.parse_function(file)?;
                func.attributes = attributes;
                Ok(Item::Function(func))
            }
            TokenKind::Type => self.parse_type_def(file).map(Item::TypeDef),
            TokenKind::Import => self.parse_import().map(Item::Import),
            TokenKind::Const => self.parse_const(file).map(Item::Const),
            _ => Err(ParseError::unexpected_token(token.clone(), "item")),
        }
    }

    /// Parse attributes (#[name] or #[name(args)]) and annotations (@requires, @provides, etc.)
    fn parse_attributes(&mut self) -> ParseResult<Vec<Attribute>> {
        let mut attributes = Vec::new();

        // Parse #[...] style attributes
        while self.check(TokenKind::Hash) {
            self.advance(); // consume #
            self.expect(TokenKind::LBracket)?;

            let start = self.peek().span;
            let name = self.expect_ident()?;
            let mut args = Vec::new();

            // Optional arguments: #[attr(arg1, arg2)]
            if self.check(TokenKind::LParen) {
                self.advance();
                if !self.check(TokenKind::RParen) {
                    loop {
                        args.push(self.expect_ident()?);
                        if !self.check(TokenKind::Comma) {
                            break;
                        }
                        self.advance();
                    }
                }
                self.expect(TokenKind::RParen)?;
            }

            let end = self.expect(TokenKind::RBracket)?;
            let span = start.merge(end);

            attributes.push(Attribute { span, name, args });
        }

        // Parse @annotation(...) style annotations
        while self.check(TokenKind::AtRequires) || self.check(TokenKind::AtProvides) ||
              self.check(TokenKind::AtOptimize) || self.check(TokenKind::AtDeferUntil) {
            let token = self.advance();
            let start = token.span;

            // Get annotation name (requires, provides, optimize, defer_until)
            let name = match token.kind {
                TokenKind::AtRequires => SmolStr::new("requires"),
                TokenKind::AtProvides => SmolStr::new("provides"),
                TokenKind::AtOptimize => SmolStr::new("optimize"),
                TokenKind::AtDeferUntil => SmolStr::new("defer_until"),
                _ => unreachable!(),
            };

            let mut args = Vec::new();

            // Parse arguments: @requires(energy: 100J, time: 10ms)
            if self.check(TokenKind::LParen) {
                self.advance();
                if !self.check(TokenKind::RParen) {
                    loop {
                        // Parse resource: amount pairs
                        let resource = self.expect_ident()?;
                        args.push(resource.clone());

                        if self.check(TokenKind::Colon) {
                            self.advance();
                            // Parse the amount (could be resource literal or number)
                            let amount_token = self.advance();
                            let amount = match &amount_token.kind {
                                TokenKind::Resource(r) => {
                                    SmolStr::new(&format!("{}{}", r.value, r.unit))
                                }
                                TokenKind::Integer(n) => SmolStr::new(&n.to_string()),
                                TokenKind::Float(f) => SmolStr::new(&f.to_string()),
                                _ => SmolStr::new("unknown"),
                            };
                            args.push(amount);
                        }

                        if !self.check(TokenKind::Comma) {
                            break;
                        }
                        self.advance();
                    }
                }
                self.expect(TokenKind::RParen)?;
            }

            let span = start.merge(self.previous_span());
            attributes.push(Attribute { span, name, args });
        }

        Ok(attributes)
    }

    /// Parse a regular function definition.
    fn parse_function(&mut self, file: &mut SourceFile) -> ParseResult<Function> {
        let start = self.peek().span;

        // 'def' or 'fn'
        self.expect_one_of(&[TokenKind::Def, TokenKind::Fn])?;

        // Function name
        let name = self.expect_ident()?;

        // Type parameters (optional): <T, U, ...>
        let type_params = if self.check(TokenKind::Lt) {
            self.advance();
            let mut params = Vec::new();
            loop {
                params.push(self.expect_ident()?);
                if !self.check(TokenKind::Comma) {
                    break;
                }
                self.advance();
            }
            self.expect(TokenKind::Gt)?;
            params
        } else {
            Vec::new()
        };

        // Parameters
        self.expect(TokenKind::LParen)?;
        let params = self.parse_params(file)?;
        self.expect(TokenKind::RParen)?;

        // Return type (optional)
        let return_type = if self.check(TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type(file)?)
        } else {
            None
        };

        // Constraints
        let constraints = self.parse_constraints(file)?;

        // Body
        let body = self.parse_block(file)?;

        let span = start.merge(body.span);

        Ok(Function {
            span,
            name,
            type_params,
            params,
            return_type,
            constraints,
            attributes: vec![],
            body,
        })
    }

    /// Parse an adaptive function definition.
    fn parse_adaptive_function(&mut self, file: &mut SourceFile) -> ParseResult<AdaptiveFunction> {
        let start = self.peek().span;

        // 'adaptive'
        self.expect(TokenKind::Adaptive)?;

        // 'def' or 'fn'
        self.expect_one_of(&[TokenKind::Def, TokenKind::Fn])?;

        // Function name
        let name = self.expect_ident()?;

        // Type parameters (optional): <T, U, ...>
        let type_params = if self.check(TokenKind::Lt) {
            self.advance();
            let mut params = Vec::new();
            loop {
                params.push(self.expect_ident()?);
                if !self.check(TokenKind::Comma) {
                    break;
                }
                self.advance();
            }
            self.expect(TokenKind::Gt)?;
            params
        } else {
            Vec::new()
        };

        // Parameters
        self.expect(TokenKind::LParen)?;
        let params = self.parse_params(file)?;
        self.expect(TokenKind::RParen)?;

        // Return type (optional)
        let return_type = if self.check(TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type(file)?)
        } else {
            None
        };

        // Constraints
        let constraints = self.parse_constraints(file)?;

        // Optimize directives
        let optimize = self.parse_optimize_directives()?;

        // Body with solutions
        self.expect(TokenKind::LBrace)?;
        let solutions = self.parse_solutions(file)?;
        let end = self.expect(TokenKind::RBrace)?;

        let span = start.merge(end);

        Ok(AdaptiveFunction {
            span,
            name,
            type_params,
            params,
            return_type,
            constraints,
            attributes: vec![],
            optimize,
            solutions,
        })
    }

    /// Parse function parameters.
    fn parse_params(&mut self, file: &mut SourceFile) -> ParseResult<Vec<Param>> {
        let mut params = Vec::new();

        if !self.check(TokenKind::RParen) {
            loop {
                let param = self.parse_param(file)?;
                params.push(param);

                if !self.check(TokenKind::Comma) {
                    break;
                }
                self.advance();
            }
        }

        Ok(params)
    }

    /// Parse a single parameter.
    fn parse_param(&mut self, file: &mut SourceFile) -> ParseResult<Param> {
        let start = self.peek().span;
        let name = self.expect_ident()?;

        let ty = if self.check(TokenKind::Colon) {
            self.advance();
            Some(self.parse_type(file)?)
        } else {
            None
        };

        let span = if let Some(ty_id) = ty {
            start.merge(file.types[ty_id].span)
        } else {
            start
        };

        Ok(Param { span, name, ty })
    }

    /// Parse constraint annotations (@requires).
    fn parse_constraints(&mut self, file: &mut SourceFile) -> ParseResult<Vec<Constraint>> {
        let mut constraints = Vec::new();

        while self.check(TokenKind::AtRequires) {
            let start = self.advance().span;
            self.expect(TokenKind::Colon)?;

            // Parse constraint expression
            let kind = self.parse_constraint_kind(file)?;
            let span = start.merge(self.previous_span());

            constraints.push(Constraint { span, kind });

            // Multiple constraints separated by comma
            while self.check(TokenKind::Comma) {
                self.advance();
                let kind = self.parse_constraint_kind(file)?;
                constraints.push(Constraint {
                    span: self.previous_span(),
                    kind,
                });
            }
        }

        Ok(constraints)
    }

    /// Parse a constraint kind.
    fn parse_constraint_kind(&mut self, file: &mut SourceFile) -> ParseResult<ConstraintKind> {
        let resource = self.expect_ident()?;

        let op = match self.peek().kind {
            TokenKind::Lt => CompareOp::Lt,
            TokenKind::Le => CompareOp::Le,
            TokenKind::Gt => CompareOp::Gt,
            TokenKind::Ge => CompareOp::Ge,
            TokenKind::EqEq => CompareOp::Eq,
            _ => {
                // Might be a predicate expression
                let expr = self.parse_expr(file)?;
                return Ok(ConstraintKind::Predicate(expr));
            }
        };
        self.advance();

        let amount = self.parse_resource_amount()?;

        Ok(ConstraintKind::Resource { resource, op, amount })
    }

    /// Parse a resource amount (e.g., 100J, 5ms).
    fn parse_resource_amount(&mut self) -> ParseResult<ResourceAmount> {
        let token = self.advance();

        match &token.kind {
            TokenKind::Resource(ResourceLiteral { value, unit }) => Ok(ResourceAmount {
                value: *value,
                unit: Some(unit.clone()),
            }),
            TokenKind::Integer(n) => Ok(ResourceAmount {
                value: *n as f64,
                unit: None,
            }),
            TokenKind::Float(f) => Ok(ResourceAmount {
                value: *f,
                unit: None,
            }),
            _ => Err(ParseError::unexpected_token(token, "resource amount")),
        }
    }

    /// Parse optimize directives.
    fn parse_optimize_directives(&mut self) -> ParseResult<Vec<Objective>> {
        let mut objectives = Vec::new();

        while self.check(TokenKind::AtOptimize) {
            let start = self.advance().span;
            self.expect(TokenKind::Colon)?;

            loop {
                let direction = if self.check(TokenKind::Minimize) {
                    self.advance();
                    OptimizeDirection::Minimize
                } else if self.check(TokenKind::Maximize) {
                    self.advance();
                    OptimizeDirection::Maximize
                } else {
                    return Err(ParseError::unexpected_token(
                        self.peek().clone(),
                        "minimize or maximize",
                    ));
                };

                let target = self.expect_ident()?;
                let span = start.merge(self.previous_span());

                objectives.push(Objective {
                    span,
                    direction,
                    target,
                });

                if !self.check(TokenKind::Comma) {
                    break;
                }
                self.advance();
            }
        }

        Ok(objectives)
    }

    /// Parse solution alternatives within an adaptive function.
    fn parse_solutions(&mut self, file: &mut SourceFile) -> ParseResult<Vec<Solution>> {
        let mut solutions = Vec::new();

        while self.check(TokenKind::AtSolution) {
            let solution = self.parse_solution(file)?;
            solutions.push(solution);
        }

        Ok(solutions)
    }

    /// Parse a single solution alternative.
    fn parse_solution(&mut self, file: &mut SourceFile) -> ParseResult<Solution> {
        let start = self.expect(TokenKind::AtSolution)?;

        // Solution name (string literal)
        let name = match self.advance().kind {
            TokenKind::String(s) => s,
            TokenKind::Ident(s) => s,
            _ => return Err(ParseError::unexpected_token(self.peek().clone(), "solution name")),
        };

        self.expect(TokenKind::Colon)?;

        // @when clause (optional)
        let when_clause = if self.check(TokenKind::AtWhen) {
            self.advance();
            self.expect(TokenKind::Colon)?;
            Some(self.parse_expr(file)?)
        } else {
            None
        };

        // @provides clause
        let mut provides = Vec::new();
        while self.check(TokenKind::AtProvides) {
            self.advance();
            self.expect(TokenKind::Colon)?;

            loop {
                let resource = self.expect_ident()?;
                self.expect(TokenKind::Colon)?;
                let amount = self.parse_resource_amount()?;

                provides.push(ResourceProvision {
                    span: self.previous_span(),
                    resource,
                    amount,
                });

                if !self.check(TokenKind::Comma) {
                    break;
                }
                self.advance();
            }
        }

        // Solution body
        let body = self.parse_block(file)?;
        let span = start.merge(body.span);

        Ok(Solution {
            span,
            name,
            when_clause,
            provides,
            body,
        })
    }

    /// Parse a block of statements.
    fn parse_block(&mut self, file: &mut SourceFile) -> ParseResult<Block> {
        let start = self.expect(TokenKind::LBrace)?;
        let mut stmts = Vec::new();
        let mut expr = None;

        while !self.check(TokenKind::RBrace) && !self.is_eof() {
            // Try to parse a statement
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
                // Remove from statements and set as block expression
                stmts.pop();
                expr = Some(expr_id);
            }
        }

        let end = self.expect(TokenKind::RBrace)?;
        let span = start.merge(end);

        Ok(Block { span, stmts, expr })
    }

    /// Parse a statement.
    fn parse_stmt(&mut self, file: &mut SourceFile) -> ParseResult<Stmt> {
        let token = self.peek();
        let start = token.span;

        let kind = match &token.kind {
            TokenKind::Let => {
                self.advance();
                let name = self.expect_ident()?;

                let ty = if self.check(TokenKind::Colon) {
                    self.advance();
                    Some(self.parse_type(file)?)
                } else {
                    None
                };

                self.expect(TokenKind::Eq)?;
                let value = self.parse_expr(file)?;

                StmtKind::Let { name, ty, value }
            }
            TokenKind::Return => {
                self.advance();
                let value = if !self.check(TokenKind::Semi) && !self.check(TokenKind::RBrace) {
                    Some(self.parse_expr(file)?)
                } else {
                    None
                };
                StmtKind::Return(value)
            }
            TokenKind::While => {
                self.advance();
                let condition = self.parse_expr(file)?;
                let body = self.parse_block(file)?;
                StmtKind::While { condition, body }
            }
            TokenKind::For => {
                self.advance();
                let name = self.expect_ident()?;
                self.expect(TokenKind::In)?;
                let iter = self.parse_expr(file)?;
                let body = self.parse_block(file)?;
                StmtKind::For { name, iter, body }
            }
            _ => {
                let expr = self.parse_expr(file)?;
                StmtKind::Expr(expr)
            }
        };

        // Optional semicolon
        if self.check(TokenKind::Semi) {
            self.advance();
        }

        let span = start.merge(self.previous_span());
        Ok(Stmt { span, kind })
    }

    /// Parse a type definition.
    fn parse_type_def(&mut self, file: &mut SourceFile) -> ParseResult<TypeDef> {
        let start = self.expect(TokenKind::Type)?;
        let name = self.expect_ident()?;

        // Type parameters (optional)
        let params = if self.check(TokenKind::LBracket) {
            self.advance();
            let mut params = Vec::new();
            loop {
                params.push(self.expect_ident()?);
                if !self.check(TokenKind::Comma) {
                    break;
                }
                self.advance();
            }
            self.expect(TokenKind::RBracket)?;
            params
        } else {
            Vec::new()
        };

        self.expect(TokenKind::Eq)?;

        let kind = if self.check(TokenKind::Struct) {
            self.advance();
            self.expect(TokenKind::LBrace)?;
            let fields = self.parse_fields(file)?;
            self.expect(TokenKind::RBrace)?;
            TypeDefKind::Struct(fields)
        } else if self.check(TokenKind::LBrace) {
            // Struct shorthand: type Foo = { ... } instead of type Foo = struct { ... }
            self.advance();
            let fields = self.parse_fields(file)?;
            self.expect(TokenKind::RBrace)?;
            TypeDefKind::Struct(fields)
        } else if self.check(TokenKind::Enum) {
            self.advance();
            self.expect(TokenKind::LBrace)?;
            let variants = self.parse_variants(file)?;
            self.expect(TokenKind::RBrace)?;
            TypeDefKind::Enum(variants)
        } else {
            let ty = self.parse_type(file)?;
            TypeDefKind::Alias(ty)
        };

        let span = start.merge(self.previous_span());

        Ok(TypeDef {
            span,
            name,
            params,
            kind,
        })
    }

    /// Parse struct fields.
    fn parse_fields(&mut self, file: &mut SourceFile) -> ParseResult<Vec<Field>> {
        let mut fields = Vec::new();

        while !self.check(TokenKind::RBrace) && !self.is_eof() {
            let start = self.peek().span;
            let name = self.expect_ident()?;
            self.expect(TokenKind::Colon)?;
            let ty = self.parse_type(file)?;

            fields.push(Field {
                span: start.merge(file.types[ty].span),
                name,
                ty,
            });

            if !self.check(TokenKind::Comma) {
                break;
            }
            self.advance();
        }

        Ok(fields)
    }

    /// Parse enum variants.
    fn parse_variants(&mut self, file: &mut SourceFile) -> ParseResult<Vec<Variant>> {
        let mut variants = Vec::new();

        while !self.check(TokenKind::RBrace) && !self.is_eof() {
            let start = self.peek().span;
            let name = self.expect_ident()?;

            let fields = if self.check(TokenKind::LParen) {
                self.advance();
                let mut types = Vec::new();
                loop {
                    types.push(self.parse_type(file)?);
                    if !self.check(TokenKind::Comma) {
                        break;
                    }
                    self.advance();
                }
                self.expect(TokenKind::RParen)?;
                Some(types)
            } else {
                None
            };

            variants.push(Variant {
                span: start.merge(self.previous_span()),
                name,
                fields,
            });

            if !self.check(TokenKind::Comma) {
                break;
            }
            self.advance();
        }

        Ok(variants)
    }

    /// Parse an import statement.
    fn parse_import(&mut self) -> ParseResult<Import> {
        let start = self.expect(TokenKind::Import)?;
        let mut path = vec![self.expect_ident()?];

        while self.check(TokenKind::ColonColon) || self.check(TokenKind::Dot) {
            self.advance();
            path.push(self.expect_ident()?);
        }

        let alias = if self.check_ident("as") {
            self.advance();
            Some(self.expect_ident()?)
        } else {
            None
        };

        let span = start.merge(self.previous_span());

        Ok(Import { span, path, alias })
    }

    /// Parse a const definition.
    fn parse_const(&mut self, file: &mut SourceFile) -> ParseResult<ConstDef> {
        let start = self.expect(TokenKind::Const)?;
        let name = self.expect_ident()?;

        let ty = if self.check(TokenKind::Colon) {
            self.advance();
            Some(self.parse_type(file)?)
        } else {
            None
        };

        self.expect(TokenKind::Eq)?;
        let value = self.parse_expr(file)?;

        let span = start.merge(self.previous_span());

        Ok(ConstDef {
            span,
            name,
            ty,
            value,
        })
    }

    /// Parse a type expression.
    fn parse_type(&mut self, file: &mut SourceFile) -> ParseResult<TypeId> {
        let start = self.peek().span;

        let kind = if self.check(TokenKind::Fn) {
            // Function type: fn(T, U) -> R
            self.advance();
            self.expect(TokenKind::LParen)?;

            let mut params = Vec::new();
            if !self.check(TokenKind::RParen) {
                loop {
                    params.push(self.parse_type(file)?);
                    if !self.check(TokenKind::Comma) {
                        break;
                    }
                    self.advance();
                }
            }
            self.expect(TokenKind::RParen)?;

            self.expect(TokenKind::Arrow)?;
            let ret = self.parse_type(file)?;

            TypeKind::Function { params, ret }
        } else if self.check(TokenKind::LParen) {
            // Tuple or function type
            self.advance();

            if self.check(TokenKind::RParen) {
                self.advance();
                // Unit type ()
                TypeKind::Tuple(Vec::new())
            } else {
                let mut types = vec![self.parse_type(file)?];

                while self.check(TokenKind::Comma) {
                    self.advance();
                    if self.check(TokenKind::RParen) {
                        break;
                    }
                    types.push(self.parse_type(file)?);
                }
                self.expect(TokenKind::RParen)?;

                if self.check(TokenKind::Arrow) {
                    self.advance();
                    let ret = self.parse_type(file)?;
                    TypeKind::Function { params: types, ret }
                } else if types.len() == 1 {
                    // Parenthesized type, unwrap
                    return Ok(types.pop().unwrap());
                } else {
                    TypeKind::Tuple(types)
                }
            }
        } else if self.check(TokenKind::LBracket) {
            // Array type
            self.advance();
            let elem = self.parse_type(file)?;

            let size = if self.check(TokenKind::Semi) {
                self.advance();
                if let TokenKind::Integer(n) = self.advance().kind {
                    Some(n as usize)
                } else {
                    None
                }
            } else {
                None
            };

            self.expect(TokenKind::RBracket)?;
            TypeKind::Array { elem, size }
        } else if self.check(TokenKind::Underscore) {
            self.advance();
            TypeKind::Infer
        } else {
            // Named type
            let name = self.expect_ident()?;

            // Generic type arguments: Foo<T, U> or Foo[T, U]
            let args = if self.check(TokenKind::LBracket) {
                self.advance();
                let mut args = Vec::new();
                loop {
                    args.push(self.parse_type(file)?);
                    if !self.check(TokenKind::Comma) {
                        break;
                    }
                    self.advance();
                }
                self.expect(TokenKind::RBracket)?;
                args
            } else if self.check(TokenKind::Lt) {
                // Support angle bracket syntax: Foo<T, U>
                self.advance();
                let mut args = Vec::new();
                loop {
                    args.push(self.parse_type(file)?);
                    if !self.check(TokenKind::Comma) {
                        break;
                    }
                    self.advance();
                }
                self.expect(TokenKind::Gt)?;
                args
            } else {
                Vec::new()
            };

            TypeKind::Named { name, args }
        };

        let span = start.merge(self.previous_span());
        let ty = Type { span, kind };
        Ok(file.types.alloc(ty))
    }

    // === Helper methods ===

    fn peek(&mut self) -> &Token {
        self.lexer.peek()
    }

    fn advance(&mut self) -> Token {
        self.lexer.next()
    }

    fn is_eof(&mut self) -> bool {
        self.lexer.is_eof()
    }

    fn check(&mut self, kind: TokenKind) -> bool {
        std::mem::discriminant(&self.peek().kind) == std::mem::discriminant(&kind)
    }

    fn check_ident(&mut self, name: &str) -> bool {
        matches!(&self.peek().kind, TokenKind::Ident(s) if s.as_str() == name)
    }

    fn expect(&mut self, kind: TokenKind) -> ParseResult<Span> {
        if self.check(kind.clone()) {
            Ok(self.advance().span)
        } else {
            Err(ParseError::expected_token(kind, self.peek().clone()))
        }
    }

    fn expect_one_of(&mut self, kinds: &[TokenKind]) -> ParseResult<Span> {
        for kind in kinds {
            if self.check(kind.clone()) {
                return Ok(self.advance().span);
            }
        }
        Err(ParseError::unexpected_token(
            self.peek().clone(),
            "one of expected tokens",
        ))
    }

    fn expect_ident(&mut self) -> ParseResult<SmolStr> {
        match self.advance().kind {
            TokenKind::Ident(s) => Ok(s),
            _ => Err(ParseError::expected_identifier(self.peek().clone())),
        }
    }

    fn previous_span(&self) -> Span {
        // This is a simplified version; in practice we'd track the previous token
        Span::dummy()
    }

    fn recover_to_item(&mut self) {
        while !self.is_eof() {
            match self.peek().kind {
                TokenKind::Adaptive
                | TokenKind::Def
                | TokenKind::Fn
                | TokenKind::Type
                | TokenKind::Import
                | TokenKind::Const => return,
                _ => {
                    self.advance();
                }
            }
        }
    }

    fn recover_to_stmt(&mut self) {
        while !self.is_eof() {
            match self.peek().kind {
                TokenKind::Let
                | TokenKind::Return
                | TokenKind::While
                | TokenKind::For
                | TokenKind::If
                | TokenKind::RBrace => return,
                TokenKind::Semi => {
                    self.advance();
                    return;
                }
                _ => {
                    self.advance();
                }
            }
        }
    }
}

/// Parse a source file.
pub fn parse(source: &str) -> (SourceFile, Vec<ParseError>) {
    let mut parser = Parser::new(source);
    parser.parse_file()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_function() {
        let source = r#"
            def add(x: Int, y: Int) -> Int {
                x + y
            }
        "#;

        let (file, errors) = parse(source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
        assert_eq!(file.items.len(), 1);
    }

    #[test]
    fn test_parse_adaptive_function() {
        let source = r#"
            adaptive def sort(arr: Array[Int]) -> Array[Int]
                @requires: energy < 100J
                @optimize: minimize energy
            {
                @solution "quick":
                    @when: true
                    @provides: energy: 50J
                {
                    quicksort(arr)
                }
            }
        "#;

        let (file, errors) = parse(source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
        assert_eq!(file.items.len(), 1);

        if let Item::AdaptiveFunction(af) = &file.items[0] {
            assert_eq!(af.name.as_str(), "sort");
            assert_eq!(af.solutions.len(), 1);
        } else {
            panic!("Expected adaptive function");
        }
    }
}
