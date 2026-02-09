// SPDX-License-Identifier: PMPL-1.0-or-later
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
#[allow(unused_imports)]
use eclexia_ast::{Visibility, TraitDecl, ImplBlock, ModuleDecl, EffectDecl, StaticDecl, ExternBlock};
use smol_str::SmolStr;

pub use error::{ParseError, ParseResult};

/// Parser for Eclexia source code.
pub struct Parser<'src> {
    lexer: Lexer<'src>,
    #[allow(dead_code)]
    source: &'src str,
    errors: Vec<ParseError>,
    /// Disable struct literal parsing in postfix position (for contexts where { starts a block)
    no_struct_literals: bool,
}

impl<'src> Parser<'src> {
    /// Create a new parser for the given source.
    pub fn new(source: &'src str) -> Self {
        Self {
            lexer: Lexer::new(source),
            source,
            errors: Vec::new(),
            no_struct_literals: false,
        }
    }

    /// Parse a complete source file.
    pub fn parse_file(&mut self) -> (SourceFile, Vec<ParseError>) {
        let mut file = SourceFile::new();

        while !self.is_eof() {
            match self.parse_item(&mut file) {
                Ok(item) => file.items.push(item),
                Err(e) => {
                    let error_span = e.span();
                    self.errors.push(e);
                    self.recover_to_item();
                    // Emit an error placeholder so downstream passes see
                    // a node for every span in the source
                    file.items.push(eclexia_ast::Item::Error(error_span));
                }
            }
        }

        (file, std::mem::take(&mut self.errors))
    }

    /// Parse a visibility modifier.
    fn parse_visibility(&mut self) -> Visibility {
        if self.check(TokenKind::Pub) {
            self.advance();
            // Check for pub(crate), pub(super), pub(self)
            if self.check(TokenKind::LParen) {
                self.advance();
                if self.check_ident("crate") {
                    self.advance();
                    let _ = self.expect(TokenKind::RParen);
                    Visibility::PubCrate
                } else if self.check(TokenKind::Super) {
                    self.advance();
                    let _ = self.expect(TokenKind::RParen);
                    Visibility::PubCrate // treat pub(super) as restricted
                } else if self.check(TokenKind::SelfLower) {
                    self.advance();
                    let _ = self.expect(TokenKind::RParen);
                    Visibility::Private // pub(self) = private
                } else {
                    // Malformed, treat as public
                    let _ = self.expect(TokenKind::RParen);
                    Visibility::Public
                }
            } else {
                Visibility::Public
            }
        } else {
            Visibility::Private
        }
    }

    /// Parse a single top-level item.
    fn parse_item(&mut self, file: &mut SourceFile) -> ParseResult<Item> {
        // Parse attributes (#[test], #[bench], etc.)
        let attributes = self.parse_attributes()?;

        // Parse visibility modifier
        let visibility = self.parse_visibility();

        let token = self.peek();

        match &token.kind {
            TokenKind::Adaptive => {
                let mut func = self.parse_adaptive_function(file)?;
                func.attributes = attributes;
                Ok(Item::AdaptiveFunction(func))
            }
            TokenKind::Def | TokenKind::Fn => {
                let mut func = self.parse_function(file)?;
                func.visibility = visibility;
                func.attributes = attributes;
                Ok(Item::Function(func))
            }
            TokenKind::Type => self.parse_type_def(file).map(Item::TypeDef),
            TokenKind::Struct => self.parse_struct_shorthand(file).map(Item::TypeDef),
            TokenKind::Import | TokenKind::Use => self.parse_import().map(Item::Import),
            TokenKind::Const => self.parse_const(file).map(Item::Const),
            TokenKind::Trait => self.parse_trait_decl(file).map(Item::TraitDecl),
            TokenKind::Impl => self.parse_impl_block(file).map(Item::ImplBlock),
            TokenKind::Module | TokenKind::Mod => self.parse_module_decl(file).map(Item::ModuleDecl),
            TokenKind::Effect => self.parse_effect_decl(file).map(Item::EffectDecl),
            TokenKind::Static => self.parse_static_decl(file).map(Item::StaticDecl),
            TokenKind::Extern => self.parse_extern_block(file).map(Item::ExternBlock),
            TokenKind::Macro => {
                let mut m = self.parse_macro_def()?;
                m.visibility = visibility;
                Ok(Item::MacroDef(m))
            }
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
                _ => return Err(ParseError::custom(token.span, "internal error: unexpected attribute token")),
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

        // Where clause
        let where_clause = self.parse_where_clause(file)?;

        // Body
        let body = self.parse_block(file)?;

        let span = start.merge(body.span);

        Ok(Function {
            span,
            visibility: Visibility::Private,
            name,
            type_params,
            params,
            return_type,
            constraints,
            attributes: vec![],
            where_clause,
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

        // Parse solutions - either @solution syntax or shorthand (name @requires...)
        loop {
            if self.check(TokenKind::AtSolution) {
                let solution = self.parse_solution(file)?;
                solutions.push(solution);
            } else if matches!(self.peek().kind, TokenKind::Ident(_)) {
                // Shorthand solution syntax
                let solution = self.parse_solution_shorthand(file)?;
                solutions.push(solution);
            } else {
                break;
            }
        }

        Ok(solutions)
    }

    /// Parse a shorthand solution: name @requires(...) { body }
    fn parse_solution_shorthand(&mut self, file: &mut SourceFile) -> ParseResult<Solution> {
        let start = self.peek().span;

        // Solution name
        let name = self.expect_ident()?;

        // @requires clause (convert to provides with negated resource)
        let mut provides = Vec::new();
        if self.check(TokenKind::AtRequires) {
            self.advance();
            self.expect(TokenKind::LParen)?;

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

            self.expect(TokenKind::RParen)?;
        }

        // Solution body
        let body = self.parse_block(file)?;
        let span = start.merge(body.span);

        Ok(Solution {
            span,
            name,
            when_clause: None,
            provides,
            body,
        })
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
                    let error_span = e.span();
                    self.errors.push(e);
                    self.recover_to_stmt();
                    // Emit an error placeholder statement so the block
                    // preserves structure for downstream passes
                    let error_stmt = eclexia_ast::Stmt {
                        span: error_span,
                        kind: eclexia_ast::StmtKind::Error,
                    };
                    let stmt_id = file.stmts.alloc(error_stmt);
                    stmts.push(stmt_id);
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
        let start = self.peek().span;
        let token_kind = self.peek().kind.clone();

        // Items inside blocks: def (always item), struct (always item)
        let kind = match &token_kind {
            TokenKind::Def => {
                // def is always a function definition
                let func = self.parse_function(file)?;
                let func_expr = file.exprs.alloc(Expr {
                    span: func.span,
                    kind: ExprKind::Literal(Literal::Unit),
                });
                return Ok(Stmt { span: func.span, kind: StmtKind::Expr(func_expr) });
            }
            TokenKind::Struct => {
                let typedef = self.parse_struct_shorthand(file)?;
                let unit_expr = file.exprs.alloc(Expr {
                    span: typedef.span,
                    kind: ExprKind::Literal(Literal::Unit),
                });
                return Ok(Stmt { span: typedef.span, kind: StmtKind::Expr(unit_expr) });
            }
            TokenKind::Let => {
                self.advance();

                // Optional 'mut' keyword
                let is_mut = if self.check(TokenKind::Mut) {
                    self.advance();
                    true
                } else {
                    false
                };

                // Parse pattern (supports destructuring)
                let pattern = self.parse_pattern()?;

                let ty = if self.check(TokenKind::Colon) {
                    self.advance();
                    Some(self.parse_type(file)?)
                } else {
                    None
                };

                self.expect(TokenKind::Eq)?;
                let value = self.parse_expr(file)?;

                StmtKind::Let { pattern, mutable: is_mut, ty, value }
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
                let pattern = self.parse_pattern()?;
                self.expect(TokenKind::In)?;
                // Parse iterator expression WITHOUT postfix struct literals
                // to avoid ambiguity with the for loop body block
                let iter = self.parse_expr_no_struct(file)?;
                let body = self.parse_block(file)?;
                StmtKind::For { pattern, iter, body }
            }
            TokenKind::Loop => {
                self.advance();
                // Optional label: loop 'name { ... }
                let label = if matches!(self.peek().kind, TokenKind::Ident(ref s) if s.starts_with('\'')) {
                    let s = self.expect_ident()?;
                    Some(s)
                } else {
                    None
                };
                let body = self.parse_block(file)?;
                StmtKind::Loop { label, body }
            }
            TokenKind::Break => {
                self.advance();
                // Optional label
                let label = if matches!(self.peek().kind, TokenKind::Ident(ref s) if s.starts_with('\'')) {
                    let s = self.expect_ident()?;
                    Some(s)
                } else {
                    None
                };
                // Optional value
                let value = if !self.check(TokenKind::Semi) && !self.check(TokenKind::RBrace) {
                    Some(self.parse_expr(file)?)
                } else {
                    None
                };
                StmtKind::Break { label, value }
            }
            TokenKind::Continue => {
                self.advance();
                // Optional label
                let label = if matches!(self.peek().kind, TokenKind::Ident(ref s) if s.starts_with('\'')) {
                    let s = self.expect_ident()?;
                    Some(s)
                } else {
                    None
                };
                StmtKind::Continue { label }
            }
            TokenKind::Ident(_) => {
                // Could be assignment (x = y, x.f = y, a[i] = y) or expression statement
                // Parse as expression first
                let expr = self.parse_expr(file)?;

                // Check if followed by = (assignment) or compound assignment
                if self.check(TokenKind::Eq) {
                    self.advance(); // consume =
                    let value = self.parse_expr(file)?;
                    StmtKind::Assign { target: expr, value }
                } else if self.check(TokenKind::PlusEq) || self.check(TokenKind::MinusEq)
                    || self.check(TokenKind::StarEq) || self.check(TokenKind::SlashEq)
                    || self.check(TokenKind::PercentEq) || self.check(TokenKind::CaretEq)
                    || self.check(TokenKind::AmpEq) || self.check(TokenKind::PipeEq)
                    || self.check(TokenKind::LtLtEq) || self.check(TokenKind::GtGtEq)
                    || self.check(TokenKind::StarStarEq)
                {
                    // Compound assignment: desugar x += y to x = x + y
                    let op_token = self.advance();
                    let op = match op_token.kind {
                        TokenKind::PlusEq => BinaryOp::Add,
                        TokenKind::MinusEq => BinaryOp::Sub,
                        TokenKind::StarEq => BinaryOp::Mul,
                        TokenKind::SlashEq => BinaryOp::Div,
                        TokenKind::PercentEq => BinaryOp::Rem,
                        TokenKind::CaretEq => BinaryOp::BitXor,
                        TokenKind::AmpEq => BinaryOp::BitAnd,
                        TokenKind::PipeEq => BinaryOp::BitOr,
                        TokenKind::LtLtEq => BinaryOp::Shl,
                        TokenKind::GtGtEq => BinaryOp::Shr,
                        TokenKind::StarStarEq => BinaryOp::Pow,
                        _ => return Err(ParseError::custom(op_token.span, "internal error: unexpected compound assignment operator")),
                    };
                    let rhs = self.parse_expr(file)?;
                    let bin_expr = file.exprs.alloc(Expr {
                        span: file.exprs[expr].span.merge(file.exprs[rhs].span),
                        kind: ExprKind::Binary { op, lhs: expr, rhs },
                    });
                    StmtKind::Assign { target: expr, value: bin_expr }
                } else {
                    // Regular expression statement
                    StmtKind::Expr(expr)
                }
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

    /// Parse struct shorthand: `struct Name { fields }`
    fn parse_struct_shorthand(&mut self, file: &mut SourceFile) -> ParseResult<TypeDef> {
        let start = self.expect(TokenKind::Struct)?;
        let name = self.expect_ident()?;

        // Type parameters (optional): struct Foo<T, U> { ... }
        let params = if self.check(TokenKind::Lt) {
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

        self.expect(TokenKind::LBrace)?;
        let fields = self.parse_fields(file)?;
        self.expect(TokenKind::RBrace)?;

        let span = start.merge(self.previous_span());

        Ok(TypeDef {
            span,
            name,
            params,
            kind: TypeDefKind::Struct(fields),
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

    /// Parse enum variants (supports unit, tuple, and struct variants).
    fn parse_variants(&mut self, file: &mut SourceFile) -> ParseResult<Vec<Variant>> {
        let mut variants = Vec::new();

        while !self.check(TokenKind::RBrace) && !self.is_eof() {
            let start = self.peek().span;
            let name = self.expect_ident()?;

            let fields = if self.check(TokenKind::LParen) {
                // Tuple variant: Variant(T1, T2)
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
            } else if self.check(TokenKind::LBrace) {
                // Struct variant: Variant { field: T }
                // Desugar to anonymous tuple of field types
                self.advance();
                let struct_fields = self.parse_fields(file)?;
                self.expect(TokenKind::RBrace)?;
                Some(struct_fields.iter().map(|f| f.ty).collect())
            } else {
                // Unit variant
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

    /// Parse an import/use statement.
    /// Supports: `import foo::bar`, `use foo::bar`, `use foo::{a, b}`, `use foo::*`
    fn parse_import(&mut self) -> ParseResult<Import> {
        let start = self.expect_one_of(&[TokenKind::Import, TokenKind::Use])?;
        let mut path = vec![self.expect_ident()?];

        while self.check(TokenKind::ColonColon) || self.check(TokenKind::Dot) {
            self.advance();

            // Check for glob: use foo::*
            if self.check(TokenKind::Star) {
                self.advance();
                path.push(SmolStr::new("*"));
                break;
            }

            // Check for tree: use foo::{a, b}
            if self.check(TokenKind::LBrace) {
                self.advance();
                // Parse each item in the tree as a separate import
                // For now, flatten to the first item (full use-tree support
                // would need an AST change)
                let mut names = Vec::new();
                if !self.check(TokenKind::RBrace) {
                    loop {
                        names.push(self.expect_ident()?);
                        if !self.check(TokenKind::Comma) { break; }
                        self.advance();
                    }
                }
                self.expect(TokenKind::RBrace)?;
                // Store as path with {items} joined
                for name in names {
                    path.push(name);
                }
                break;
            }

            // Check for self keyword
            if self.check(TokenKind::SelfLower) {
                self.advance();
                path.push(SmolStr::new("self"));
            } else if self.check(TokenKind::Super) {
                self.advance();
                path.push(SmolStr::new("super"));
            } else {
                path.push(self.expect_ident()?);
            }
        }

        let alias = if self.check_ident("as") {
            self.advance();
            Some(self.expect_ident()?)
        } else {
            None
        };

        // Optional semicolon
        if self.check(TokenKind::Semi) {
            self.advance();
        }

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

        // Optional semicolon
        if self.check(TokenKind::Semi) {
            self.advance();
        }

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

        let kind = if self.check(TokenKind::Amp) {
            // Reference type: &T or &mut T
            self.advance();
            let mutable = if self.check(TokenKind::Mut) {
                self.advance();
                true
            } else {
                false
            };
            let ty = self.parse_type(file)?;
            TypeKind::Reference { ty, mutable }
        } else if self.check(TokenKind::Fn) {
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
                    // Parenthesized type - safe: len == 1 verified above
                    return Ok(types.into_iter().next().expect("len checked"));
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
        let mut ty_id = file.types.alloc(ty);

        // Optional type postfix: T?
        if self.check(TokenKind::Question) {
            self.advance();
            let opt_span = start.merge(self.previous_span());
            let opt_ty = Type { span: opt_span, kind: TypeKind::Optional(ty_id) };
            ty_id = file.types.alloc(opt_ty);
        }

        Ok(ty_id)
    }

    /// Parse a trait bound: TraitName or TraitName<T, U>
    fn parse_trait_bound(&mut self, file: &mut SourceFile) -> ParseResult<TraitBound> {
        let start = self.peek().span;
        // Parse path: Name or Name::Other
        let mut path = vec![self.expect_ident()?];
        while self.check(TokenKind::ColonColon) {
            self.advance();
            path.push(self.expect_ident()?);
        }
        let type_args = if self.check(TokenKind::Lt) {
            self.advance();
            let mut args = Vec::new();
            loop {
                args.push(self.parse_type(file)?);
                if !self.check(TokenKind::Comma) { break; }
                self.advance();
            }
            self.expect(TokenKind::Gt)?;
            args
        } else {
            Vec::new()
        };
        Ok(TraitBound {
            span: start.merge(self.previous_span()),
            path,
            type_args,
        })
    }

    /// Parse trait bounds separated by +
    fn parse_trait_bounds(&mut self, file: &mut SourceFile) -> ParseResult<Vec<TraitBound>> {
        let mut bounds = Vec::new();
        loop {
            bounds.push(self.parse_trait_bound(file)?);
            if !self.check(TokenKind::Plus) { break; }
            self.advance();
        }
        Ok(bounds)
    }

    /// Parse a where clause: where T: Trait, U: Trait + OtherTrait
    fn parse_where_clause(&mut self, file: &mut SourceFile) -> ParseResult<Vec<WherePredicate>> {
        if !self.check(TokenKind::Where) {
            return Ok(Vec::new());
        }
        self.advance();

        let mut predicates = Vec::new();
        loop {
            let start = self.peek().span;
            let ty = self.parse_type(file)?;
            self.expect(TokenKind::Colon)?;
            let bounds = self.parse_trait_bounds(file)?;

            predicates.push(WherePredicate {
                span: start.merge(self.previous_span()),
                ty,
                bounds,
            });

            if !self.check(TokenKind::Comma) { break; }
            self.advance();
            if self.check(TokenKind::LBrace) || self.is_eof() { break; }
        }

        Ok(predicates)
    }

    /// Parse a trait declaration.
    fn parse_trait_decl(&mut self, file: &mut SourceFile) -> ParseResult<TraitDecl> {
        let start = self.expect(TokenKind::Trait)?;
        let name = self.expect_ident()?;
        let type_params = self.parse_type_param_list_full(file)?;

        // Supertraits
        let super_traits = if self.check(TokenKind::Colon) {
            self.advance();
            self.parse_trait_bounds(file)?
        } else {
            Vec::new()
        };

        let where_clause = self.parse_where_clause(file)?;

        self.expect(TokenKind::LBrace)?;
        let mut items = Vec::new();
        while !self.check(TokenKind::RBrace) && !self.is_eof() {
            if self.check(TokenKind::Type) {
                let assoc_start = self.peek().span;
                self.advance();
                let assoc_name = self.expect_ident()?;
                let bounds = if self.check(TokenKind::Colon) {
                    self.advance();
                    self.parse_trait_bounds(file)?
                } else {
                    Vec::new()
                };
                let default = if self.check(TokenKind::Eq) {
                    self.advance();
                    Some(self.parse_type(file)?)
                } else {
                    None
                };
                if self.check(TokenKind::Semi) { self.advance(); }
                items.push(TraitItem::AssocType {
                    span: assoc_start.merge(self.previous_span()),
                    name: assoc_name,
                    bounds,
                    default,
                });
            } else if self.check(TokenKind::Def) || self.check(TokenKind::Fn) {
                let func = self.parse_function(file)?;
                let sig = FunctionSig {
                    span: func.span,
                    name: func.name,
                    type_params: func.type_params.iter().map(|n| TypeParam {
                        span: func.span,
                        name: n.clone(),
                        bounds: Vec::new(),
                    }).collect(),
                    params: func.params,
                    return_type: func.return_type,
                    where_clause: func.where_clause,
                };
                let body = if func.body.stmts.is_empty() && func.body.expr.is_none() {
                    None
                } else {
                    Some(func.body)
                };
                items.push(TraitItem::Method {
                    sig,
                    body,
                    attributes: func.attributes,
                });
            } else {
                self.advance();
            }
        }
        let end = self.expect(TokenKind::RBrace)?;

        Ok(TraitDecl {
            span: start.merge(end),
            visibility: Visibility::Private,
            name,
            type_params: type_params.iter().map(|n| TypeParam {
                span: start,
                name: n.clone(),
                bounds: Vec::new(),
            }).collect(),
            super_traits,
            where_clause,
            items,
        })
    }

    /// Parse an impl block.
    fn parse_impl_block(&mut self, file: &mut SourceFile) -> ParseResult<ImplBlock> {
        let start = self.expect(TokenKind::Impl)?;
        let type_params = self.parse_type_param_list_full(file)?;

        let first_ty = self.parse_type(file)?;

        let (trait_path, self_ty) = if self.check(TokenKind::For) {
            self.advance();
            let self_type = self.parse_type(file)?;
            // Extract trait path from the type
            let t_path = match &file.types[first_ty].kind {
                TypeKind::Named { name, .. } => Some(vec![name.clone()]),
                _ => None,
            };
            (t_path, self_type)
        } else {
            (None, first_ty)
        };

        let where_clause = self.parse_where_clause(file)?;

        self.expect(TokenKind::LBrace)?;
        let mut items = Vec::new();
        while !self.check(TokenKind::RBrace) && !self.is_eof() {
            let vis = self.parse_visibility();
            if self.check(TokenKind::Type) {
                let assoc_start = self.peek().span;
                self.advance();
                let assoc_name = self.expect_ident()?;
                self.expect(TokenKind::Eq)?;
                let ty = self.parse_type(file)?;
                if self.check(TokenKind::Semi) { self.advance(); }
                items.push(ImplItem::AssocType {
                    span: assoc_start.merge(self.previous_span()),
                    name: assoc_name,
                    ty,
                });
            } else if self.check(TokenKind::Def) || self.check(TokenKind::Fn) {
                let func = self.parse_function(file)?;
                let sig = FunctionSig {
                    span: func.span,
                    name: func.name,
                    type_params: func.type_params.iter().map(|n| TypeParam {
                        span: func.span,
                        name: n.clone(),
                        bounds: Vec::new(),
                    }).collect(),
                    params: func.params,
                    return_type: func.return_type,
                    where_clause: func.where_clause,
                };
                items.push(ImplItem::Method {
                    visibility: vis,
                    sig,
                    body: func.body,
                    attributes: func.attributes,
                });
            } else {
                self.advance();
            }
        }
        let end = self.expect(TokenKind::RBrace)?;

        Ok(ImplBlock {
            span: start.merge(end),
            type_params: type_params.iter().map(|n| TypeParam {
                span: start,
                name: n.clone(),
                bounds: Vec::new(),
            }).collect(),
            trait_path,
            self_ty,
            where_clause,
            items,
        })
    }

    /// Parse a module declaration.
    fn parse_module_decl(&mut self, file: &mut SourceFile) -> ParseResult<ModuleDecl> {
        let start = self.expect_one_of(&[TokenKind::Module, TokenKind::Mod])?;
        let name = self.expect_ident()?;

        self.expect(TokenKind::LBrace)?;
        let mut items = Vec::new();
        while !self.check(TokenKind::RBrace) && !self.is_eof() {
            match self.parse_item(file) {
                Ok(item) => items.push(item),
                Err(e) => {
                    self.errors.push(e);
                    self.recover_to_item();
                }
            }
        }
        let end = self.expect(TokenKind::RBrace)?;

        Ok(ModuleDecl {
            span: start.merge(end),
            visibility: Visibility::Private,
            name,
            items: Some(items),
        })
    }

    /// Parse an effect declaration.
    fn parse_effect_decl(&mut self, file: &mut SourceFile) -> ParseResult<EffectDecl> {
        let start = self.expect(TokenKind::Effect)?;
        let name = self.expect_ident()?;
        let type_params_idents = self.parse_type_param_list_full(file)?;

        self.expect(TokenKind::LBrace)?;
        let mut operations = Vec::new();
        while !self.check(TokenKind::RBrace) && !self.is_eof() {
            let op_start = self.peek().span;
            if self.check(TokenKind::Def) || self.check(TokenKind::Fn) {
                self.advance();
            }
            let op_name = self.expect_ident()?;
            self.expect(TokenKind::LParen)?;
            let params = self.parse_params(file)?;
            self.expect(TokenKind::RParen)?;
            let ret_ty = if self.check(TokenKind::Arrow) {
                self.advance();
                Some(self.parse_type(file)?)
            } else {
                None
            };
            if self.check(TokenKind::Semi) { self.advance(); }
            operations.push(EffectOp {
                span: op_start.merge(self.previous_span()),
                name: op_name,
                params,
                return_type: ret_ty,
            });
        }
        let end = self.expect(TokenKind::RBrace)?;

        Ok(EffectDecl {
            span: start.merge(end),
            visibility: Visibility::Private,
            name,
            type_params: type_params_idents.iter().map(|n| TypeParam {
                span: start,
                name: n.clone(),
                bounds: Vec::new(),
            }).collect(),
            operations,
        })
    }

    /// Parse a static declaration.
    fn parse_static_decl(&mut self, file: &mut SourceFile) -> ParseResult<StaticDecl> {
        let start = self.expect(TokenKind::Static)?;
        let mutable = if self.check(TokenKind::Mut) {
            self.advance();
            true
        } else {
            false
        };
        let name = self.expect_ident()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_type(file)?;
        self.expect(TokenKind::Eq)?;
        let value = self.parse_expr(file)?;
        if self.check(TokenKind::Semi) { self.advance(); }

        Ok(StaticDecl {
            span: start.merge(self.previous_span()),
            visibility: Visibility::Private,
            mutable,
            name,
            ty,
            value,
        })
    }

    /// Parse an extern block.
    fn parse_extern_block(&mut self, file: &mut SourceFile) -> ParseResult<ExternBlock> {
        let start = self.expect(TokenKind::Extern)?;

        let abi = if matches!(self.peek().kind, TokenKind::String(_)) {
            let tok = self.advance();
            let s = match tok.kind {
                TokenKind::String(s) => s,
                _ => return Err(ParseError::custom(tok.span, "internal error: expected string for extern ABI")),
            };
            Some(s)
        } else {
            None
        };

        self.expect(TokenKind::LBrace)?;
        let mut items = Vec::new();
        while !self.check(TokenKind::RBrace) && !self.is_eof() {
            if self.check(TokenKind::Def) || self.check(TokenKind::Fn) {
                let fn_start = self.peek().span;
                self.advance();
                let fn_name = self.expect_ident()?;
                self.expect(TokenKind::LParen)?;
                let params = self.parse_params(file)?;
                self.expect(TokenKind::RParen)?;
                let ret_ty = if self.check(TokenKind::Arrow) {
                    self.advance();
                    Some(self.parse_type(file)?)
                } else {
                    None
                };
                if self.check(TokenKind::Semi) { self.advance(); }
                items.push(ExternItem::Fn(FunctionSig {
                    span: fn_start.merge(self.previous_span()),
                    name: fn_name,
                    type_params: Vec::new(),
                    params,
                    return_type: ret_ty,
                    where_clause: Vec::new(),
                }));
            } else if self.check(TokenKind::Static) {
                let static_start = self.peek().span;
                self.advance();
                let mutable = if self.check(TokenKind::Mut) { self.advance(); true } else { false };
                let item_name = self.expect_ident()?;
                self.expect(TokenKind::Colon)?;
                let ty = self.parse_type(file)?;
                if self.check(TokenKind::Semi) { self.advance(); }
                items.push(ExternItem::Static {
                    span: static_start.merge(self.previous_span()),
                    mutable,
                    name: item_name,
                    ty,
                });
            } else {
                self.advance();
            }
        }
        let end = self.expect(TokenKind::RBrace)?;

        Ok(ExternBlock {
            span: start.merge(end),
            abi,
            items,
        })
    }

    /// Parse a macro definition.
    ///
    /// Syntax: `macro name { (pattern) => { template }, ... }`
    ///
    /// Pattern tokens: literals, `$name:kind` metavariables, `$(...)*` repetitions.
    /// Template tokens: literals, `$name` metavariable references.
    fn parse_macro_def(&mut self) -> ParseResult<MacroDef> {
        let start = self.expect(TokenKind::Macro)?;
        let name = self.expect_ident()?;

        self.expect(TokenKind::LBrace)?;

        let mut rules = Vec::new();
        while !self.check(TokenKind::RBrace) && !self.is_eof() {
            let rule = self.parse_macro_rule()?;
            rules.push(rule);

            // Optional comma/semicolon between rules
            if self.check(TokenKind::Comma) || self.check(TokenKind::Semi) {
                self.advance();
            }
        }

        let end = self.expect(TokenKind::RBrace)?;

        Ok(MacroDef {
            span: start.merge(end),
            visibility: Visibility::Private, // overridden by caller
            name,
            rules,
        })
    }

    /// Parse a single macro rule: `(pattern) => { template }` or `(pattern) => template`
    fn parse_macro_rule(&mut self) -> ParseResult<MacroRule> {
        let start = self.peek().span;

        // Parse pattern (wrapped in parens or brackets)
        self.expect(TokenKind::LParen)?;
        let pattern = self.parse_macro_tokens(TokenKind::RParen)?;
        self.expect(TokenKind::RParen)?;

        // Arrow separator
        self.expect(TokenKind::FatArrow)?;

        // Parse template (wrapped in braces, parens, or brackets)
        let template = if self.check(TokenKind::LBrace) {
            self.advance();
            let t = self.parse_macro_tokens(TokenKind::RBrace)?;
            self.expect(TokenKind::RBrace)?;
            t
        } else if self.check(TokenKind::LParen) {
            self.advance();
            let t = self.parse_macro_tokens(TokenKind::RParen)?;
            self.expect(TokenKind::RParen)?;
            t
        } else if self.check(TokenKind::LBracket) {
            self.advance();
            let t = self.parse_macro_tokens(TokenKind::RBracket)?;
            self.expect(TokenKind::RBracket)?;
            t
        } else {
            return Err(ParseError::custom(self.peek().span, "expected { or ( after => in macro rule"));
        };

        let span = start.merge(self.previous_span());
        Ok(MacroRule { span, pattern, template })
    }

    /// Parse macro tokens (pattern or template) until a closing delimiter.
    fn parse_macro_tokens(&mut self, closing: TokenKind) -> ParseResult<Vec<MacroToken>> {
        let mut tokens = Vec::new();
        let mut brace_depth: u32 = 0;
        let mut paren_depth: u32 = 0;
        let mut bracket_depth: u32 = 0;

        while !self.is_eof() {
            // Only stop at closing token when all nesting is balanced
            if self.check_discriminant(&closing) && brace_depth == 0 && paren_depth == 0 && bracket_depth == 0 {
                break;
            }
            if self.check(TokenKind::Dollar) {
                self.advance();

                if self.check(TokenKind::LParen) {
                    // Repetition: $(...)*  $(...)+  $(...)?
                    self.advance();
                    let inner = self.parse_macro_tokens(TokenKind::RParen)?;
                    self.expect(TokenKind::RParen)?;

                    // Optional separator before repetition kind
                    let separator = if self.check(TokenKind::Comma) {
                        self.advance();
                        Some(SmolStr::new(","))
                    } else {
                        None
                    };

                    let kind = if self.check(TokenKind::Star) {
                        self.advance();
                        RepetitionKind::ZeroOrMore
                    } else if self.check(TokenKind::Plus) {
                        self.advance();
                        RepetitionKind::OneOrMore
                    } else if self.check(TokenKind::Question) {
                        self.advance();
                        RepetitionKind::Optional
                    } else {
                        // Default to zero-or-more
                        RepetitionKind::ZeroOrMore
                    };

                    tokens.push(MacroToken::Repetition {
                        tokens: inner,
                        separator,
                        kind,
                    });
                } else if matches!(self.peek().kind, TokenKind::Ident(_)) {
                    // Metavariable: $name or $name:kind
                    let name = self.expect_ident()?;

                    let kind = if self.check(TokenKind::Colon) {
                        self.advance();
                        let kind_name = self.expect_ident()?;
                        match kind_name.as_str() {
                            "expr" => MacroVarKind::Expr,
                            "stmt" => MacroVarKind::Stmt,
                            "ty" => MacroVarKind::Ty,
                            "pat" => MacroVarKind::Pat,
                            "ident" => MacroVarKind::Ident,
                            "block" => MacroVarKind::Block,
                            "literal" => MacroVarKind::Literal,
                            "tt" => MacroVarKind::Tt,
                            _ => {
                                return Err(ParseError::custom(
                                    self.previous_span(),
                                    format!("unknown macro variable kind '{}', expected one of: expr, stmt, ty, pat, ident, block, literal, tt", kind_name),
                                ));
                            }
                        }
                    } else {
                        // In template position, $name without :kind references a bound metavar
                        MacroVarKind::Tt
                    };

                    tokens.push(MacroToken::MetaVar { name, kind });
                } else {
                    // Lone $ - treat as literal
                    tokens.push(MacroToken::Literal(SmolStr::new("$")));
                }
            } else {
                // Track nesting depth for balanced delimiters
                if self.check(TokenKind::LBrace) { brace_depth += 1; }
                else if self.check(TokenKind::RBrace) && brace_depth > 0 { brace_depth -= 1; }
                else if self.check(TokenKind::LParen) { paren_depth += 1; }
                else if self.check(TokenKind::RParen) && paren_depth > 0 { paren_depth -= 1; }
                else if self.check(TokenKind::LBracket) { bracket_depth += 1; }
                else if self.check(TokenKind::RBracket) && bracket_depth > 0 { bracket_depth -= 1; }
                // Literal token - capture its text
                let tok = self.advance();
                let text = match &tok.kind {
                    TokenKind::Ident(s) => s.clone(),
                    TokenKind::Integer(n) => SmolStr::new(&n.to_string()),
                    TokenKind::Float(f) => SmolStr::new(&f.to_string()),
                    TokenKind::String(s) => SmolStr::new(&format!("\"{}\"", s)),
                    TokenKind::Plus => SmolStr::new("+"),
                    TokenKind::Minus => SmolStr::new("-"),
                    TokenKind::Star => SmolStr::new("*"),
                    TokenKind::Slash => SmolStr::new("/"),
                    TokenKind::Percent => SmolStr::new("%"),
                    TokenKind::Eq => SmolStr::new("="),
                    TokenKind::EqEq => SmolStr::new("=="),
                    TokenKind::BangEq => SmolStr::new("!="),
                    TokenKind::Lt => SmolStr::new("<"),
                    TokenKind::Gt => SmolStr::new(">"),
                    TokenKind::Le => SmolStr::new("<="),
                    TokenKind::Ge => SmolStr::new(">="),
                    TokenKind::And => SmolStr::new("&&"),
                    TokenKind::Or => SmolStr::new("||"),
                    TokenKind::Bang => SmolStr::new("!"),
                    TokenKind::LParen => SmolStr::new("("),
                    TokenKind::RParen => SmolStr::new(")"),
                    TokenKind::LBrace => SmolStr::new("{"),
                    TokenKind::RBrace => SmolStr::new("}"),
                    TokenKind::LBracket => SmolStr::new("["),
                    TokenKind::RBracket => SmolStr::new("]"),
                    TokenKind::Comma => SmolStr::new(","),
                    TokenKind::Colon => SmolStr::new(":"),
                    TokenKind::Semi => SmolStr::new(";"),
                    TokenKind::Arrow => SmolStr::new("->"),
                    TokenKind::FatArrow => SmolStr::new("=>"),
                    TokenKind::Dot => SmolStr::new("."),
                    TokenKind::DotDot => SmolStr::new(".."),
                    TokenKind::Pipe => SmolStr::new("|"),
                    // Keywords
                    TokenKind::If => SmolStr::new("if"),
                    TokenKind::Else => SmolStr::new("else"),
                    TokenKind::Let => SmolStr::new("let"),
                    TokenKind::Def => SmolStr::new("def"),
                    TokenKind::Fn => SmolStr::new("fn"),
                    TokenKind::Return => SmolStr::new("return"),
                    TokenKind::While => SmolStr::new("while"),
                    TokenKind::For => SmolStr::new("for"),
                    TokenKind::In => SmolStr::new("in"),
                    TokenKind::Match => SmolStr::new("match"),
                    TokenKind::Struct => SmolStr::new("struct"),
                    TokenKind::Trait => SmolStr::new("trait"),
                    TokenKind::Impl => SmolStr::new("impl"),
                    TokenKind::Pub => SmolStr::new("pub"),
                    TokenKind::True => SmolStr::new("true"),
                    TokenKind::False => SmolStr::new("false"),
                    TokenKind::Mut => SmolStr::new("mut"),
                    TokenKind::As => SmolStr::new("as"),
                    TokenKind::Break => SmolStr::new("break"),
                    TokenKind::Continue => SmolStr::new("continue"),
                    TokenKind::Loop => SmolStr::new("loop"),
                    TokenKind::Type => SmolStr::new("type"),
                    TokenKind::Enum => SmolStr::new("enum"),
                    TokenKind::Use => SmolStr::new("use"),
                    TokenKind::Adaptive => SmolStr::new("adaptive"),
                    TokenKind::Macro => SmolStr::new("macro"),
                    _ => SmolStr::new(&format!("{:?}", tok.kind)),
                };
                tokens.push(MacroToken::Literal(text));
            }
        }

        Ok(tokens)
    }

    /// Check if peek token has the same discriminant as the given token kind.
    fn check_discriminant(&mut self, expected: &TokenKind) -> bool {
        std::mem::discriminant(&self.peek().kind) == std::mem::discriminant(expected)
    }

    /// Parse a type parameter list: <T, U: Trait, V = Default> (returns simple Ident vec)
    /// Bounds and defaults are consumed but not returned in the Ident vec
    /// (callers that need full TypeParam info use parse_type_params_full_structured)
    fn parse_type_param_list_full(&mut self, file: &mut SourceFile) -> ParseResult<Vec<Ident>> {
        if self.check(TokenKind::Lt) {
            self.advance();
            let mut params = Vec::new();
            loop {
                params.push(self.expect_ident()?);
                // Consume optional bounds: T: Trait1 + Trait2
                if self.check(TokenKind::Colon) {
                    self.advance();
                    // Parse bounds (trait names separated by +)
                    let _ = self.parse_trait_bounds(file)?;
                }
                // Consume optional default: T = DefaultType
                if self.check(TokenKind::Eq) {
                    self.advance();
                    let _ = self.parse_type(file)?;
                }
                if !self.check(TokenKind::Comma) {
                    break;
                }
                self.advance();
            }
            self.expect(TokenKind::Gt)?;
            Ok(params)
        } else {
            Ok(Vec::new())
        }
    }

    /// Parse type parameters with full TypeParam info including bounds
    #[allow(dead_code)]
    fn parse_type_params_structured(&mut self, file: &mut SourceFile) -> ParseResult<Vec<TypeParam>> {
        if self.check(TokenKind::Lt) {
            self.advance();
            let mut params = Vec::new();
            loop {
                let start = self.peek().span;
                let name = self.expect_ident()?;
                let bounds = if self.check(TokenKind::Colon) {
                    self.advance();
                    self.parse_trait_bounds(file)?
                } else {
                    Vec::new()
                };
                // Skip defaults for now
                if self.check(TokenKind::Eq) {
                    self.advance();
                    let _ = self.parse_type(file)?;
                }
                params.push(TypeParam {
                    span: start.merge(self.previous_span()),
                    name,
                    bounds,
                });
                if !self.check(TokenKind::Comma) {
                    break;
                }
                self.advance();
            }
            self.expect(TokenKind::Gt)?;
            Ok(params)
        } else {
            Ok(Vec::new())
        }
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
        let token = self.advance();
        match token.kind {
            TokenKind::Ident(s) => Ok(s),
            // Accept contextual keywords as identifiers
            TokenKind::Energy => Ok(SmolStr::new("energy")),
            TokenKind::Latency => Ok(SmolStr::new("latency")),
            TokenKind::Memory => Ok(SmolStr::new("memory")),
            TokenKind::Carbon => Ok(SmolStr::new("carbon")),
            TokenKind::Unit => Ok(SmolStr::new("unit")),
            TokenKind::Case => Ok(SmolStr::new("case")),
            TokenKind::Do => Ok(SmolStr::new("do")),
            TokenKind::Super => Ok(SmolStr::new("super")),
            TokenKind::SelfLower => Ok(SmolStr::new("self")),
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
                | TokenKind::Const
                | TokenKind::Pub
                | TokenKind::Trait
                | TokenKind::Impl
                | TokenKind::Module
                | TokenKind::Mod
                | TokenKind::Effect
                | TokenKind::Use
                | TokenKind::Static
                | TokenKind::Extern
                | TokenKind::Struct
                | TokenKind::Enum
                | TokenKind::Hash
                | TokenKind::AtRequires
                | TokenKind::AtProvides => return,
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
                | TokenKind::Loop
                | TokenKind::Break
                | TokenKind::Continue
                | TokenKind::Match
                | TokenKind::Def
                | TokenKind::Fn
                | TokenKind::Struct
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

    /// Skip tokens until we reach a matching closing delimiter.
    /// Tracks nesting depth to handle nested delimiters correctly.
    /// Returns the span of the closing delimiter, or a dummy span on EOF.
    fn recover_to_closing_delimiter(&mut self, close: TokenKind) -> Span {
        let mut depth = 0u32;
        while !self.is_eof() {
            let kind = self.peek().kind.clone();

            // Track nesting: opening delimiters increase depth
            match &kind {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => {
                    depth += 1;
                    self.advance();
                }
                _ if std::mem::discriminant(&kind) == std::mem::discriminant(&close) => {
                    if depth == 0 {
                        let span = self.advance().span;
                        return span;
                    }
                    depth -= 1;
                    self.advance();
                }
                _ => {
                    self.advance();
                }
            }
        }
        Span::dummy()
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

    #[test]
    fn test_recovery_multiple_items_after_error() {
        // First function has a syntax error, second should still parse
        let source = r#"
            def bad( {
                oops
            }

            def good(x: Int) -> Int {
                x + 1
            }
        "#;

        let (file, errors) = parse(source);
        // Should have at least one error from the bad function
        assert!(!errors.is_empty(), "Expected errors from bad function");
        // Should have recovered and found the second good function
        let func_count = file.items.iter().filter(|i| matches!(i, Item::Function(_))).count();
        assert!(func_count >= 1, "Expected at least one parsed function after recovery, got {}", func_count);
    }

    #[test]
    fn test_recovery_statement_level() {
        // A block with a bad statement followed by a good one
        let source = r#"
            def foo() -> Int {
                let x = @@@;
                let y = 42;
                y
            }
        "#;

        let (file, errors) = parse(source);
        assert!(!errors.is_empty(), "Expected errors from bad statement");
        // The function should still be parsed
        assert_eq!(file.items.len(), 1);
    }

    #[test]
    fn test_recovery_item_error_nodes() {
        // Error items should create Item::Error nodes
        let source = r#"
            @@@ garbage

            def good() -> Int { 42 }
        "#;

        let (file, errors) = parse(source);
        assert!(!errors.is_empty());
        // Should have an error item and then the good function
        let has_error = file.items.iter().any(|i| matches!(i, Item::Error(_)));
        let has_function = file.items.iter().any(|i| matches!(i, Item::Function(_)));
        assert!(has_error, "Expected an error item node");
        assert!(has_function, "Expected the good function to be parsed");
    }
}
