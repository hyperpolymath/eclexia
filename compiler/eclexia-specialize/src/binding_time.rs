// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Binding-time analysis for partial evaluation.
//!
//! Determines which MIR values are statically known (compile-time)
//! versus dynamically determined (runtime). This drives specialization:
//! if all inputs to an adaptive function's constraints are static,
//! we can select the optimal solution at compile time.

use rustc_hash::FxHashMap;

use eclexia_mir::{ConstantKind, InstructionKind, MirFile, Value};

use crate::BindingTime;

/// Binding-time environment for a function.
#[derive(Debug, Clone)]
pub struct BindingTimeEnv {
    /// Binding time of each local variable.
    pub locals: FxHashMap<u32, BindingTime>,
    /// Binding time of each parameter (by index).
    pub params: Vec<BindingTime>,
}

impl BindingTimeEnv {
    /// Create a new environment where all parameters are dynamic.
    pub fn all_dynamic(param_count: usize) -> Self {
        Self {
            locals: FxHashMap::default(),
            params: vec![BindingTime::Dynamic; param_count],
        }
    }

    /// Create a new environment with specified parameter binding times.
    pub fn with_params(params: Vec<BindingTime>) -> Self {
        Self {
            locals: FxHashMap::default(),
            params,
        }
    }

    /// Get the binding time of a local variable.
    pub fn get_local(&self, id: u32) -> BindingTime {
        self.locals
            .get(&id)
            .copied()
            .unwrap_or(BindingTime::Dynamic)
    }

    /// Set the binding time of a local variable.
    pub fn set_local(&mut self, id: u32, bt: BindingTime) {
        self.locals.insert(id, bt);
    }

    /// Analyze the binding time of a MIR value.
    pub fn analyze_value(&self, value: &Value, mir: &MirFile) -> BindingTime {
        match value {
            Value::Constant(id) => {
                let constant = &mir.constants[*id];
                match &constant.kind {
                    ConstantKind::Int(_)
                    | ConstantKind::Float(_)
                    | ConstantKind::Bool(_)
                    | ConstantKind::Char(_)
                    | ConstantKind::String(_)
                    | ConstantKind::Unit
                    | ConstantKind::Resource { .. } => BindingTime::Static,
                    ConstantKind::Function(_) => BindingTime::Static,
                }
            }
            Value::Local(id) => self.get_local(*id),
            Value::Binary { lhs, rhs, .. } => {
                let l = self.analyze_value(lhs, mir);
                let r = self.analyze_value(rhs, mir);
                l.join(r)
            }
            Value::Unary { operand, .. } => self.analyze_value(operand, mir),
            // Field access, index, load, cast — conservatively dynamic
            _ => BindingTime::Dynamic,
        }
    }
}

/// Perform binding-time analysis on a MIR function.
///
/// Returns the binding-time environment after propagation.
pub fn analyze_function(
    func: &eclexia_mir::Function,
    mir: &MirFile,
    param_binding_times: &[BindingTime],
) -> BindingTimeEnv {
    let mut env = BindingTimeEnv::with_params(param_binding_times.to_vec());

    // Initialize parameters as locals (params have IDs 0..n-1)
    for (i, &bt) in param_binding_times.iter().enumerate() {
        env.set_local(i as u32, bt);
    }

    // Propagate through instructions
    for (_, block) in func.basic_blocks.iter() {
        for instr in &block.instructions {
            if let InstructionKind::Assign { target, value } = &instr.kind {
                let bt = env.analyze_value(value, mir);
                env.set_local(*target, bt);
            }
        }
    }

    env
}

/// Check if all resource constraints of a function are statically resolvable.
pub fn constraints_are_static(
    func: &eclexia_mir::Function,
    mir: &MirFile,
    env: &BindingTimeEnv,
) -> bool {
    // Resource constraints reference resource amounts — check if those are static
    for (_, block) in func.basic_blocks.iter() {
        for instr in &block.instructions {
            if let InstructionKind::ResourceTrack { amount, .. } = &instr.kind {
                if env.analyze_value(amount, mir) == BindingTime::Dynamic {
                    return false;
                }
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use eclexia_ast::dimension::Dimension;
    use eclexia_ast::span::Span;
    use eclexia_ast::types::{PrimitiveTy, Ty};
    use eclexia_mir::{
        BasicBlock, Constant, Function, Instruction, ResourceConstraint, Terminator, Value,
    };
    use la_arena::Arena;
    use smol_str::SmolStr;

    fn make_static_function(amounts: &[f64]) -> (MirFile, eclexia_mir::Function) {
        let mut constants: Arena<Constant> = Arena::new();
        let const_ids: Vec<_> = amounts
            .iter()
            .map(|v| {
                constants.alloc(Constant {
                    ty: Ty::Primitive(PrimitiveTy::Float),
                    kind: ConstantKind::Float(*v),
                })
            })
            .collect();

        let instructions: Vec<Instruction> = const_ids
            .iter()
            .map(|id| Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::ResourceTrack {
                    resource: SmolStr::new("energy"),
                    dimension: Dimension::energy(),
                    amount: Value::Constant(*id),
                },
            })
            .collect();

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions,
            terminator: Terminator::Return(None),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("test_fn"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Unit),
            locals: vec![],
            basic_blocks,
            entry_block: entry,
            resource_constraints: vec![ResourceConstraint {
                resource: SmolStr::new("energy"),
                dimension: Dimension::energy(),
                op: eclexia_mir::ConstraintOp::Le,
                bound: 100.0,
            }],
            is_adaptive: false,
        };

        let mir = MirFile {
            functions: vec![func.clone()],
            constants,
        };

        (mir, func)
    }

    #[test]
    fn test_all_static_constants() {
        let (mir, func) = make_static_function(&[30.0, 40.0]);
        let env = analyze_function(&func, &mir, &[]);
        assert!(constraints_are_static(&func, &mir, &env));
    }

    #[test]
    fn test_dynamic_parameter() {
        let constants: Arena<Constant> = Arena::new();
        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![Instruction {
                span: Span::new(0, 0),
                kind: InstructionKind::ResourceTrack {
                    resource: SmolStr::new("energy"),
                    dimension: Dimension::energy(),
                    amount: Value::Local(0), // parameter → dynamic
                },
            }],
            terminator: Terminator::Return(None),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("dynamic_fn"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Unit),
            locals: vec![],
            basic_blocks,
            entry_block: entry,
            resource_constraints: vec![ResourceConstraint {
                resource: SmolStr::new("energy"),
                dimension: Dimension::energy(),
                op: eclexia_mir::ConstraintOp::Le,
                bound: 100.0,
            }],
            is_adaptive: false,
        };

        let mir = MirFile {
            functions: vec![func.clone()],
            constants,
        };

        let env = analyze_function(&func, &mir, &[BindingTime::Dynamic]);
        assert!(!constraints_are_static(&func, &mir, &env));
    }

    #[test]
    fn test_static_parameter() {
        let mut constants: Arena<Constant> = Arena::new();
        let const_id = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Float),
            kind: ConstantKind::Float(50.0),
        });

        let mut basic_blocks: Arena<BasicBlock> = Arena::new();
        let entry = basic_blocks.alloc(BasicBlock {
            label: SmolStr::new("entry"),
            instructions: vec![
                // Assign: local1 = constant(50.0)
                Instruction {
                    span: Span::new(0, 0),
                    kind: InstructionKind::Assign {
                        target: 1,
                        value: Value::Constant(const_id),
                    },
                },
                // Track: energy += local1
                Instruction {
                    span: Span::new(0, 0),
                    kind: InstructionKind::ResourceTrack {
                        resource: SmolStr::new("energy"),
                        dimension: Dimension::energy(),
                        amount: Value::Local(1),
                    },
                },
            ],
            terminator: Terminator::Return(None),
        });

        let func = Function {
            span: Span::new(0, 0),
            name: SmolStr::new("assigned_fn"),
            params: vec![],
            return_ty: Ty::Primitive(PrimitiveTy::Unit),
            locals: vec![],
            basic_blocks,
            entry_block: entry,
            resource_constraints: vec![ResourceConstraint {
                resource: SmolStr::new("energy"),
                dimension: Dimension::energy(),
                op: eclexia_mir::ConstraintOp::Le,
                bound: 100.0,
            }],
            is_adaptive: false,
        };

        let mir = MirFile {
            functions: vec![func.clone()],
            constants,
        };

        let env = analyze_function(&func, &mir, &[]);
        // local1 was assigned from a constant → should be static
        assert_eq!(env.get_local(1), BindingTime::Static);
        assert!(constraints_are_static(&func, &mir, &env));
    }

    #[test]
    fn test_binding_time_env_default_dynamic() {
        let env = BindingTimeEnv::all_dynamic(3);
        assert_eq!(env.params.len(), 3);
        assert_eq!(env.get_local(0), BindingTime::Dynamic);
        assert_eq!(env.get_local(99), BindingTime::Dynamic);
    }

    #[test]
    fn test_value_analysis_binary() {
        let mut constants: Arena<Constant> = Arena::new();
        let c1 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Int),
            kind: ConstantKind::Int(10),
        });
        let c2 = constants.alloc(Constant {
            ty: Ty::Primitive(PrimitiveTy::Int),
            kind: ConstantKind::Int(20),
        });

        let mir = MirFile {
            functions: vec![],
            constants,
        };

        let env = BindingTimeEnv::all_dynamic(0);

        // static + static = static
        let val = Value::Binary {
            op: eclexia_mir::BinaryOp::Add,
            lhs: Box::new(Value::Constant(c1)),
            rhs: Box::new(Value::Constant(c2)),
        };
        assert_eq!(env.analyze_value(&val, &mir), BindingTime::Static);

        // static + dynamic = dynamic
        let val_mixed = Value::Binary {
            op: eclexia_mir::BinaryOp::Add,
            lhs: Box::new(Value::Constant(c1)),
            rhs: Box::new(Value::Local(0)), // dynamic
        };
        assert_eq!(env.analyze_value(&val_mixed, &mir), BindingTime::Dynamic);
    }
}
