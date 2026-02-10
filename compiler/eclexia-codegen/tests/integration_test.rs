// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Integration tests for code generation and VM execution.

use eclexia_ast::span::Span;
use eclexia_ast::types::{PrimitiveTy, Ty};
use eclexia_codegen::{Backend, BytecodeGenerator, VirtualMachine, VmValue};
use eclexia_mir::{
    BasicBlock, BinaryOp, Constant, ConstantKind, Function, Instruction, InstructionKind, Local,
    MirFile, Terminator, Value,
};
use la_arena::Arena;
use smol_str::SmolStr;

#[test]
fn test_simple_arithmetic() {
    // Create a simple MIR function: fn main() -> Int { 5 + 10 }
    let mut mir = MirFile::new();

    // Constants
    let const_5 = mir.constants.alloc(Constant {
        ty: Ty::Primitive(PrimitiveTy::Int),
        kind: ConstantKind::Int(5),
    });

    let const_10 = mir.constants.alloc(Constant {
        ty: Ty::Primitive(PrimitiveTy::Int),
        kind: ConstantKind::Int(10),
    });

    // Create main function
    let mut basic_blocks = Arena::new();
    let entry_block = basic_blocks.alloc(BasicBlock {
        label: SmolStr::new("entry"),
        instructions: vec![Instruction {
            span: Span::default(),
            kind: InstructionKind::Nop,
        }],
        terminator: Terminator::Return(Some(Value::Binary {
            op: BinaryOp::Add,
            lhs: Box::new(Value::Constant(const_5)),
            rhs: Box::new(Value::Constant(const_10)),
        })),
    });

    let func = Function {
        span: Span::default(),
        name: SmolStr::new("main"),
        params: Vec::new(),
        return_ty: Ty::Primitive(PrimitiveTy::Int),
        locals: Vec::new(),
        basic_blocks,
        entry_block,
        resource_constraints: Vec::new(),
        is_adaptive: false,
    };

    mir.functions.push(func);

    // Generate bytecode
    let mut codegen = BytecodeGenerator::new();
    let bytecode = codegen.generate(&mir).expect("Bytecode generation failed");

    // Execute on VM
    let mut vm = VirtualMachine::new(bytecode);
    let result = vm.run().expect("VM execution failed");

    // Verify result
    match result {
        VmValue::Int(n) => assert_eq!(n, 15, "Expected 5 + 10 = 15"),
        _ => panic!("Expected integer result"),
    }
}

#[test]
fn test_local_variables() {
    // Create: fn main() -> Int { let x = 42; x }
    let mut mir = MirFile::new();

    let const_42 = mir.constants.alloc(Constant {
        ty: Ty::Primitive(PrimitiveTy::Int),
        kind: ConstantKind::Int(42),
    });

    let mut basic_blocks = Arena::new();
    let entry_block = basic_blocks.alloc(BasicBlock {
        label: SmolStr::new("entry"),
        instructions: vec![
            // x = 42
            Instruction {
                span: Span::default(),
                kind: InstructionKind::Assign {
                    target: 0,
                    value: Value::Constant(const_42),
                },
            },
        ],
        terminator: Terminator::Return(Some(Value::Local(0))),
    });

    let func = Function {
        span: Span::default(),
        name: SmolStr::new("main"),
        params: Vec::new(),
        return_ty: Ty::Primitive(PrimitiveTy::Int),
        locals: vec![Local {
            id: 0,
            name: SmolStr::new("x"),
            ty: Ty::Primitive(PrimitiveTy::Int),
            mutable: false,
        }],
        basic_blocks,
        entry_block,
        resource_constraints: Vec::new(),
        is_adaptive: false,
    };

    mir.functions.push(func);

    // Generate and execute
    let mut codegen = BytecodeGenerator::new();
    let bytecode = codegen.generate(&mir).expect("Bytecode generation failed");

    let mut vm = VirtualMachine::new(bytecode);
    let result = vm.run().expect("VM execution failed");

    match result {
        VmValue::Int(n) => assert_eq!(n, 42, "Expected x = 42"),
        _ => panic!("Expected integer result"),
    }
}

#[test]
fn test_comparison_operations() {
    // Create: fn main() -> Bool { 10 > 5 }
    let mut mir = MirFile::new();

    let const_10 = mir.constants.alloc(Constant {
        ty: Ty::Primitive(PrimitiveTy::Int),
        kind: ConstantKind::Int(10),
    });

    let const_5 = mir.constants.alloc(Constant {
        ty: Ty::Primitive(PrimitiveTy::Int),
        kind: ConstantKind::Int(5),
    });

    let mut basic_blocks = Arena::new();
    let entry_block = basic_blocks.alloc(BasicBlock {
        label: SmolStr::new("entry"),
        instructions: vec![],
        terminator: Terminator::Return(Some(Value::Binary {
            op: BinaryOp::Gt,
            lhs: Box::new(Value::Constant(const_10)),
            rhs: Box::new(Value::Constant(const_5)),
        })),
    });

    let func = Function {
        span: Span::default(),
        name: SmolStr::new("main"),
        params: Vec::new(),
        return_ty: Ty::Primitive(PrimitiveTy::Bool),
        locals: Vec::new(),
        basic_blocks,
        entry_block,
        resource_constraints: Vec::new(),
        is_adaptive: false,
    };

    mir.functions.push(func);

    // Generate and execute
    let mut codegen = BytecodeGenerator::new();
    let bytecode = codegen.generate(&mir).expect("Bytecode generation failed");

    let mut vm = VirtualMachine::new(bytecode);
    let result = vm.run().expect("VM execution failed");

    match result {
        VmValue::Bool(b) => assert!(b, "Expected 10 > 5 = true"),
        _ => panic!("Expected boolean result"),
    }
}
