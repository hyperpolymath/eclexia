# Eclexia Language Specification

<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell -->

**Version:** 1.0
**Date:** December 2025
**Authors:** Jonathan D.A. Jewell
**Status:** Draft Specification

---

## Abstract

This document provides the complete formal specification of the Eclexia programming language, including lexical structure, grammar, type system, and operational semantics. Eclexia is a statically-typed language implementing the Economics-as-Code paradigm, featuring resource types with dimensional analysis, adaptive execution blocks, shadow price computation, and carbon-aware scheduling.

---

## Table of Contents

1. [Introduction](#1-introduction)
2. [Lexical Structure](#2-lexical-structure)
3. [Grammar](#3-grammar)
4. [Types](#4-types)
5. [Expressions](#5-expressions)
6. [Declarations](#6-declarations)
7. [Patterns](#7-patterns)
8. [Modules](#8-modules)
9. [Type System](#9-type-system)
10. [Operational Semantics](#10-operational-semantics)
11. [Denotational Semantics](#11-denotational-semantics)
12. [Standard Library](#12-standard-library)
13. [Conformance](#13-conformance)

---

## 1. Introduction

### 1.1 Scope

This specification defines:
- Lexical and syntactic structure of Eclexia programs
- Static semantics (type system)
- Dynamic semantics (evaluation)
- Standard library interfaces

### 1.2 Conformance Levels

- **Core Eclexia:** Minimum conforming implementation
- **Standard Eclexia:** Core + standard library
- **Extended Eclexia:** Standard + implementation-defined extensions

### 1.3 Notation

- `UPPERCASE`: Terminal symbols (tokens)
- `lowercase`: Non-terminal symbols
- `'...'`: Literal strings
- `[...]`: Optional
- `{...}`: Zero or more repetitions
- `(...)+`: One or more repetitions
- `|`: Alternation

---

## 2. Lexical Structure

### 2.1 Character Set

Eclexia source files are UTF-8 encoded Unicode text.

```
unicode_char    ::= any Unicode code point
newline         ::= U+000A | U+000D U+000A | U+000D
whitespace      ::= U+0020 | U+0009 | newline
```

### 2.2 Comments

```
line_comment    ::= '//' {unicode_char - newline} newline
block_comment   ::= '/*' {unicode_char | block_comment} '*/'
doc_comment     ::= '///' {unicode_char - newline} newline
                  | '/**' {unicode_char | block_comment} '*/'
```

### 2.3 Identifiers

```
identifier      ::= ident_start {ident_continue}
ident_start     ::= 'a'..'z' | 'A'..'Z' | '_'
ident_continue  ::= ident_start | '0'..'9' | '\''
type_identifier ::= 'A'..'Z' {ident_continue}
```

### 2.4 Keywords

```
keyword ::= 'adaptive' | 'and' | 'as' | 'async' | 'await'
          | 'break' | 'carbon' | 'case' | 'continue'
          | 'def' | 'defer_until' | 'do' | 'effect' | 'else'
          | 'energy' | 'enum' | 'false' | 'fn' | 'for'
          | 'handle' | 'if' | 'impl' | 'import' | 'in'
          | 'latency' | 'let' | 'loop' | 'match' | 'maximize'
          | 'memory' | 'minimize' | 'mod' | 'module' | 'mut'
          | 'not' | 'observe' | 'optimize' | 'or' | 'provides'
          | 'pub' | 'requires' | 'return' | 'self' | 'solution'
          | 'struct' | 'then' | 'trait' | 'true' | 'type'
          | 'unit' | 'use' | 'when' | 'where' | 'while'
```

### 2.5 Literals

#### 2.5.1 Integer Literals

```
int_literal     ::= decimal_literal | hex_literal | octal_literal | binary_literal
decimal_literal ::= digit {digit | '_'}
hex_literal     ::= '0' ('x' | 'X') hex_digit {hex_digit | '_'}
octal_literal   ::= '0' ('o' | 'O') octal_digit {octal_digit | '_'}
binary_literal  ::= '0' ('b' | 'B') bin_digit {bin_digit | '_'}

digit           ::= '0'..'9'
hex_digit       ::= digit | 'a'..'f' | 'A'..'F'
octal_digit     ::= '0'..'7'
bin_digit       ::= '0' | '1'
```

#### 2.5.2 Floating-Point Literals

```
float_literal   ::= decimal_literal '.' decimal_literal [exponent]
                  | decimal_literal exponent
exponent        ::= ('e' | 'E') ['+' | '-'] decimal_literal
```

#### 2.5.3 Resource Literals

```
resource_literal ::= (int_literal | float_literal) unit_symbol
unit_symbol      ::= energy_unit | time_unit | memory_unit | carbon_unit | power_unit

energy_unit      ::= 'J' | 'kJ' | 'MJ' | 'mJ' | 'μJ' | 'nJ' | 'Wh' | 'kWh'
time_unit        ::= 's' | 'ms' | 'μs' | 'ns' | 'min' | 'h' | 'd'
memory_unit      ::= 'B' | 'KB' | 'MB' | 'GB' | 'TB' | 'KiB' | 'MiB' | 'GiB' | 'TiB'
carbon_unit      ::= 'gCO2e' | 'kgCO2e' | 'tCO2e'
power_unit       ::= 'W' | 'kW' | 'MW' | 'mW' | 'μW'
```

#### 2.5.4 String Literals

```
string_literal   ::= '"' {string_char | escape_seq} '"'
                   | 'r"' {unicode_char - '"'} '"'
                   | 'r#"' {unicode_char} '"#'

string_char      ::= unicode_char - ('"' | '\' | newline)
escape_seq       ::= '\' ('n' | 'r' | 't' | '\' | '"' | '0'
                        | 'x' hex_digit hex_digit
                        | 'u{' hex_digit+ '}')
```

#### 2.5.5 Character Literals

```
char_literal     ::= '\'' (unicode_char - ('\'' | '\')) '\''
                   | '\'' escape_seq '\''
```

### 2.6 Operators and Punctuation

```
operator ::= '+' | '-' | '*' | '/' | '%' | '^'
           | '==' | '!=' | '<' | '>' | '<=' | '>='
           | '&&' | '||' | '!'
           | '&' | '|' | '~' | '<<' | '>>'
           | '=' | '+=' | '-=' | '*=' | '/=' | '%='
           | '->' | '=>' | '::'
           | '.' | '..' | '..='
           | '@'

punctuation ::= '(' | ')' | '[' | ']' | '{' | '}'
              | ',' | ':' | ';' | '#'
```

---

## 3. Grammar

### 3.1 Program Structure

```
program         ::= {item}
item            ::= visibility? item_kind
visibility      ::= 'pub' ['(' pub_scope ')']
pub_scope       ::= 'crate' | 'super' | 'self' | 'in' path

item_kind       ::= module_decl
                  | import_decl
                  | type_alias
                  | struct_decl
                  | enum_decl
                  | trait_decl
                  | impl_block
                  | function_decl
                  | adaptive_decl
                  | const_decl
                  | effect_decl
```

### 3.2 Modules and Imports

```
module_decl     ::= 'module' IDENT ['{' {item} '}']
import_decl     ::= 'use' use_tree ';'
use_tree        ::= path ['::' ('*' | '{' use_tree {',' use_tree} [','] '}')]
                  | path 'as' IDENT
path            ::= ['::'] path_segment {'::' path_segment}
path_segment    ::= IDENT ['::<' type_args '>']
```

### 3.3 Type Declarations

```
type_alias      ::= 'type' TYPE_IDENT [type_params] '=' type ';'

struct_decl     ::= 'struct' TYPE_IDENT [type_params] [where_clause]
                    ('{' struct_fields '}' | '(' tuple_fields ')' ';' | ';')
struct_fields   ::= {struct_field ','}
struct_field    ::= visibility? IDENT ':' type

enum_decl       ::= 'enum' TYPE_IDENT [type_params] [where_clause]
                    '{' enum_variants '}'
enum_variants   ::= {enum_variant ','}
enum_variant    ::= IDENT [('(' tuple_fields ')' | '{' struct_fields '}')]

trait_decl      ::= 'trait' TYPE_IDENT [type_params] [':' trait_bounds]
                    [where_clause] '{' {trait_item} '}'
trait_item      ::= type_alias | function_sig ';' | function_decl

impl_block      ::= 'impl' [type_params] [trait_path 'for'] type
                    [where_clause] '{' {impl_item} '}'
impl_item       ::= type_alias | function_decl
```

### 3.4 Function Declarations

```
function_decl   ::= 'def' IDENT [type_params] '(' params ')' ['->' type]
                    [resource_annotations] [where_clause] block

adaptive_decl   ::= 'adaptive' 'def' IDENT [type_params] '(' params ')' '->' type
                    resource_annotations [where_clause]
                    '{' {solution_block}+ '}'

function_sig    ::= 'def' IDENT [type_params] '(' params ')' ['->' type]
                    [resource_annotations] [where_clause]

params          ::= [param {',' param} [',']]
param           ::= pattern ':' type

type_params     ::= '<' type_param {',' type_param} [','] '>'
type_param      ::= TYPE_IDENT [':' trait_bounds] ['=' type]
trait_bounds    ::= trait_bound {'+' trait_bound}
trait_bound     ::= path | '(' trait_bound ')'
where_clause    ::= 'where' where_pred {',' where_pred} [',']
where_pred      ::= type ':' trait_bounds
```

### 3.5 Resource Annotations

```
resource_annotations ::= {resource_annotation}
resource_annotation  ::= requires_clause
                       | provides_clause
                       | optimize_clause
                       | observe_clause
                       | defer_clause

requires_clause ::= '@requires' ':' constraint_list
provides_clause ::= '@provides' ':' resource_binding {',' resource_binding}
optimize_clause ::= '@optimize' ':' objective {',' objective}
observe_clause  ::= '@observe' ':' IDENT {',' IDENT}
defer_clause    ::= '@defer_until' ':' expr

constraint_list ::= constraint {',' constraint}
constraint      ::= resource_expr compare_op expr
compare_op      ::= '<' | '<=' | '>' | '>=' | '==' | '!='

resource_binding ::= IDENT ':' resource_literal

objective       ::= ('minimize' | 'maximize') IDENT
```

### 3.6 Solution Blocks

```
solution_block  ::= '@solution' STRING ':' [when_clause] [provides_clause] block

when_clause     ::= '@when' ':' expr
```

### 3.7 Effect Declarations

```
effect_decl     ::= 'effect' TYPE_IDENT [type_params] '{' {effect_op} '}'
effect_op       ::= IDENT '(' params ')' ['->' type] ';'
```

---

## 4. Types

### 4.1 Type Syntax

```
type            ::= type_path
                  | '(' ')'                              // Unit
                  | '(' type ',' type {',' type} [','] ')'  // Tuple
                  | '[' type ']'                         // Array
                  | '[' type ';' expr ']'                // Fixed array
                  | type '->' type                       // Function
                  | '&' ['mut'] type                     // Reference
                  | type '?'                             // Optional
                  | resource_type                        // Resource
                  | type '@requires' constraint_list     // Constrained
                  | 'fn' '(' [type_list] ')' ['->' type] // Fn pointer

type_path       ::= path ['::<' type_args '>']
type_args       ::= type {',' type} [',']
type_list       ::= type {',' type} [',']

resource_type   ::= 'Energy' '[' dimension ']'
                  | 'Time' '[' dimension ']'
                  | 'Memory' '[' dimension ']'
                  | 'Carbon' '[' dimension ']'
                  | 'Power' '[' dimension ']'
                  | resource_type_short

resource_type_short ::= 'Energy' | 'Time' | 'Memory' | 'Carbon' | 'Power'
```

### 4.2 Dimensions

```
dimension       ::= '1'                                  // Dimensionless
                  | base_dim
                  | dimension '*' dimension              // Product
                  | dimension '/' dimension              // Quotient
                  | dimension '^' int_literal            // Power
                  | '(' dimension ')'

base_dim        ::= 'M' | 'L' | 'T' | 'I' | 'Θ' | 'N' | 'J'
                  // Mass, Length, Time, Current, Temperature, Amount, Luminosity
```

### 4.3 Built-in Types

| Type | Description |
|------|-------------|
| `Unit` | Unit type (zero-sized) |
| `Bool` | Boolean |
| `Int` | Signed integer (platform-sized) |
| `Int8`, `Int16`, `Int32`, `Int64`, `Int128` | Fixed-width signed integers |
| `Uint`, `Uint8`, `Uint16`, `Uint32`, `Uint64`, `Uint128` | Unsigned integers |
| `Float32`, `Float64` | IEEE 754 floating point |
| `Char` | Unicode scalar value |
| `String` | UTF-8 string |
| `[T]` | Dynamically-sized slice |
| `[T; N]` | Fixed-size array |
| `(T1, T2, ...)` | Tuple |
| `Option[T]` | Optional value |
| `Result[T, E]` | Result or error |

---

## 5. Expressions

### 5.1 Expression Syntax

```
expr            ::= expr_with_block | expr_without_block

expr_without_block ::=
                    literal
                  | path_expr
                  | '(' expr ')'
                  | '(' expr ',' expr {',' expr} [','] ')'  // Tuple
                  | '[' [expr {',' expr} [',']] ']'         // Array
                  | '[' expr ';' expr ']'                   // Repeat array
                  | prefix_op expr
                  | expr binary_op expr
                  | expr '.' IDENT                          // Field access
                  | expr '.' int_literal                    // Tuple index
                  | expr '.' IDENT '(' [args] ')'           // Method call
                  | expr '(' [args] ')'                     // Call
                  | expr '[' expr ']'                       // Index
                  | expr '?'                                // Try
                  | expr 'as' type                          // Cast
                  | '&' ['mut'] expr                        // Borrow
                  | '*' expr                                // Deref
                  | range_expr
                  | closure_expr
                  | 'return' [expr]
                  | 'break' [IDENT] [expr]
                  | 'continue' [IDENT]

expr_with_block ::=
                    block
                  | if_expr
                  | match_expr
                  | loop_expr
                  | for_expr
                  | while_expr
                  | async_block
                  | handle_expr

path_expr       ::= path
literal         ::= int_literal | float_literal | char_literal
                  | string_literal | 'true' | 'false' | resource_literal

prefix_op       ::= '-' | '!' | '~'
binary_op       ::= '+' | '-' | '*' | '/' | '%'
                  | '==' | '!=' | '<' | '>' | '<=' | '>='
                  | '&&' | '||'
                  | '&' | '|' | '^' | '<<' | '>>'

range_expr      ::= expr '..' expr
                  | expr '..=' expr
                  | expr '..'
                  | '..' expr
                  | '..=' expr
                  | '..'

closure_expr    ::= '|' [closure_params] '|' ['->' type] (expr | block)
closure_params  ::= closure_param {',' closure_param}
closure_param   ::= pattern [':' type]

args            ::= expr {',' expr} [',']
```

### 5.2 Block Expressions

```
block           ::= '{' {statement} [expr] '}'

statement       ::= ';'
                  | item
                  | let_stmt
                  | expr_stmt

let_stmt        ::= 'let' ['mut'] pattern [':' type] ['=' expr] ';'
expr_stmt       ::= expr ';'
                  | expr_with_block [';']
```

### 5.3 Control Flow

```
if_expr         ::= 'if' expr block ['else' (if_expr | block)]

match_expr      ::= 'match' expr '{' {match_arm} '}'
match_arm       ::= pattern [guard] '=>' (expr ',' | expr_with_block [','])
guard           ::= 'if' expr

loop_expr       ::= ['label' ':'] 'loop' block
while_expr      ::= ['label' ':'] 'while' expr block
for_expr        ::= ['label' ':'] 'for' pattern 'in' expr block

label           ::= '\'' IDENT
```

### 5.4 Async and Effects

```
async_block     ::= 'async' block
await_expr      ::= expr '.' 'await'

handle_expr     ::= 'handle' effect_handlers block
effect_handlers ::= '{' {effect_handler} '}'
effect_handler  ::= path '.' IDENT '(' params ')' '=>' expr ','
```

---

## 6. Declarations

### 6.1 Constant Declarations

```
const_decl      ::= 'const' IDENT ':' type '=' expr ';'
static_decl     ::= 'static' ['mut'] IDENT ':' type '=' expr ';'
```

### 6.2 Type Aliases

```
type_alias      ::= 'type' TYPE_IDENT [type_params] '=' type ';'
```

### 6.3 External Declarations

```
extern_block    ::= 'extern' [abi] '{' {extern_item} '}'
abi             ::= STRING
extern_item     ::= visibility? (function_sig ';' | static_decl)
```

---

## 7. Patterns

### 7.1 Pattern Syntax

```
pattern         ::= literal_pattern
                  | identifier_pattern
                  | wildcard_pattern
                  | range_pattern
                  | reference_pattern
                  | struct_pattern
                  | tuple_struct_pattern
                  | tuple_pattern
                  | slice_pattern
                  | or_pattern
                  | grouped_pattern

literal_pattern ::= 'true' | 'false' | char_literal | string_literal
                  | '-'? int_literal | '-'? float_literal

identifier_pattern ::= ['ref'] ['mut'] IDENT ['@' pattern]

wildcard_pattern ::= '_'

range_pattern   ::= pattern '..' pattern
                  | pattern '..=' pattern

reference_pattern ::= '&' ['mut'] pattern

struct_pattern  ::= path '{' [struct_pattern_fields] '}'
struct_pattern_fields ::= struct_pattern_field {',' struct_pattern_field} [',']
struct_pattern_field ::= IDENT [':' pattern] | '..'

tuple_struct_pattern ::= path '(' [pattern {',' pattern} [','] ')'

tuple_pattern   ::= '(' [pattern {',' pattern} [',']] ')'

slice_pattern   ::= '[' [pattern {',' pattern} [',']] ']'

or_pattern      ::= pattern '|' pattern

grouped_pattern ::= '(' pattern ')'
```

---

## 8. Modules

### 8.1 Module System

Eclexia uses a hierarchical module system:

```
module foo {
    pub def bar() -> Int { 42 }

    module nested {
        pub def baz() -> Int { foo::bar() }
    }
}
```

### 8.2 Visibility

- `pub`: Public to all
- `pub(crate)`: Public within crate
- `pub(super)`: Public to parent module
- `pub(self)`: Private (default)
- `pub(in path)`: Public to specified path

### 8.3 Imports

```
use std::collections::HashMap;
use std::io::{Read, Write};
use crate::utils::*;
use super::config as cfg;
```

---

## 9. Type System

### 9.1 Typing Judgment

The typing judgment `Γ ⊢ e : τ` states that expression `e` has type `τ` in context `Γ`.

### 9.2 Type Inference

Eclexia uses bidirectional type inference:
- **Synthesis**: `Γ ⊢ e ⇒ τ` (infer type from expression)
- **Checking**: `Γ ⊢ e ⇐ τ` (check expression against type)

### 9.3 Subtyping

Eclexia has structural subtyping for resources:
```
τ @requires C₁ <: τ @requires C₂   if C₁ ⊇ C₂
```

### 9.4 Typing Rules

See docs/proofs/PROOFS.md §2 for complete typing rules.

### 9.5 Kind System

```
κ ::= *           // Type
    | κ → κ       // Type constructor
    | Resource    // Resource kind
    | Dimension   // Dimension kind
    | Constraint  // Constraint kind
```

---

## 10. Operational Semantics

### 10.1 Values

```
v ::= ()                            // Unit
    | true | false                  // Booleans
    | n                             // Integers
    | r                             // Floats
    | 'c'                           // Characters
    | "..."                         // Strings
    | n unit                        // Resource values
    | (v₁, ..., vₙ)                 // Tuples
    | [v₁, ..., vₙ]                 // Arrays
    | Struct { f₁: v₁, ..., fₙ: vₙ } // Structs
    | Variant(v)                    // Enum variants
    | λx. e                         // Closures
    | &v                            // References
```

### 10.2 Evaluation Contexts

```
E ::= □
    | E e | v E
    | (v₁, ..., vᵢ₋₁, E, eᵢ₊₁, ..., eₙ)
    | [v₁, ..., vᵢ₋₁, E, eᵢ₊₁, ..., eₙ]
    | E.f
    | E(e₁, ..., eₙ) | v(v₁, ..., vᵢ₋₁, E, eᵢ₊₁, ..., eₙ)
    | E[e] | v[E]
    | E + e | v + E | E - e | v - E | ...
    | E == e | v == E | E < e | v < E | ...
    | E && e | E || e
    | let x = E in e
    | if E then e₁ else e₂
    | match E { arms }
    | E?
    | return E
    | &E | *E
```

### 10.3 Reduction Rules

#### 10.3.1 Core Reductions

```
(λx. e) v ⟶ e[x := v]                              (β)

let x = v in e ⟶ e[x := v]                         (let)

if true then e₁ else e₂ ⟶ e₁                       (if-true)
if false then e₁ else e₂ ⟶ e₂                      (if-false)

match Cᵢ(v) { C₁(x₁) => e₁, ..., Cₙ(xₙ) => eₙ }
    ⟶ eᵢ[xᵢ := v]                                  (match)

(v₁, ..., vₙ).i ⟶ vᵢ                               (tuple-proj)

Struct { f₁: v₁, ..., fₙ: vₙ }.fᵢ ⟶ vᵢ            (field)

[v₁, ..., vₙ][i] ⟶ vᵢ₊₁    if 0 ≤ i < n           (index)

*(&v) ⟶ v                                          (deref)

Some(v)? ⟶ v                                       (try-some)
None? ⟶ return None                                (try-none)
```

#### 10.3.2 Arithmetic Reductions

```
n₁ + n₂ ⟶ n₁ + n₂                                  (add-int)
r₁ + r₂ ⟶ r₁ + r₂                                  (add-float)
n₁ - n₂ ⟶ n₁ - n₂                                  (sub-int)
n₁ * n₂ ⟶ n₁ * n₂                                  (mul-int)
n₁ / n₂ ⟶ n₁ / n₂    if n₂ ≠ 0                    (div-int)
n₁ % n₂ ⟶ n₁ mod n₂  if n₂ ≠ 0                    (mod-int)
```

#### 10.3.3 Resource Reductions

```
(n₁ unit) + (n₂ unit) ⟶ (n₁ + n₂) unit            (res-add)
(n₁ u₁) * (n₂ u₂) ⟶ (n₁ * n₂) (u₁ · u₂)           (res-mul)
(n₁ u₁) / (n₂ u₂) ⟶ (n₁ / n₂) (u₁ / u₂)           (res-div)
```

#### 10.3.4 Adaptive Reductions

```
adaptive { solutions } ⟶ eᵢ
    where i = select(solutions, Σ, B, objectives)  (adaptive)
```

### 10.4 Error States

```
error ::= DivisionByZero
        | IndexOutOfBounds(i, len)
        | ResourceExhausted(resource)
        | PatternMatchFailure
        | AssertionFailed(msg)
        | Panic(msg)
```

---

## 11. Denotational Semantics

### 11.1 Semantic Domains

```
⟦Bool⟧ = {true, false}
⟦Int⟧ = ℤ
⟦Float⟧ = ℝ (IEEE 754)
⟦Unit⟧ = {()}
⟦τ₁ × τ₂⟧ = ⟦τ₁⟧ × ⟦τ₂⟧
⟦τ₁ → τ₂⟧ = ⟦τ₁⟧ → ⟦τ₂⟧⊥  (partial functions)
⟦ρ[d]⟧ = ℝ × Dim(d)  (real value with dimension)
⟦τ @requires C⟧ = { v ∈ ⟦τ⟧ | C(v) holds }
```

### 11.2 Expression Semantics

```
⟦n⟧ρ = n
⟦r⟧ρ = r
⟦x⟧ρ = ρ(x)
⟦λx. e⟧ρ = λv. ⟦e⟧ρ[x ↦ v]
⟦e₁ e₂⟧ρ = ⟦e₁⟧ρ (⟦e₂⟧ρ)
⟦let x = e₁ in e₂⟧ρ = ⟦e₂⟧ρ[x ↦ ⟦e₁⟧ρ]
⟦if e₁ then e₂ else e₃⟧ρ = if ⟦e₁⟧ρ then ⟦e₂⟧ρ else ⟦e₃⟧ρ
⟦(e₁, e₂)⟧ρ = (⟦e₁⟧ρ, ⟦e₂⟧ρ)
⟦fst e⟧ρ = π₁(⟦e⟧ρ)
⟦snd e⟧ρ = π₂(⟦e⟧ρ)
```

### 11.3 Resource Semantics

```
⟦n unit⟧ρ = (n, dim(unit))
⟦e₁ + e₂⟧ρ = let (n₁, d) = ⟦e₁⟧ρ, (n₂, d') = ⟦e₂⟧ρ in
              if d = d' then (n₁ + n₂, d) else ⊥
⟦e₁ * e₂⟧ρ = let (n₁, d₁) = ⟦e₁⟧ρ, (n₂, d₂) = ⟦e₂⟧ρ in
              (n₁ * n₂, d₁ · d₂)
⟦e₁ / e₂⟧ρ = let (n₁, d₁) = ⟦e₁⟧ρ, (n₂, d₂) = ⟦e₂⟧ρ in
              if n₂ ≠ 0 then (n₁ / n₂, d₁ / d₂) else ⊥
```

### 11.4 Adaptive Semantics

```
⟦adaptive { sᵢ }⟧ρ,Σ,B,λ =
    let feasible = { i | ⟦gᵢ⟧ρ ∧ Σ + pᵢ ⊑ B } in
    if feasible = ∅ then ⊥
    else let i* = argmin_{i ∈ feasible} λ · pᵢ in
         (⟦eᵢ*⟧ρ, Σ + pᵢ*)
```

---

## 12. Standard Library

### 12.1 Core Module

```eclexia
module core {
    // Primitive types are built-in

    pub trait Clone {
        def clone(&self) -> Self;
    }

    pub trait Copy: Clone {}

    pub trait Default {
        def default() -> Self;
    }

    pub trait Eq {
        def eq(&self, other: &Self) -> Bool;
        def ne(&self, other: &Self) -> Bool { !self.eq(other) }
    }

    pub trait Ord: Eq {
        def cmp(&self, other: &Self) -> Ordering;
        def lt(&self, other: &Self) -> Bool;
        def le(&self, other: &Self) -> Bool;
        def gt(&self, other: &Self) -> Bool;
        def ge(&self, other: &Self) -> Bool;
    }

    pub enum Ordering { Less, Equal, Greater }

    pub enum Option[T] {
        Some(T),
        None,
    }

    pub enum Result[T, E] {
        Ok(T),
        Err(E),
    }
}
```

### 12.2 Resources Module

```eclexia
module resources {
    pub type Energy = Energy[M * L^2 * T^-2];
    pub type Time = Time[T];
    pub type Memory = Memory[1];
    pub type Carbon = Carbon[M];
    pub type Power = Power[M * L^2 * T^-3];

    pub trait Resource {
        type Dimension;
        def value(&self) -> Float64;
        def unit(&self) -> String;
    }

    pub def convert[R: Resource](from: R, to_unit: String) -> R;

    pub def current_budget() -> Budget;
    pub def remaining_budget() -> Budget;
    pub def shadow_prices() -> ShadowPrices;

    pub struct Budget {
        energy: Option[Energy],
        time: Option[Time],
        memory: Option[Memory],
        carbon: Option[Carbon],
    }

    pub struct ShadowPrices {
        energy: Float64,
        time: Float64,
        memory: Float64,
        carbon: Float64,
    }
}
```

### 12.3 Carbon Module

```eclexia
module carbon {
    pub async def grid_carbon_intensity(location: Location) -> Carbon;
    pub async def carbon_forecast(location: Location, hours: Int) -> Array[CarbonForecast];

    pub struct Location {
        latitude: Float64,
        longitude: Float64,
        region: Option[String],
    }

    pub struct CarbonForecast {
        time: Timestamp,
        intensity: Carbon,
        source: String,
    }

    pub async def defer_until_low_carbon[T](
        threshold: Carbon,
        task: async fn() -> T
    ) -> T;
}
```

### 12.4 Collections Module

```eclexia
module collections {
    pub struct Vec[T] { ... }
    pub struct HashMap[K, V] { ... }
    pub struct HashSet[T] { ... }
    pub struct BTreeMap[K, V] { ... }
    pub struct BTreeSet[T] { ... }
    pub struct LinkedList[T] { ... }
    pub struct VecDeque[T] { ... }
}
```

### 12.5 IO Module

```eclexia
module io {
    pub effect IO {
        read_line() -> Result[String, IoError];
        write_line(s: String) -> Result[Unit, IoError];
        read_file(path: String) -> Result[String, IoError];
        write_file(path: String, content: String) -> Result[Unit, IoError];
    }

    pub trait Read {
        def read(&mut self, buf: &mut [Uint8]) -> Result[Int, IoError];
    }

    pub trait Write {
        def write(&mut self, buf: &[Uint8]) -> Result[Int, IoError];
        def flush(&mut self) -> Result[Unit, IoError];
    }

    pub struct IoError { kind: IoErrorKind, message: String }
    pub enum IoErrorKind { NotFound, PermissionDenied, ... }
}
```

---

## 13. Conformance

### 13.1 Required Features

A conforming Eclexia implementation MUST:

1. Accept all syntactically valid programs as defined in §3
2. Reject all ill-typed programs as defined in §9
3. Implement all typing rules from docs/proofs/PROOFS.md
4. Implement all reduction rules from §10
5. Provide the core standard library from §12.1
6. Support resource types and dimensional analysis

### 13.2 Implementation-Defined Behavior

The following are implementation-defined:

1. Maximum integer size (minimum: 64-bit)
2. Floating-point precision beyond IEEE 754
3. Maximum recursion depth
4. Maximum memory allocation
5. Carbon intensity data sources
6. Shadow price computation algorithm (must satisfy §8 properties)

### 13.3 Optional Features

The following features are optional:

1. GPU acceleration
2. Carbon-aware scheduling
3. Distributed adaptive selection
4. IDE integration
5. Profile-guided optimization

### 13.4 Extensions

Implementations MAY provide extensions marked with `#[extension]`. Extensions:
- MUST NOT change semantics of conforming programs
- MUST be documented
- MUST be opt-in

---

## Appendix A: Complete EBNF Grammar

**TODO:** Generate machine-readable grammar file.

## Appendix B: Unicode Categories

**TODO:** Define allowed Unicode categories for identifiers.

## Appendix C: Operator Precedence

| Precedence | Operators | Associativity |
|------------|-----------|---------------|
| 1 (lowest) | `=` `+=` `-=` `*=` `/=` `%=` | Right |
| 2 | `||` | Left |
| 3 | `&&` | Left |
| 4 | `==` `!=` `<` `>` `<=` `>=` | Non-assoc |
| 5 | `|` | Left |
| 6 | `^` | Left |
| 7 | `&` | Left |
| 8 | `<<` `>>` | Left |
| 9 | `+` `-` | Left |
| 10 | `*` `/` `%` | Left |
| 11 | `as` | Left |
| 12 (highest) | Unary `-` `!` `~` `&` `*` | Right |

## Appendix D: Reserved Words

The following identifiers are reserved for future use:
```
abstract, become, box, do, final, macro, override,
priv, try, typeof, unsized, virtual, yield
```

---

**Document Version:** 1.0
**Last Updated:** December 2025
**License:** PMPL-1.0-or-later

```bibtex
@techreport{eclexia2025spec,
  title={Eclexia Language Specification},
  author={Jewell, Jonathan D.A.},
  year={2025},
  month={December},
  institution={Eclexia Project},
  url={https://eclexia.org/specification},
  note={Version 1.0}
}
```
