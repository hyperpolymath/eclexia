# Eclexia Language Reference

**Version:** 0.1.0
**Last Updated:** 2026-02-07

This document is the authoritative specification for the Eclexia programming language.

---

## Table of Contents

1. [Lexical Structure](#lexical-structure)
2. [Syntax](#syntax)
3. [Type System](#type-system)
4. [Resource Semantics](#resource-semantics)
5. [Runtime Behavior](#runtime-behavior)
6. [Standard Library](#standard-library)

---

## Lexical Structure

### Keywords

Reserved keywords that cannot be used as identifiers:

```
fn          let         mut         if          else
match       for         while       loop        break
continue    return      struct      enum        type
impl        trait       use         pub         resource
adaptive    shadow      dimension   requires    provides
Some        None        Ok          Err         true
false       const
```

### Identifiers

Identifiers start with a letter or underscore, followed by letters, digits, or underscores:

```ebnf
identifier ::= ( letter | '_' ) ( letter | digit | '_' )*
letter     ::= 'a'..'z' | 'A'..'Z'
digit      ::= '0'..'9'
```

Examples:
```eclexia
x
myVariable
_internal
snake_case_name
CamelCaseName
```

### Literals

**Integer literals:**
```ebnf
integer ::= decimal_literal | hex_literal | binary_literal | octal_literal
decimal_literal ::= digit ( digit | '_' )*
hex_literal ::= '0x' hex_digit ( hex_digit | '_' )*
binary_literal ::= '0b' ('0' | '1') ( '0' | '1' | '_' )*
octal_literal ::= '0o' octal_digit ( octal_digit | '_' )*
```

Examples: `42`, `1_000_000`, `0xFF`, `0b1010`, `0o755`

**Float literals:**
```ebnf
float ::= decimal_literal '.' decimal_literal ( exponent )?
       | decimal_literal exponent
exponent ::= ( 'e' | 'E' ) ( '+' | '-' )? decimal_literal
```

Examples: `3.14`, `1.0e-10`, `6.022e23`

**String literals:**
```ebnf
string ::= '"' ( string_char | escape_sequence )* '"'
string_char ::= any character except '"' or '\'
escape_sequence ::= '\n' | '\t' | '\r' | '\\' | '\"' | '\0'
```

Examples: `"hello"`, `"line1\nline2"`, `"quote: \"text\""`

**Dimensional literals:**
```ebnf
dimensional_literal ::= ( integer | float ) dimension_unit
dimension_unit ::= 'J' | 's' | 'm' | 'kg' | 'K' | 'A' | 'mol' | 'cd'
                 | derived_unit
derived_unit ::= base_unit ( '·' base_unit )* ( '/' base_unit )*
               | base_unit '^' integer
```

Examples: `100J`, `5s`, `3.14m`, `10kg·m²/s²`

### Operators

**Arithmetic:** `+` `-` `*` `/` `%` `^`

**Comparison:** `==` `!=` `<` `>` `<=` `>=`

**Logical:** `&&` `||` `!`

**Bitwise:** `&` `|` `^` `<<` `>>`

**Assignment:** `=` `+=` `-=` `*=` `/=`

**Other:** `.` `::` `->` `=>` `?` `@`

### Comments

**Line comments:**
```eclexia
// This is a line comment
```

**Block comments:**
```eclexia
/* This is a
   block comment */
```

**Documentation comments:**
```eclexia
/// Documentation for the following item
fn documented_function() { }

//! Documentation for the containing module
```

---

## Syntax

### EBNF Grammar

Complete formal grammar in Extended Backus-Naur Form:

```ebnf
(* Program *)
program ::= item*

item ::= function_def
       | type_def
       | const_def
       | use_statement
       | resource_def
       | impl_block

(* Functions *)
function_def ::= 'fn' identifier type_params? '(' param_list? ')' return_type? resource_annotation? block

param_list ::= param ( ',' param )*
param ::= identifier ':' type

return_type ::= '->' type

type_params ::= '<' identifier ( ',' identifier )* '>'

resource_annotation ::= '@requires' '(' resource_req ( ',' resource_req )* ')'
                     | '@provides' '(' resource_prov ( ',' resource_prov )* ')'

resource_req ::= identifier ':' expression
resource_prov ::= identifier ':' expression

(* Types *)
type_def ::= 'type' identifier type_params? '=' type
           | 'struct' identifier type_params? '{' field_list '}'
           | 'enum' identifier type_params? '{' variant_list '}'

field_list ::= field ( ',' field )*
field ::= identifier ':' type

variant_list ::= variant ( ',' variant )*
variant ::= identifier ( '(' type_list ')' )?

type ::= primitive_type
       | identifier type_args?
       | '(' type_list ')'
       | '[' type ']'
       | 'fn' '(' type_list ')' '->' type
       | type '+' type
       | type '-' type
       | type '*' type
       | type '/' type

type_list ::= type ( ',' type )*
type_args ::= '<' type_list '>'

primitive_type ::= 'Int' | 'Float' | 'Bool' | 'String' | 'Unit'

(* Constants *)
const_def ::= 'const' identifier ':' type '=' expression

(* Use Statements *)
use_statement ::= 'use' path ( '::' '{' identifier_list '}' )?

path ::= identifier ( '::' identifier )*
identifier_list ::= identifier ( ',' identifier )*

(* Resources *)
resource_def ::= 'resource' identifier '{' resource_config '}'

resource_config ::= resource_field ( ',' resource_field )*
resource_field ::= 'dimension' ':' type
                 | 'budget' ':' expression
                 | 'shadow' ':' expression

(* Adaptive Blocks *)
adaptive_block ::= 'adaptive' identifier '{' adaptive_option ( ',' adaptive_option )* '}'

adaptive_option ::= identifier ':' block

(* Implementations *)
impl_block ::= 'impl' type_params? type ( 'for' type )? '{' impl_item* '}'

impl_item ::= function_def

(* Statements *)
statement ::= let_statement
            | expression_statement
            | item

let_statement ::= 'let' 'mut'? identifier ( ':' type )? '=' expression

expression_statement ::= expression

(* Expressions *)
expression ::= literal
             | identifier
             | '(' expression ')'
             | expression binary_op expression
             | unary_op expression
             | expression '.' identifier
             | expression '[' expression ']'
             | expression '(' arg_list? ')'
             | if_expression
             | match_expression
             | block
             | for_expression
             | while_expression
             | adaptive_block
             | return_expression
             | break_expression
             | continue_expression

literal ::= integer | float | string | dimensional_literal | bool_literal

bool_literal ::= 'true' | 'false'

binary_op ::= '+' | '-' | '*' | '/' | '%' | '^'
           | '==' | '!=' | '<' | '>' | '<=' | '>='
           | '&&' | '||'
           | '&' | '|' | '^' | '<<' | '>>'

unary_op ::= '-' | '!' | '&' | '*'

arg_list ::= expression ( ',' expression )*

if_expression ::= 'if' expression block ( 'else' ( block | if_expression ) )?

match_expression ::= 'match' expression '{' match_arm ( ',' match_arm )* '}'

match_arm ::= pattern ( 'if' expression )? '=>' expression

pattern ::= literal
          | identifier
          | '_'
          | identifier '(' pattern_list ')'
          | '(' pattern_list ')'

pattern_list ::= pattern ( ',' pattern )*

for_expression ::= 'for' identifier 'in' expression block

while_expression ::= 'while' expression block

return_expression ::= 'return' expression?

break_expression ::= 'break' expression?

continue_expression ::= 'continue'

block ::= '{' statement* expression? '}'
```

### Example Programs

**Hello World:**
```eclexia
fn main() {
    print("Hello, Eclexia!");
}
```

**Factorial:**
```eclexia
fn factorial(n: Int) -> Int {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}
```

**Resource-Aware Computation:**
```eclexia
resource energy { budget: 1000J }

fn expensive_compute() @requires(energy: 500J) -> Int {
    // Computation...
    42
}

fn main() {
    let result = expensive_compute();
    print(result);
}
```

**Adaptive Execution:**
```eclexia
adaptive sort {
    fast: { quicksort(data) @requires(time: 10ms) },
    slow: { bubblesort(data) @requires(time: 100ms) },
}
```

---

## Type System

### Type Inference Rules

Eclexia uses bidirectional type checking. Judgment notation: `Γ ⊢ e : τ`

**Variable:**
```
(x : τ) ∈ Γ
───────────── (Var)
Γ ⊢ x ↑ τ
```

**Integer Literal:**
```
───────────────── (Int)
Γ ⊢ n ↑ Int
```

**Float Literal:**
```
───────────────── (Float)
Γ ⊢ f ↑ Float
```

**String Literal:**
```
────────────────── (String)
Γ ⊢ s ↑ String
```

**Function Application:**
```
Γ ⊢ f ↑ τ₁ → τ₂    Γ ⊢ e ↓ τ₁
─────────────────────────────── (App)
Γ ⊢ f(e) ↑ τ₂
```

**Let Binding:**
```
Γ ⊢ e₁ ↑ τ₁    Γ, x: τ₁ ⊢ e₂ ↑ τ₂
────────────────────────────────── (Let)
Γ ⊢ let x = e₁; e₂ ↑ τ₂
```

**If Expression:**
```
Γ ⊢ cond ↓ Bool    Γ ⊢ then ↑ τ    Γ ⊢ else ↑ τ
──────────────────────────────────────────────── (If)
Γ ⊢ if cond { then } else { else } ↑ τ
```

**Binary Operation:**
```
Γ ⊢ e₁ ↑ τ₁    Γ ⊢ e₂ ↑ τ₂    τ₁ ~ τ₂    op : τ₁ × τ₂ → τ₃
──────────────────────────────────────────────────────────── (BinOp)
Γ ⊢ e₁ op e₂ ↑ τ₃
```

### Dimensional Types

**Dimension Algebra:**

Base dimensions: L (length), M (mass), T (time), I (current), Θ (temperature), N (amount), J (luminosity)

Derived dimensions: Products of powers of base dimensions

**Addition Rule:**
```
Γ ⊢ e₁ : Quantity⟨D⟩    Γ ⊢ e₂ : Quantity⟨D⟩
────────────────────────────────────────────── (Add-Dim)
Γ ⊢ e₁ + e₂ : Quantity⟨D⟩
```

**Multiplication Rule:**
```
Γ ⊢ e₁ : Quantity⟨D₁⟩    Γ ⊢ e₂ : Quantity⟨D₂⟩
─────────────────────────────────────────────── (Mul-Dim)
Γ ⊢ e₁ * e₂ : Quantity⟨D₁ × D₂⟩
```

**Division Rule:**
```
Γ ⊢ e₁ : Quantity⟨D₁⟩    Γ ⊢ e₂ : Quantity⟨D₂⟩
─────────────────────────────────────────────── (Div-Dim)
Γ ⊢ e₁ / e₂ : Quantity⟨D₁ / D₂⟩
```

**Example:**
```eclexia
let distance : Length = 100m;
let time : Time = 5s;
let speed : Velocity = distance / time;  // Type: Length / Time = Velocity
```

### Generic Types

**Type Parameters:**
```eclexia
fn identity<T>(x: T) -> T { x }
```

**Trait Bounds:**
```eclexia
fn max<T: Ord>(a: T, b: T) -> T {
    if a > b { a } else { b }
}
```

**Associated Types:**
```eclexia
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}
```

### Subtyping

Subtyping relation `S <: T` means S can be used where T is expected.

**Transitivity:**
```
S <: U    U <: T
──────────────── (Sub-Trans)
S <: T
```

**Function Subtyping:**
```
T₁' <: T₁    T₂ <: T₂'
──────────────────────── (Sub-Fun)
(T₁ → T₂) <: (T₁' → T₂')
```

Arguments are contravariant, returns are covariant.

---

## Resource Semantics

### Resource Declaration

Resources are declared with dimension, budget, and shadow price function:

```eclexia
resource identifier {
    dimension: Dimension,
    budget: Expression,
    shadow: Expression,
}
```

**Example:**
```eclexia
resource energy {
    dimension: Energy,
    budget: 1000J,
    shadow: compute_energy_price(),
}
```

### Resource Annotations

Functions declare resource requirements:

```eclexia
fn f() @requires(resource: amount) { ... }
```

Multiple resources:
```eclexia
fn f() @requires(energy: 100J, time: 50ms) { ... }
```

### Shadow Price Computation

Shadow prices are computed from dual variables in linear programming:

**For binding constraints:**
```
shadow_price = λᵢ  (dual variable from LP solver)
```

**For non-binding constraints:**
```
scarcity = usage / budget
shadow_price = base_price * exp(k * scarcity)
```

Where k controls price sensitivity.

### Resource Tracking

Runtime maintains resource state:

```rust
struct ResourceState {
    budget: f64,
    usage: f64,
    shadow_price: f64,
}
```

On function call with `@requires(resource: amount)`:
1. Check `usage + amount <= budget`
2. If yes, `usage += amount`
3. Recompute `shadow_price` based on new usage

### Adaptive Selection

Adaptive blocks solve:

```
Minimize: Σᵢ (cost_i * xᵢ)
Subject to: Σᵢ xᵢ = 1  (choose exactly one)
            resource_usage_i * xᵢ <= remaining_budget  (for all resources)
            xᵢ ∈ {0, 1}
```

Where `cost_i = Σⱼ (shadow_price_j * resource_requirement_ij)`

Uses branch-and-bound integer programming.

---

## Runtime Behavior

### Execution Model

Eclexia compiles to bytecode executed by a virtual machine.

**Instruction Set:**
- `LoadConst <value>` - Push constant onto stack
- `LoadLocal <index>` - Push local variable
- `StoreLocal <index>` - Pop stack, store in local
- `Add`, `Sub`, `Mul`, `Div` - Arithmetic operations
- `Call <func_id>` - Call function
- `Return` - Return from function
- `Jump <offset>` - Unconditional jump
- `JumpIf <offset>` - Conditional jump
- `ConsumeResource <resource_id> <amount>` - Deduct resource budget

**Example:**
```eclexia
fn add(a: Int, b: Int) -> Int {
    a + b
}
```

Compiles to:
```
LoadLocal 0    // a
LoadLocal 1    // b
Add
Return
```

### Memory Model

**Value Stack:** For expression evaluation
**Call Stack:** For function calls and local variables
**Heap:** For dynamically-allocated objects (strings, arrays, etc.)

All values are 64-bit:
- Integers: i64
- Floats: f64
- Pointers: 64-bit addresses
- Booleans: 0 (false) or 1 (true)

### Resource Runtime

Runtime maintains global resource table:

```rust
struct ResourceTable {
    resources: HashMap<ResourceId, ResourceState>,
}
```

On `ConsumeResource` instruction:
1. Look up resource in table
2. Check budget constraint
3. Update usage
4. Recompute shadow price

If budget exceeded, runtime panics with `ResourceExhaustionError`.

---

## Standard Library

### Core Module (`core`)

**Types:**
- `Option<T>` - Optional value (Some or None)
- `Result<T, E>` - Fallible operation result (Ok or Err)

**Functions:**
- `print(s: String)` - Output to stdout
- `panic(msg: String)` - Abort with error message
- `assert(condition: Bool, msg: String)` - Assert condition or panic

**Option Methods:**
- `is_some(self) -> Bool`
- `is_none(self) -> Bool`
- `unwrap(self) -> T`
- `unwrap_or(self, default: T) -> T`

**Result Methods:**
- `is_ok(self) -> Bool`
- `is_err(self) -> Bool`
- `unwrap(self) -> T`
- `unwrap_err(self) -> E`
- `unwrap_or(self, default: T) -> T`

### Collections Module (`collections`)

**Vec<T>** - Dynamic array
- `new() -> Vec<T>`
- `push(&mut self, item: T)`
- `pop(&mut self) -> Option<T>`
- `len(&self) -> Int`
- `get(&self, index: Int) -> Option<T>`

**HashMap<K, V>** - Hash table
- `new() -> HashMap<K, V>`
- `insert(&mut self, key: K, value: V)`
- `get(&self, key: K) -> Option<V>`
- `remove(&mut self, key: K) -> Option<V>`
- `contains_key(&self, key: K) -> Bool`

**HashSet<T>** - Hash set
- `new() -> HashSet<T>`
- `insert(&mut self, value: T) -> Bool`
- `contains(&self, value: T) -> Bool`
- `remove(&mut self, value: T) -> Bool`

### Math Module (`math`)

**Trigonometry:**
- `sin(x: Float) -> Float`
- `cos(x: Float) -> Float`
- `tan(x: Float) -> Float`

**Exponentials:**
- `exp(x: Float) -> Float`
- `log(x: Float) -> Float`
- `pow(x: Float, y: Float) -> Float`

**Rounding:**
- `floor(x: Float) -> Float`
- `ceil(x: Float) -> Float`
- `round(x: Float) -> Float`

**Constants:**
- `PI: Float = 3.14159265358979323846`
- `E: Float = 2.71828182845904523536`

### I/O Module (`io`)

**File Operations:**
- `read_file(path: String) -> Result<String, String>`
- `write_file(path: String, contents: String) -> Result<(), String>`
- `file_exists(path: String) -> Bool`

**JSON:**
- `read_json(path: String) -> Result<Value, String>`
- `write_json(path: String, value: Value) -> Result<(), String>`

### Text Module (`text`)

**String Operations:**
- `trim(s: String) -> String`
- `split(s: String, delim: String) -> Vec<String>`
- `join(parts: Vec<String>, delim: String) -> String`
- `to_lowercase(s: String) -> String`
- `to_uppercase(s: String) -> String`
- `contains(s: String, needle: String) -> Bool`
- `starts_with(s: String, prefix: String) -> Bool`
- `ends_with(s: String, suffix: String) -> Bool`

### Time Module (`time`)

**Duration:**
- `from_secs(secs: Float) -> Duration`
- `from_millis(millis: Int) -> Duration`
- `as_secs(self) -> Float`
- `as_millis(self) -> Int`

**Instant:**
- `now() -> Instant`
- `elapsed(self) -> Duration`
- `duration_since(self, earlier: Instant) -> Duration`

**Functions:**
- `sleep(duration: Duration)`
- `measure<T>(f: fn() -> T) -> (T, Duration)`

---

## Appendix: Reserved for Future Use

Keywords reserved but not yet implemented:
- `async`, `await` - Asynchronous programming
- `unsafe` - Unsafe operations
- `move` - Ownership transfer
- `ref` - Reference types
- `mod` - Module system
- `where` - Trait constraints

---

## References

1. **Type System:** Pierce, B. C. (2002). *Types and Programming Languages*. MIT Press.
2. **Shadow Pricing:** Dantzig, G. B., & Thapa, M. N. (1997). *Linear Programming 1: Introduction*. Springer.
3. **Dimensional Analysis:** Buckingham, E. (1914). "On Physically Similar Systems; Illustrations of the Use of Dimensional Equations." *Physical Review*.
4. **Resource-Aware Computing:** Hoffmann, J., & Hofmann, M. (2010). "Amortized Resource Analysis with Polymorphic Recursion and Partial Big-Step Operational Semantics." *APLAS*.

---

**Document Version:** 1.0.0
**Eclexia Version:** 0.1.0
**License:** PMPL-1.0-or-later
**Copyright:** 2025 Jonathan D.A. Jewell
