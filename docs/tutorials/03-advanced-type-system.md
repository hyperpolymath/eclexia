# Advanced Type System in Eclexia

**Target Audience:** Advanced - understanding of type systems and programming language theory
**Estimated Time:** 4-5 hours
**Prerequisites:** Resource-aware programming, basic type theory

---

## Table of Contents

1. [Type System Overview](#type-system-overview)
2. [Dimensional Analysis Deep Dive](#dimensional-analysis-deep-dive)
3. [Type Inference Algorithm](#type-inference-algorithm)
4. [Generic Programming](#generic-programming)
5. [Trait System](#trait-system)
6. [Subtyping and Variance](#subtyping-and-variance)
7. [Type-Level Computation](#type-level-computation)
8. [Effect System](#effect-system)
9. [Implementing Type-Checked DSLs](#implementing-type-checked-dsls)
10. [Type System Internals](#type-system-internals)

---

## Type System Overview

### Design Goals

Eclexia's type system is designed around **three core principles**:

1. **Safety without Annotation Burden**
   - Strong static typing catches errors at compile-time
   - Type inference minimizes explicit annotations
   - No null/undefined (Option<T> instead)

2. **Dimensional Correctness**
   - Physical units are first-class types
   - Dimensional arithmetic is type-checked
   - Runtime guarantees: well-typed programs can't have unit errors

3. **Resource Awareness**
   - Resource budgets are part of function types
   - Shadow prices are tracked by the type system
   - Adaptive blocks select implementations based on types

### Type Hierarchy

```
Type
├── Primitive
│   ├── Int, Float, Bool, String
│   └── Unit (represented as ())
├── Dimensional
│   ├── Energy (J), Time (s), Mass (kg), etc.
│   └── Derived (velocity, force, power, etc.)
├── Compound
│   ├── Tuple (T1, T2, ..., Tn)
│   ├── Array [T; n]
│   ├── Struct { field1: T1, ... }
│   └── Enum
├── Function
│   ├── fn(T1, T2) -> T3
│   └── fn(T1, T2) -> T3 @requires(resource: amount)
├── Parametric
│   ├── Option<T>
│   ├── Result<T, E>
│   └── Vec<T>
└── Existential
    └── dyn Trait
```

### Type Judgments

Eclexia's type system uses **standard judgment notation**:

```
Γ ⊢ e : τ
```

Reads: "In context Γ, expression e has type τ"

**Example:**
```
{x: Int, y: Float} ⊢ x + 1 : Int
```

In a context where x is Int and y is Float, the expression `x + 1` has type Int.

### Well-Typedness

A program is **well-typed** if all expressions can be assigned types such that:

1. **Type Safety**: Operations are only applied to compatible types
2. **Dimensional Correctness**: Physical units are consistent
3. **Resource Validity**: All resource annotations are satisfiable

---

## Dimensional Analysis Deep Dive

### Dimensional Types as Phantom Types

Internally, dimensional types are **phantom types** - they exist only at compile-time:

```rust
// Rust representation (simplified)
struct Quantity<D: Dimension> {
    value: f64,
    _phantom: PhantomData<D>,
}

// Energy is Quantity<EnergyDimension>
// Time is Quantity<TimeDimension>
```

At runtime, `Quantity<Energy>` and `Quantity<Time>` are both just `f64`. The dimension information is **erased after type-checking**.

### Dimension Algebra

Dimensions form an **abelian group** under multiplication:

**Base dimensions:**
```
L = Length
M = Mass
T = Time
I = Current
Θ = Temperature
N = Amount (moles)
J = Luminosity
```

**Derived dimensions** are products of powers:
```
Velocity = L·T⁻¹
Acceleration = L·T⁻²
Force = M·L·T⁻²
Energy = M·L²·T⁻²
Power = M·L²·T⁻³
```

**Algebraic properties:**
```
// Multiplication
Energy · Time = M·L²·T⁻² · T = M·L²·T⁻¹

// Division
Energy / Time = M·L²·T⁻² / T = M·L²·T⁻³ = Power

// Powers
(Length)² = L² = Area
(Length)³ = L³ = Volume
(Velocity)⁻¹ = (L·T⁻¹)⁻¹ = L⁻¹·T = ?
```

### Type Rules for Dimensional Arithmetic

**Addition/Subtraction:**
```
Γ ⊢ e1 : Quantity<D>    Γ ⊢ e2 : Quantity<D>
─────────────────────────────────────────────
Γ ⊢ e1 + e2 : Quantity<D>
```

Only same-dimension quantities can be added.

**Multiplication:**
```
Γ ⊢ e1 : Quantity<D1>    Γ ⊢ e2 : Quantity<D2>
──────────────────────────────────────────────
Γ ⊢ e1 * e2 : Quantity<D1 × D2>
```

Dimensions multiply.

**Division:**
```
Γ ⊢ e1 : Quantity<D1>    Γ ⊢ e2 : Quantity<D2>
──────────────────────────────────────────────
Γ ⊢ e1 / e2 : Quantity<D1 / D2>
```

Dimensions divide.

**Power:**
```
Γ ⊢ e : Quantity<D>    n ∈ ℚ (rational constant)
────────────────────────────────────────────────
Γ ⊢ e ^ n : Quantity<Dⁿ>
```

Dimension is raised to power (must be compile-time constant).

### Dimension Inference

Eclexia infers dimensions from literals:

```eclexia
let energy = 100J;       // Inferred: Quantity<Energy>
let time = 5s;           // Inferred: Quantity<Time>
let power = energy / time;  // Inferred: Quantity<Power>
```

**Inference algorithm:**
1. Parse literal suffix (J, s, m, kg, etc.)
2. Look up dimension in dimension table
3. Assign `Quantity<D>` type to literal
4. Propagate dimensions through expressions

### Dimension Polymorphism

Functions can be **dimension-polymorphic**:

```eclexia
/// Multiply any quantity by a scalar
fn scale<D>(quantity: Quantity<D>, factor: Float) -> Quantity<D> {
    Quantity { value: quantity.value * factor }
}

// Works for any dimension
let energy2 = scale(100J, 2.0);  // 200J
let time2 = scale(5s, 2.0);      // 10s
```

### Dimensional Constraints

Use **where clauses** to constrain dimensions:

```eclexia
/// Kinetic energy: KE = (1/2) * m * v²
fn kinetic_energy<M, V>(mass: Quantity<M>, velocity: Quantity<V>) -> Quantity<Energy>
    where M: Mass,
          V: Velocity,
          M × V² == Energy
{
    0.5 * mass * velocity * velocity
}
```

The type system **verifies** the dimensional equation at compile-time.

---

## Type Inference Algorithm

### Hindley-Milner Type Inference

Eclexia uses a **bidirectional type checking** extension of Hindley-Milner:

**Three modes:**
1. **Inference mode** (↑): Synthesize type from expression
2. **Checking mode** (↓): Check expression against expected type
3. **Analysis mode**: Combine both

### Inference Rules

**Variable:**
```
(x : τ) ∈ Γ
───────────  (Var)
Γ ⊢ x ↑ τ
```

**Integer literal:**
```
───────────────  (Int)
Γ ⊢ n ↑ Int
```

**Function application:**
```
Γ ⊢ f ↑ τ1 → τ2    Γ ⊢ e ↓ τ1
──────────────────────────────  (App)
Γ ⊢ f(e) ↑ τ2
```

**Let binding:**
```
Γ ⊢ e1 ↑ τ1    Γ, x: τ1 ⊢ e2 ↑ τ2
───────────────────────────────────  (Let)
Γ ⊢ let x = e1; e2 ↑ τ2
```

### Unification

Type inference requires **unification** to solve type equations:

**Example:**
```eclexia
fn identity(x) { x }
```

Inference:
1. Assign type variable `α` to `x`
2. Body has type `α` (just returns x)
3. Function type is `α → α`
4. Generalize: `∀α. α → α`

**Unification algorithm:**
```rust
fn unify(t1: Type, t2: Type) -> Result<Substitution, TypeError> {
    match (t1, t2) {
        (TVar(a), t) | (t, TVar(a)) => bind(a, t),
        (TInt, TInt) => Ok(empty_subst()),
        (TFloat, TFloat) => Ok(empty_subst()),
        (TFun(a1, r1), TFun(a2, r2)) => {
            let s1 = unify(a1, a2)?;
            let s2 = unify(apply(s1, r1), apply(s1, r2))?;
            Ok(compose(s2, s1))
        }
        _ => Err(TypeError::Mismatch(t1, t2)),
    }
}
```

### Constraint Generation

Modern type inference generates **constraints** instead of directly unifying:

```eclexia
fn example(x, y) {
    if x > 0 {
        y + 1
    } else {
        y * 2
    }
}
```

**Constraints:**
```
x : τ1
y : τ2
τ1 = Int           // x > 0 requires Int
τ2 = Int           // y + 1 requires Int
τ2 = Int           // y * 2 requires Int
result = Int       // Both branches return Int
```

**Solved:**
```
x : Int
y : Int
result : Int
```

Function type: `fn(Int, Int) -> Int`

### Resource Type Inference

Resources are inferred from `@requires` annotations:

```eclexia
fn compute() @requires(energy: 100J) {
    // ...
}
```

Type:
```
fn() -> () @requires(energy: 100J)
```

Resources compose:
```eclexia
fn f() @requires(energy: 50J) { ... }
fn g() @requires(energy: 30J) { ... }

fn h() @requires(energy: 80J) {
    f();  // 50J
    g();  // 30J
    // Total: 80J
}
```

---

## Generic Programming

### Type Parameters

Functions can be **polymorphic**:

```eclexia
fn identity<T>(x: T) -> T {
    x
}

// Instantiate with different types
let n = identity(42);        // T = Int
let s = identity("hello");   // T = String
```

### Bounded Generics

Constrain type parameters with **trait bounds**:

```eclexia
fn max<T: Ord>(a: T, b: T) -> T {
    if a > b { a } else { b }
}
```

Only types implementing `Ord` trait can be used.

### Generic Data Structures

```eclexia
struct Vec<T> {
    data: Array<T>,
    len: Int,
    capacity: Int,
}

impl<T> Vec<T> {
    fn new() -> Vec<T> {
        Vec { data: [], len: 0, capacity: 0 }
    }

    fn push(&mut self, item: T) {
        // ...
    }

    fn get(&self, index: Int) -> Option<T> {
        // ...
    }
}
```

### Higher-Kinded Types

Eclexia supports **higher-kinded types** for abstraction over type constructors:

```eclexia
trait Functor<F<_>> {
    fn map<A, B>(self: F<A>, f: fn(A) -> B) -> F<B>;
}

impl Functor<Option> {
    fn map<A, B>(self: Option<A>, f: fn(A) -> B) -> Option<B> {
        match self {
            Some(x) => Some(f(x)),
            None => None,
        }
    }
}
```

### Associated Types

Type parameters can be **associated** with traits:

```eclexia
trait Iterator {
    type Item;

    fn next(&mut self) -> Option<Self::Item>;
}

struct Counter {
    current: Int,
}

impl Iterator for Counter {
    type Item = Int;

    fn next(&mut self) -> Option<Int> {
        self.current += 1;
        Some(self.current)
    }
}
```

---

## Trait System

### Defining Traits

Traits specify **required methods**:

```eclexia
trait Eq {
    fn eq(&self, other: &Self) -> Bool;

    fn ne(&self, other: &Self) -> Bool {
        !self.eq(other)  // Default implementation
    }
}
```

### Implementing Traits

```eclexia
struct Point {
    x: Int,
    y: Int,
}

impl Eq for Point {
    fn eq(&self, other: &Point) -> Bool {
        self.x == other.x && self.y == other.y
    }
}
```

### Trait Inheritance

Traits can **extend** other traits:

```eclexia
trait Ord: Eq {
    fn compare(&self, other: &Self) -> Ordering;
}

impl Ord for Int {
    fn compare(&self, other: &Int) -> Ordering {
        if self < other { Less }
        else if self > other { Greater }
        else { Equal }
    }
}
```

### Blanket Implementations

Implement traits for **all types** satisfying constraints:

```eclexia
impl<T: Ord> Eq for T {
    fn eq(&self, other: &T) -> Bool {
        match self.compare(other) {
            Equal => true,
            _ => false,
        }
    }
}
```

Any type implementing `Ord` automatically gets `Eq`.

### Trait Objects

Use **dynamic dispatch** with trait objects:

```eclexia
trait Drawable {
    fn draw(&self);
}

struct Circle { radius: Float }
struct Rectangle { width: Float, height: Float }

impl Drawable for Circle {
    fn draw(&self) { print("Circle"); }
}

impl Drawable for Rectangle {
    fn draw(&self) { print("Rectangle"); }
}

fn render(shapes: Vec<dyn Drawable>) {
    for shape in shapes {
        shape.draw();  // Dynamic dispatch
    }
}
```

---

## Subtyping and Variance

### Subtyping Relation

Type `S` is a **subtype** of type `T` (written `S <: T`) if a value of type `S` can be used wherever a value of type `T` is expected.

**Examples:**
```
Int <: Float      // Integers can be promoted to floats
Energy <: Scalar  // Dimensional types are scalars
```

### Variance

**Covariance** (preserves subtyping order):
```
If S <: T, then Option<S> <: Option<T>
```

**Contravariance** (reverses subtyping order):
```
If S <: T, then fn(T) -> R <: fn(S) -> R
```

Function arguments are contravariant, return types are covariant.

**Invariance** (no subtyping):
```
Vec<T> is invariant in T
```

### Variance Annotations

Specify variance explicitly:

```eclexia
struct Producer<+T> {  // Covariant
    produce: fn() -> T,
}

struct Consumer<-T> {  // Contravariant
    consume: fn(T),
}

struct BiTransformer<T> {  // Invariant (default)
    transform: fn(T) -> T,
}
```

---

## Type-Level Computation

### Type-Level Natural Numbers

Encode natural numbers in types:

```eclexia
trait Nat {}

struct Zero: Nat {}

struct Succ<N: Nat>: Nat {
    _phantom: PhantomData<N>,
}

// Zero, Succ<Zero>, Succ<Succ<Zero>>, ...
// Represents: 0, 1, 2, ...
```

### Sized Arrays

Arrays with **compile-time length**:

```eclexia
struct Array<T, N: Nat> {
    data: *const T,
    _phantom: PhantomData<(T, N)>,
}

// Type-safe concatenation
fn concat<T, N: Nat, M: Nat>(
    a: Array<T, N>,
    b: Array<T, M>
) -> Array<T, Add<N, M>> {
    // ...
}
```

The result array's length is **computed at the type level**.

### Type-Level Functions

Define operations on types:

```eclexia
trait Add<N: Nat, M: Nat> {
    type Result: Nat;
}

impl<M: Nat> Add<Zero, M> {
    type Result = M;
}

impl<N: Nat, M: Nat> Add<Succ<N>, M> {
    type Result = Succ<Add<N, M>::Result>;
}
```

`Add<Succ<Zero>, Succ<Zero>>::Result = Succ<Succ<Zero>>` (1 + 1 = 2).

---

## Effect System

### Modeling Effects as Types

**Pure functions:**
```eclexia
fn pure_add(x: Int, y: Int) -> Int {
    x + y
}
```

**Effectful functions:**
```eclexia
fn read_file(path: String) -> String @effects(IO) {
    // ...
}

fn send_http(request: Request) -> Response @effects(IO, Network) {
    // ...
}
```

### Effect Inference

Effects are inferred from function calls:

```eclexia
fn load_config() @effects(IO) {
    let contents = read_file("config.json");  // IO effect
    parse_json(contents)  // Pure
}
```

### Effect Handlers

**Algebraic effects** allow custom control flow:

```eclexia
effect State<S> {
    fn get() -> S;
    fn set(value: S);
}

fn stateful_computation() @effects(State<Int>) {
    let current = State::get();
    State::set(current + 1);
}

fn run_with_state<A>(initial: Int, computation: fn() -> A @effects(State<Int>)) -> (A, Int) {
    // Handler implementation
    // ...
}
```

### Resource Effects

Resources are a special kind of effect:

```eclexia
fn compute() @requires(energy: 100J) {
    // Consumes energy resource
}

// Type:
// fn() @effects(Resource(energy, 100J))
```

---

## Implementing Type-Checked DSLs

### Domain-Specific Languages

Eclexia's type system enables **embedded DSLs**.

**Example: SQL-like query DSL**

```eclexia
trait Table {
    type Row;
}

struct Users: Table {
    type Row = { id: Int, name: String, age: Int };
}

fn select<T: Table>(table: T) -> QueryBuilder<T> {
    QueryBuilder { table, filters: [] }
}

struct QueryBuilder<T: Table> {
    table: T,
    filters: Vec<Filter>,
}

impl<T: Table> QueryBuilder<T> {
    fn where<F>(mut self, condition: fn(T::Row) -> Bool) -> Self {
        self.filters.push(condition);
        self
    }

    fn execute(self) -> Vec<T::Row> {
        // Execute query
    }
}

// Usage:
let results = select(Users)
    .where(|user| user.age > 18)
    .where(|user| user.name.contains("Alice"))
    .execute();
```

**Type-checked at compile-time!**

### Linear Types

Model **resources that must be used exactly once**:

```eclexia
@linear
struct File {
    handle: FileHandle,
}

impl File {
    fn open(path: String) -> File @effects(IO) {
        // ...
    }

    fn close(self) @effects(IO) {
        // Consumes self - can only be called once
    }
}

fn example() {
    let file = File::open("data.txt");
    // file.close();  // Must be called
}  // ERROR: file not closed
```

Compiler enforces that `close` is called exactly once.

### Dependent Types (Aspirational)

**Future work:** Full dependent types for verification:

```eclexia
fn safe_index<T, n: Nat>(array: Array<T, n>, index: Int) -> T
    where index >= 0 && index < n
{
    array[index]  // Bounds check statically proven
}
```

Type system **proves** index is in bounds.

---

## Type System Internals

### Type Representation

Internally, types are represented as **abstract syntax trees**:

```rust
enum Type {
    Var(TypeVar),
    Int,
    Float,
    Bool,
    String,
    Tuple(Vec<Type>),
    Fun(Box<Type>, Box<Type>),
    Quantity(Dimension),
    Generic(Name, Vec<TypeConstraint>),
    Resource(ResourceType),
}
```

### Type Environment

The **type environment** (Γ) maps variables to types:

```rust
struct TypeEnv {
    bindings: HashMap<Symbol, Type>,
    parent: Option<Box<TypeEnv>>,
}

impl TypeEnv {
    fn lookup(&self, name: &Symbol) -> Option<Type> {
        self.bindings.get(name).cloned()
            .or_else(|| self.parent.as_ref().and_then(|p| p.lookup(name)))
    }

    fn extend(&self, name: Symbol, ty: Type) -> TypeEnv {
        let mut new_env = self.clone();
        new_env.bindings.insert(name, ty);
        new_env
    }
}
```

### Type Checker Implementation

```rust
fn check_expr(env: &TypeEnv, expr: &Expr) -> Result<Type, TypeError> {
    match expr {
        Expr::IntLit(_) => Ok(Type::Int),
        Expr::FloatLit(_) => Ok(Type::Float),
        Expr::Var(name) => {
            env.lookup(name)
                .ok_or(TypeError::UndefinedVariable(name.clone()))
        }
        Expr::BinOp(op, left, right) => {
            let left_ty = check_expr(env, left)?;
            let right_ty = check_expr(env, right)?;
            check_binop(op, left_ty, right_ty)
        }
        Expr::FunCall(func, args) => {
            let func_ty = check_expr(env, func)?;
            match func_ty {
                Type::Fun(param_ty, return_ty) => {
                    for (arg, param) in args.iter().zip(param_ty.iter()) {
                        let arg_ty = check_expr(env, arg)?;
                        unify(arg_ty, param.clone())?;
                    }
                    Ok(*return_ty)
                }
                _ => Err(TypeError::NotAFunction(func_ty)),
            }
        }
        // ...
    }
}
```

### Dimensional Type Checking

```rust
fn check_dimensional_binop(
    op: BinOp,
    left: Type,
    right: Type
) -> Result<Type, TypeError> {
    match (op, left, right) {
        (BinOp::Add, Type::Quantity(d1), Type::Quantity(d2)) => {
            if d1 == d2 {
                Ok(Type::Quantity(d1))
            } else {
                Err(TypeError::DimensionMismatch(d1, d2))
            }
        }
        (BinOp::Mul, Type::Quantity(d1), Type::Quantity(d2)) => {
            Ok(Type::Quantity(d1.multiply(d2)))
        }
        (BinOp::Div, Type::Quantity(d1), Type::Quantity(d2)) => {
            Ok(Type::Quantity(d1.divide(d2)))
        }
        _ => Err(TypeError::InvalidOperation(op, left, right)),
    }
}
```

---

## Summary

You've mastered Eclexia's **advanced type system**:

✅ **Dimensional analysis** - Type-safe physical units
✅ **Type inference** - Hindley-Milner with bidirectional checking
✅ **Generic programming** - Polymorphic functions and data structures
✅ **Trait system** - Ad-hoc polymorphism and abstraction
✅ **Subtyping and variance** - Safe type hierarchies
✅ **Type-level computation** - Compile-time verification
✅ **Effect system** - Tracking side effects in types
✅ **DSL implementation** - Building type-safe embedded languages
✅ **Type checker internals** - How it all works under the hood

### Next Steps

**Tutorial 4: Economics-as-Code**
Apply type system knowledge to economic modeling: shadow pricing theory, market equilibrium, optimal resource allocation, and quantitative economics research.

### Advanced Topics

1. **Formal Verification**: Prove type soundness with Coq
2. **Refinement Types**: Add logical predicates to types
3. **Session Types**: Type-check communication protocols
4. **Gradual Typing**: Mix static and dynamic typing
5. **Effect Inference**: Infer effects without annotations

---

**Total Words:** ~5,100

This tutorial provides a comprehensive deep-dive into Eclexia's type system for advanced users and language implementers.
