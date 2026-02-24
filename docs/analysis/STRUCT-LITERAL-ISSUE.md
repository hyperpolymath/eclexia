# Struct Literal Parsing Issue

## Problem

Struct literals in postfix position create ambiguity with block expressions:

```ecl
for x in arr { }  // Is `arr {` a struct literal or is `{}` the loop body?
```

## Current Status (95%)

✅ **Working:**
- Struct declarations: `struct Point { x: int, y: int }`
- Struct field access: `p.x`, `p.y`  
- For loops with array parameters: `for x in arr { }`

❌ **Not Working:**  
- Struct literals in expressions: `Point { x: 10, y: 20 }`

## Workaround

Use constructor functions:
```ecl
fn Point_new(x: int, y: int) -> Point {
    // Internal constructor
}
```

## Permanent Fix (Future)

Requires parser refactoring to:
1. Pass context flags through expression parsing
2. Use lookahead to disambiguate `Name { field: value }` from `Name { stmt }`
3. Or adopt Rust-style disambiguation rules

**Estimated effort:** 4-6 hours
