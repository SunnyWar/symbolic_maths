# symbolic_maths

**Automatically simplify mathematical expressions at compile time.**

A Rust proc-macro that uses symbolic mathematics (via the [egg](https://egraphs-good.github.io/) library) to simplify your numeric expressions before they run, giving you cleaner code and potentially better performance.

---

## Why use this?

Mathematical identities like `sin²(x) + cos²(x) = 1` are always true, but writing them explicitly in code clutters your logic and wastes CPU cycles. This macro:

- **Simplifies expressions automatically** - Write natural mathematical code, get optimized runtime code
- **Catches errors early** - Mathematical simplifications happen at compile time
- **Makes code clearer** - Express your intent mathematically without worrying about optimization

---

## Example

**Without the macro:**
```rust
fn compute(x: f32) -> f32 {
    2.0 * x + x.sin().powi(2) + x.cos().powi(2)
}
// Runtime: Computes sin(x), cos(x), squares both, adds them → wastes cycles
```

**With the macro:**
```rust
#[sym_math]
fn compute(x: f32) -> f32 {
    2.0 * x + x.sin().powi(2) + x.cos().powi(2)
}
// Compiles to: 2.0 * x + 1.0
// The macro recognized sin²(x) + cos²(x) = 1 and simplified it!
```

**Result:** The function runs faster and the generated code is cleaner.

---

## Quick Start

**1. Add to your `Cargo.toml`:**
```toml
[dependencies]
symbolic_maths = { path = "../symbolic_maths_macro" }
```

**2. Use the macro:**
```rust
use symbolic_maths::sym_math;

#[sym_math]
fn my_function(x: f32) -> f32 {
    x.sin().powi(2) + x.cos().powi(2)  // Simplifies to: 1.0
}
```

**3. Build and run:**
```bash
cargo build
cargo run
```

---

## What gets simplified?

Currently supports:
- **Trigonometric identities**: `sin²(x) + cos²(x) → 1`
- **Basic algebra**: `x * 1 → x`, `x + 0 → x`, `x^1 → x`

Supports these expression types:
- Numeric literals: `42`, `3.14`
- Variables: function parameters
- Binary operations: `+`, `*`, `-`
- Method calls: `.sin()`, `.cos()`, `.powi(n)`
- Function calls: `foo(x)`, `math::bar(y)`

---

## Requirements

- **Single expression body**: Function must be a single expression (no statements)
- **No trailing semicolon**: Write `x + 1` not `x + 1;`

**Example of correct usage:**
```rust
#[sym_math]
fn good(x: f32) -> f32 {
    x.sin().powi(2) + x.cos().powi(2)  // ✓ Single expression
}
```

**Example of incorrect usage:**
```rust
#[sym_math]
fn bad(x: f32) -> f32 {
    let y = x * 2.0;  // ✗ Has statements
    y + 1.0
}
```

---

## How it works (brief)

1. **Parse**: Reads your function at compile time
2. **Simplify**: Uses symbolic math (e-graphs via egg) to find the simplest equivalent form
3. **Generate**: Replaces your function body with the optimized version

All of this happens during compilation - zero runtime overhead!

---

## Testing
```bash
# Run all tests
cargo test

# Run integration tests
cargo test --test integration_tests

# Run example
cargo run -p example_runtime
```

---

## Future Work

Potential enhancements to make the macro more powerful and broadly applicable:

**More mathematical identities:**
- Double angle formulas: `sin(2x) = 2·sin(x)·cos(x)`
- Pythagorean variants: `1 + tan²(x) = sec²(x)`
- Sum/difference formulas for trig functions
- Logarithm rules: `log(a·b) = log(a) + log(b)`
- Exponent rules: `x^a · x^b = x^(a+b)`

**Algebraic simplifications:**
- Common factor extraction: `a·x + a·y → a·(x + y)`
- Polynomial simplification: `(x + 1)² → x² + 2x + 1`
- Fraction simplification
- Constant folding for complex expressions

**Expression support:**
- Multi-statement functions (analyze final expression)
- Control flow (if/else, match) with symbolic conditions
- Loops with compile-time known bounds
- Array/vector operations

**Advanced features:**
- User-defined rewrite rules via attributes
- Optimization hints (speed vs. numerical stability)
- Configurable simplification aggressiveness
- Support for integer and generic numeric types
- Partial evaluation with known constant inputs

**Developer experience:**
- Better error messages with suggestions
- Show simplified result in compiler output or documentation
- IDE integration for live simplification preview
- Benchmarking helpers to measure actual performance gains

**Performance:**
- Parallel simplification for large expressions
- Caching of simplified expressions across builds
- Profile-guided optimization based on runtime patterns

---

## License

MIT License - see [LICENSE](LICENSE) file for details.