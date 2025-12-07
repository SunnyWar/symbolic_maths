# symbolic_maths

**Automatically simplify mathematical expressions at compile time.**

A Rust proc‑macro that uses symbolic mathematics (via the [egg](https://egraphs-good.github.io/) library) to simplify numeric expressions at compile time, producing smaller, clearer, and often faster generated code.

---

### Overview

This macro rewrites a function's single expression body using a set of rewrite rules expressed as e‑graph rewrites. It is **conservative by default**: only safe, type‑agnostic simplifications are applied. More aggressive algebraic transforms are planned for future releases but are **not** part of the current implementation.

**Key benefits**

- **Smaller generated code** — removes redundant operations and folds constants.  
- **Faster runtime** — fewer operations and simpler expressions help the optimizer.  
- **Compile‑time simplification** — transformations happen during compilation, not at runtime.

**Simple example**

Without the macro:
```rust
fn compute(x: f32) -> f32 {
    2.0 * x + x.sin().powi(2) + x.cos().powi(2)
}
```

With the macro:
```rust
use symbolic_maths::sym_math;

#[sym_math]
fn compute(x: f32) -> f32 {
    2.0 * x + x.sin().powi(2) + x.cos().powi(2)
}
// The macro simplifies sin^2 + cos^2 to 1, producing code equivalent to:
// 2.0 * x + 1.0
```

---

### Quick Start and Usage

**Add to your Cargo.toml**
```toml
[dependencies]
symbolic_maths = { path = "../symbolic_maths_macro" }
```

**Use the macro**
```rust
use symbolic_maths::sym_math;

#[sym_math]
fn my_function(x: f32) -> f32 {
    x.sin().powi(2) + x.cos().powi(2)  // Simplifies to: 1.0
}
```

**Build and run**
```bash
cargo build
cargo run
```

**Important usage constraints**

- **Single expression body**: The function must be a single expression (no statements).  
- **No trailing semicolon**: The function body must be an expression (e.g., `x + 1`, not `x + 1;`).  
- **Current attribute form**: Use `#[sym_math]`. There are **no** attribute options in this release.

**Correct example**
```rust
#[sym_math]
fn good(x: f32) -> f32 {
    x.sin().powi(2) + x.cos().powi(2)
}
```

**Incorrect example**
```rust
#[sym_math]
fn bad(x: f32) -> f32 {
    let y = x * 2.0;  // ✗ statements are not supported
    y + 1.0
}
```

---

### Rules and Safety

The macro applies a **conservative, type‑agnostic** set of rewrite rules that are safe to apply to arbitrary numeric code. Example rules included in the current release:

**Trigonometric identity**
- `(+ (pow (sin ?x) 2) (pow (cos ?x) 2)) -> 1`

**Basic algebra**
- `(pow ?a 1) -> ?a`
- `(* 1 ?a) -> ?a`
- `(+ 0 ?a) -> ?a`

**Safe simplifiers added**
- `(log (exp ?x)) -> ?x`
- `(log 1) -> 0`
- `(* ?a 0) -> 0`

**What the macro does**
- **Constant folding**: evaluates constant arithmetic where possible.  
- **Canonicalization**: normalizes shapes using commutativity, associativity, and flattening so equivalent expressions match reliably.  
- **Extraction**: after rewriting, the macro extracts a compact expression to generate the final function body.

**What the macro does not do (yet)**
- The macro does **not** include aggressive algebraic transforms (for example, combining `log(a) + log(b)` into `log(a*b)`) in the default rule set. Those transforms can change expression shape and require domain assumptions (e.g., positivity) and are planned as opt‑in features in future releases.

**Safety note**
- Algebraic transforms that require domain assumptions (such as positivity for logarithms) are **not** applied automatically. If you need such transforms, they will be provided as explicit, opt‑in features in a later release.

---

### Testing

Run tests:
```bash
cargo test
cargo test --test integration_tests
cargo run -p example_runtime
```

**Recommended test style**

Prefer semantic equivalence checks rather than asserting a specific extracted shape. Use a helper like `assert_simplifies_equivalent` to compare canonical simplified forms. This keeps tests robust to extractor cost heuristics and future rule additions.

Example tests:
```rust
#[test]
fn test_log_exp_simplifies() {
    assert_simplifies_equivalent("(log (exp x))", "x");
}

#[test]
fn test_log_1_simplifies_to_zero() {
    assert_simplifies_equivalent("(log 1)", "0");
}

#[test]
fn test_mul_0_simplifies_to_zero() {
    assert_simplifies_equivalent("(* x 0)", "0");
}
```

If you need to assert that a particular rewrite actually fired (not just that final forms are equivalent), inspect the e‑graph produced by the runner and use `Pattern::search` to check for the presence of the RHS.

---

### Future Work and License

**Planned enhancements**
- More mathematical identities (double angle, sum/difference, exponent rules).  
- Algebraic simplifiers (factor extraction, polynomial simplification) as opt‑in features.  
- User‑defined rewrite rules via attributes.  
- Guarded rewrites and runtime checks for domain‑sensitive transforms.  
- Optional compile‑time trace output and IDE integration.  
- Caching and parallel simplification for large expressions.

**License**

MIT License — see the `LICENSE` file for details.

---

If you want, I can also produce a small README patch file you can apply directly, or open a branch with this README update and provide the exact git commands to commit it locally. Which would you prefer?