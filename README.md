# symbolic_maths

A small Rust workspace demonstrating a proc‑macro that converts numeric expressions into an e‑graph, simplifies them with **egg**, and emits optimized Rust code. Includes a proc‑macro crate and an example runtime that shows how to use the `#[sym_math]` attribute.

---

## Quickstart

**Prerequisites**

- Rust toolchain installed via `rustup` (stable).

**Build and run**

```bash
# from repository root
cargo build -p symbolic_maths
cargo run -p example_runtime
```

**Clean build**

```bash
cargo clean
cargo build
```

---

## Usage

**Annotate a function**

Apply the attribute to a single‑expression function. The macro expects a single expression body without statements or a trailing semicolon.

```rust
use symbolic_maths::sym_math;

#[sym_math]
pub fn A(x: f32) -> f32 {
    x * x.sin() * x.sin() + x.cos() * x.cos()
}
```

**Notes**

- The macro replaces the function body at compile time with the simplified expression.
- Supported expression forms include numeric literals, variables, binary ops `+` and `*`, unary negation, method calls `sin`, `cos`, `powi`, and simple function calls. Unsupported forms will produce a compile error with diagnostics.

---

## How it works

**Pipeline**

1. **Parse** the annotated function using `syn`.  
2. **Convert** the `syn::Expr` into a compact s‑expression suitable for `egg` (`conv::to_rec_expr`).  
3. **Rewrite** the expression using e‑graph rules (`rewrite::simplify_rec_expr`).  
4. **Render** the simplified `RecExpr` back into Rust tokens (`conv::rec_expr_to_tokens`) and replace the function body.

**Key modules**

- `lib.rs` — proc‑macro entry point and error wrapper.  
- `conv.rs` — conversion between `syn::Expr` and s‑expressions and rendering back to Rust.  
- `rewrite.rs` — e‑graph rewrite rules and simplification pipeline.

---

## Development notes and troubleshooting

**Common issues**

- **Dependency name mismatch**: Ensure `example_runtime/Cargo.toml` references the proc‑macro package name, for example:
  ```toml
  [dependencies]
  symbolic_maths = { path = "../symbolic_maths_macro" }
  ```
  Or use an alias if the package name differs:
  ```toml
  symbolic_maths_macro = { package = "symbolic_maths", path = "../symbolic_maths_macro" }
  ```

- **Single expression requirement**: The macro requires a single expression body. If your function has statements or a trailing semicolon, the macro will emit a compile error.

- **Macro panics**: The proc‑macro wraps internal errors and emits `compile_error!` with diagnostics. If you see `custom attribute panicked`, build the macro crate directly to inspect errors:
  ```bash
  cargo build -p symbolic_maths
  ```

- **Unsupported calls**: If the converter reports unsupported calls (for example `unsupported call B`), extend `conv::expr_to_sexpr` to convert `Expr::Call` into s‑expressions and ensure `sexpr_to_tokens` renders generic calls back to Rust.

**Debugging tips**

- Add defensive checks in `conv.rs` to avoid panics and produce helpful error messages.  
- Temporarily emit intermediate s‑expressions as compile errors to inspect what the macro produced.

---

## Contributing and License

**Contributing**

- Open issues for bugs or feature requests.  
- Send focused pull requests with tests where applicable.  
- Keep proc‑macro changes small and include clear error messages.

**License**

---
