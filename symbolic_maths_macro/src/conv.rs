// symbolic_maths_macro/src/conv.rs
use anyhow::{Result, anyhow};
use egg::RecExpr;
use egg::SymbolLang;
use indexmap::IndexSet;
use proc_macro2::Span;
use quote::quote;
use syn::Expr;
use syn::Ident;
use syn::LitFloat;
use syn::LitInt;
use syn::{FnArg, Pat};

use crate::parser::expr_to_sexpr;
use crate::types::ConversionContext;
use crate::types::FloatTy;
use crate::types::detect_primary_float;

// ============================================================================
// STEP 1: Extract function parameters from signature
// ============================================================================

/// Return function parameter names in declaration order.
pub fn extract_param_names_ordered(sig: &syn::Signature) -> Vec<String> {
    let mut params = IndexSet::new();
    for input in &sig.inputs {
        if let FnArg::Typed(pat_type) = input {
            if let Pat::Ident(pat_ident) = &*pat_type.pat {
                params.insert(pat_ident.ident.to_string());
            }
        }
    }
    params.into_iter().collect()
}

// ============================================================================
// STEP 4: Top-level conversion function
// ============================================================================

/// Produce a RecExpr by converting the syn::Expr to an s-expression
/// and parsing it into the e-graph representation.
pub fn to_rec_expr(expr: &Expr, sig: &syn::Signature) -> Result<RecExpr<SymbolLang>> {
    let vec_params: Vec<String> = extract_param_names_ordered(sig);
    let params: IndexSet<String> = vec_params.into_iter().collect();
    let float_ty = detect_primary_float(sig); // implement or stub in detect.rs
    let ctx = ConversionContext { params, float_ty };

    let s = expr_to_sexpr(expr, &ctx)?;
    eprintln!("DEBUG: s-expression before parsing: {:?}", s);

    let rec: RecExpr<SymbolLang> = s.parse()?;
    Ok(rec)
}

// ============================================================================
// STEP 5: RecExpr to tokens conversion - broken into smaller functions
// ============================================================================

pub fn tokenize_sexpr(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();

    for ch in s.chars() {
        match ch {
            '(' | ')' => {
                if !cur.trim().is_empty() {
                    out.push(cur.trim().to_string());
                }
                cur.clear();
                out.push(ch.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.trim().is_empty() {
                    out.push(cur.trim().to_string());
                    cur.clear();
                }
            }
            c => cur.push(c),
        }
    }

    if !cur.trim().is_empty() {
        out.push(cur.trim().to_string());
    }

    out.into_iter().filter(|t| !t.is_empty()).collect()
}

/// Parse a binary s-expression like "(+ a b)" or "(* a b)" starting at `pos`.
/// Forward `float_ty` so numeric atoms are emitted with the correct float suffix.
fn parse_binary_op(
    op: &str,
    tokens: &[String],
    pos: usize,
    float_ty: FloatTy,
) -> Result<(proc_macro2::TokenStream, usize)> {
    // parse left and right operands, forwarding float_ty
    let (a, p1) = sexpr_to_tokens(tokens, pos + 2, float_ty)?;
    let (b, p2) = sexpr_to_tokens(tokens, p1, float_ty)?;

    if p2 >= tokens.len() || tokens[p2] != ")" {
        return Err(anyhow!("expected ) after {} expression", op));
    }

    let result = match op {
        "+" => quote! { (#a) + (#b) },
        "*" => quote! { (#a) * (#b) },
        _ => return Err(anyhow!("unknown binary op: {}", op)),
    };

    Ok((result, p2 + 1))
}

/// Parse a unary s-expression like "(sin a)" or "(cos a)" starting at `pos`.
/// Forward `float_ty` so numeric atoms are emitted with the correct float suffix.
fn parse_unary_op(
    op: &str,
    tokens: &[String],
    pos: usize,
    float_ty: FloatTy,
) -> Result<(proc_macro2::TokenStream, usize)> {
    let (a, p1) = sexpr_to_tokens(tokens, pos + 2, float_ty)?;

    if p1 >= tokens.len() || tokens[p1] != ")" {
        return Err(anyhow!("expected ) after {} expression", op));
    }

    let result = match op {
        "sin" => quote! { (#a).sin() },
        "cos" => quote! { (#a).cos() },
        _ => return Err(anyhow!("unknown unary op: {}", op)),
    };

    Ok((result, p1 + 1))
}

/// Parse a function call s-expression like "(f a b)" starting at `pos`.
/// `float_ty` is forwarded so numeric atoms in arguments are emitted as f32/f64.
fn parse_function_call(
    fname: &str,
    tokens: &[String],
    pos: usize,
    float_ty: FloatTy,
) -> Result<(proc_macro2::TokenStream, usize)> {
    let mut args_ts: Vec<proc_macro2::TokenStream> = Vec::new();
    let mut p = pos + 2;

    while p < tokens.len() && tokens[p] != ")" {
        let (arg_ts, next) = sexpr_to_tokens(tokens, p, float_ty)?;
        args_ts.push(arg_ts);
        p = next;
    }

    if p >= tokens.len() || tokens[p] != ")" {
        return Err(anyhow!("expected ) after function call {}", fname));
    }

    let func_ts = if syn::parse_str::<syn::Path>(fname).is_ok() {
        let path: syn::Path = syn::parse_str(fname).unwrap();
        quote! { #path }
    } else {
        let ident = syn::Ident::new(fname, Span::call_site());
        quote! { #ident }
    };

    let call = quote! { #func_ts ( #(#args_ts),* ) };
    Ok((call, p + 1))
}

/// Parse tokens starting at `pos` and return a TokenStream for the expression
/// plus the next position after the parsed expression. `float_ty` controls
/// whether numeric atoms are emitted as f32/f64 literals.
pub fn sexpr_to_tokens(
    tokens: &[String],
    pos: usize,
    float_ty: FloatTy,
) -> Result<(proc_macro2::TokenStream, usize)> {
    if tokens.is_empty() {
        return Err(anyhow!("empty token slice"));
    }
    if pos >= tokens.len() {
        return Err(anyhow!("position {} out of bounds", pos));
    }

    let t = &tokens[pos];

    if t == "(" {
        if pos + 1 >= tokens.len() {
            return Err(anyhow!(
                "malformed s-expression: missing operator after '('"
            ));
        }

        let op = &tokens[pos + 1];

        match op.as_str() {
            "+" | "*" => parse_binary_op(op, tokens, pos, float_ty),
            "sin" | "cos" => parse_unary_op(op, tokens, pos, float_ty),
            "pow" => parse_pow(tokens, pos, float_ty),
            "log" => {
                let (a, p1) = sexpr_to_tokens(tokens, pos + 2, float_ty)?;
                if p1 >= tokens.len() || tokens[p1] != ")" {
                    return Err(anyhow!("expected ) after log expression"));
                }
                Ok((quote! { (#a).ln() }, p1 + 1))
            }
            other => parse_function_call(other, tokens, pos, float_ty),
        }
    } else if t == ")" {
        Err(anyhow!("unexpected ) at position {}", pos))
    } else {
        Ok((parse_atom(t, float_ty), pos + 1))
    }
}

pub fn rec_expr_to_tokens(
    rec: &RecExpr<SymbolLang>,
    sig: &syn::Signature,
) -> Result<proc_macro2::TokenStream> {
    let s = rec.to_string();

    eprintln!("DEBUG: RecExpr string representation: {:?}", s);
    eprintln!("DEBUG: RecExpr nodes: {:?}", rec.as_ref());

    if s.trim().is_empty() {
        return Err(anyhow!("RecExpr produced empty string"));
    }

    let tokens = tokenize_sexpr(&s);
    if tokens.is_empty() {
        return Err(anyhow!("empty token list after tokenizing"));
    }

    // detect the float preference from the function signature and pass it through
    let float_ty = detect_primary_float(sig);
    let (ts, pos) = sexpr_to_tokens(&tokens, 0, float_ty)?;
    if pos != tokens.len() {
        return Err(anyhow!("trailing tokens after parse"));
    }

    Ok(ts)
}

/// Parse a single s-expression atom into tokens for macro expansion.
/// `float_ty` controls whether numeric atoms are emitted as f32/f64 literals.
fn parse_atom(token: &str, float_ty: FloatTy) -> proc_macro2::TokenStream {
    // integer literal (e.g., "1") -> emit as 1.0f32/1.0f64 when float_ty known
    if token.parse::<i64>().is_ok() {
        match float_ty {
            FloatTy::F64 => {
                let lit = LitFloat::new(&format!("{}.0f64", token), Span::call_site());
                return quote! { #lit };
            }
            FloatTy::F32 => {
                let lit = LitFloat::new(&format!("{}.0f32", token), Span::call_site());
                return quote! { #lit };
            }
            FloatTy::Unknown => {
                let lit = LitInt::new(token, Span::call_site());
                return quote! { #lit };
            }
        }
    }

    // float-like token (has decimal or parses as f64)
    if token.parse::<f64>().is_ok() {
        match float_ty {
            FloatTy::F64 => {
                let lit = LitFloat::new(&format!("{}f64", token), Span::call_site());
                return quote! { #lit };
            }
            FloatTy::F32 => {
                let lit = LitFloat::new(&format!("{}f32", token), Span::call_site());
                return quote! { #lit };
            }
            FloatTy::Unknown => {
                let lit = LitFloat::new(token, Span::call_site());
                return quote! { #lit };
            }
        }
    }

    // otherwise treat as identifier
    let ident = Ident::new(token, Span::call_site());
    quote! { #ident }
}

/// Parse a pow s-expression like "(pow base exp)" starting at `pos`.
/// Forward `float_ty` so numeric atoms are emitted with the correct float suffix.
fn parse_pow(
    tokens: &[String],
    pos: usize,
    float_ty: FloatTy,
) -> Result<(proc_macro2::TokenStream, usize)> {
    // parse base and exponent, forwarding float_ty
    let (base, p1) = sexpr_to_tokens(tokens, pos + 2, float_ty)?;
    let (exp_ts, p2) = sexpr_to_tokens(tokens, p1, float_ty)?;

    if p2 >= tokens.len() || tokens[p2] != ")" {
        return Err(anyhow!("expected ) after pow expression"));
    }

    // exp_ts -> string like "2", "2.0", "2.0f64", "2f32", etc.
    let exp_str = exp_ts.to_string();

    // strip common float suffixes
    let mut numeric = exp_str.trim().to_string();
    if numeric.ends_with("f32") {
        numeric.truncate(numeric.len() - 3);
    } else if numeric.ends_with("f64") {
        numeric.truncate(numeric.len() - 3);
    }
    numeric = numeric.trim().to_string();

    // If it looks like a float with trailing .0, normalize it
    // Try integer parse first
    let n: i32 = if let Ok(i) = numeric.parse::<i32>() {
        i
    } else if let Ok(f) = numeric.parse::<f64>() {
        // allow floats that are exact integers (e.g., "2.0")
        if (f.fract()).abs() < std::f64::EPSILON {
            f as i32
        } else {
            return Err(anyhow!("non-integer exponent in pow: {}", exp_str));
        }
    } else {
        return Err(anyhow!("non-const exponent in pow: {}", exp_str));
    };

    Ok((quote! { (#base).powi(#n) }, p2 + 1))
}

// ============================================================================
// UNIT TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use crate::{literals::convert_literal, types::FloatTy};

    use super::*;
    use crate::types::ConversionContext;
    use indexmap::IndexSet;
    use syn::{Lit, parse_quote};

    // ========================================================================
    // Test extract_param_names
    // ========================================================================

    #[test]
    fn test_extract_param_names_single() {
        let sig: syn::Signature = parse_quote! { fn foo(x: f32) -> f32 };
        let params = extract_param_names_ordered(&sig);
        assert_eq!(params.len(), 1);
        assert!(params.iter().any(|s| s == "x"));
    }

    #[test]
    fn test_extract_param_names_multiple() {
        let sig: syn::Signature = parse_quote! { fn foo(x: f32, y: f32, z: i32) -> f32 };
        let params = extract_param_names_ordered(&sig);
        assert_eq!(params.len(), 3);
        assert!(params.iter().any(|s| s == "x"));
        assert!(params.iter().any(|s| s == "y"));
        assert!(params.iter().any(|s| s == "z"));
    }

    #[test]
    fn test_extract_param_names_none() {
        let sig: syn::Signature = parse_quote! { fn foo() -> f32 };
        let params = extract_param_names_ordered(&sig);
        assert_eq!(params.len(), 0);
    }

    // ========================================================================
    // Test tokenize_sexpr
    // ========================================================================

    #[test]
    fn test_tokenize_simple_number() {
        let tokens = tokenize_sexpr("42");
        assert_eq!(tokens, vec!["42"]);
    }

    #[test]
    fn test_tokenize_simple_identifier() {
        let tokens = tokenize_sexpr("x");
        assert_eq!(tokens, vec!["x"]);
    }

    #[test]
    fn test_tokenize_simple_sexpr() {
        let tokens = tokenize_sexpr("(+ 1 2)");
        assert_eq!(tokens, vec!["(", "+", "1", "2", ")"]);
    }

    #[test]
    fn test_tokenize_nested_sexpr() {
        let tokens = tokenize_sexpr("(+ (* 2 3) 4)");
        assert_eq!(tokens, vec!["(", "+", "(", "*", "2", "3", ")", "4", ")"]);
    }

    #[test]
    fn test_tokenize_trig() {
        let tokens = tokenize_sexpr("(sin x)");
        assert_eq!(tokens, vec!["(", "sin", "x", ")"]);
    }

    #[test]
    fn test_tokenize_empty() {
        let tokens = tokenize_sexpr("");
        assert_eq!(tokens.len(), 0);
    }

    #[test]
    fn test_tokenize_whitespace_only() {
        let tokens = tokenize_sexpr("   ");
        assert_eq!(tokens.len(), 0);
    }

    // ========================================================================
    // Test convert_literal
    // ========================================================================

    #[test]
    fn test_convert_int_literal() {
        let lit: Lit = parse_quote! { 42 };
        let ctx = ConversionContext {
            params: IndexSet::new(),
            float_ty: FloatTy::Unknown,
        };
        let result = convert_literal(&lit, &ctx).unwrap();

        assert_eq!(result, "42");
    }

    #[test]
    fn test_convert_float_literal() {
        let lit: Lit = parse_quote! { 3.14 };
        let ctx = ConversionContext {
            params: IndexSet::new(),
            float_ty: FloatTy::Unknown,
        };
        let result = convert_literal(&lit, &ctx).unwrap();

        assert_eq!(result, "3.14");
    }

    // ========================================================================
    // Test expr_to_sexpr for simple cases
    // ========================================================================

    #[test]
    fn test_expr_to_sexpr_literal() {
        let expr: Expr = parse_quote! { 42 };
        let params = IndexSet::new();
        let ctx = ConversionContext {
            params,
            float_ty: FloatTy::Unknown,
        };
        let result = expr_to_sexpr(&expr, &ctx).unwrap();
        assert_eq!(result, "42");
    }

    #[test]
    fn test_expr_to_sexpr_variable() {
        let expr: Expr = parse_quote! { x };
        let params = IndexSet::new();
        let ctx = ConversionContext {
            params,
            float_ty: FloatTy::Unknown,
        };
        let result = expr_to_sexpr(&expr, &ctx).unwrap();
        assert_eq!(result, "x");
    }

    #[test]
    fn test_expr_to_sexpr_add() {
        let expr: Expr = parse_quote! { x + y };
        let params = IndexSet::new();
        let ctx = ConversionContext {
            params,
            float_ty: FloatTy::Unknown,
        };
        let result = expr_to_sexpr(&expr, &ctx).unwrap();
        assert_eq!(result, "(+ x y)");
    }

    #[test]
    fn test_expr_to_sexpr_mul() {
        let expr: Expr = parse_quote! { x * y };
        let params = IndexSet::new();
        let ctx = ConversionContext {
            params,
            float_ty: FloatTy::Unknown,
        };
        let result = expr_to_sexpr(&expr, &ctx).unwrap();
        assert_eq!(result, "(* x y)");
    }

    #[test]
    fn test_expr_to_sexpr_sub() {
        let expr: Expr = parse_quote! { x - y };
        let params = IndexSet::new();
        let ctx = ConversionContext {
            params,
            float_ty: FloatTy::Unknown,
        };
        let result = expr_to_sexpr(&expr, &ctx).unwrap();
        assert_eq!(result, "(+ x (* -1 y))");
    }

    #[test]
    fn test_expr_to_sexpr_sin() {
        let expr: Expr = parse_quote! { x.sin() };
        let params = IndexSet::new();
        let ctx = ConversionContext {
            params,
            float_ty: FloatTy::Unknown,
        };
        let result = expr_to_sexpr(&expr, &ctx).unwrap();
        assert_eq!(result, "(sin x)");
    }

    #[test]
    fn test_expr_to_sexpr_cos() {
        let expr: Expr = parse_quote! { x.cos() };
        let params = IndexSet::new();
        let ctx = ConversionContext {
            params,
            float_ty: FloatTy::Unknown,
        };
        let result = expr_to_sexpr(&expr, &ctx).unwrap();
        assert_eq!(result, "(cos x)");
    }

    #[test]
    fn test_expr_to_sexpr_powi() {
        let expr: Expr = parse_quote! { x.powi(2) };
        let params = IndexSet::new();
        let ctx = ConversionContext {
            params,
            float_ty: FloatTy::Unknown,
        };
        let result = expr_to_sexpr(&expr, &ctx).unwrap();
        assert_eq!(result, "(pow x 2)");
    }

    #[test]
    fn test_expr_to_sexpr_function_call() {
        let expr: Expr = parse_quote! { f(x) };
        let params = IndexSet::new();
        let ctx = ConversionContext {
            params,
            float_ty: FloatTy::Unknown,
        };
        let result = expr_to_sexpr(&expr, &ctx).unwrap();
        assert_eq!(result, "(f x)");
    }

    #[test]
    fn test_expr_to_sexpr_nested() {
        let expr: Expr = parse_quote! { (x + y) * z };
        let params = IndexSet::new();
        let ctx = ConversionContext {
            params,
            float_ty: FloatTy::Unknown,
        };
        let result = expr_to_sexpr(&expr, &ctx).unwrap();
        assert_eq!(result, "(* (+ x y) z)");
    }

    // ========================================================================
    // Test the trig identity pattern (THIS IS THE KEY TEST)
    // ========================================================================

    #[test]
    fn test_expr_to_sexpr_sin_squared_plus_cos_squared_with_mul() {
        // x.sin() * x.sin() + x.cos() * x.cos()
        let expr: Expr = parse_quote! { x.sin() * x.sin() + x.cos() * x.cos() };
        let params = IndexSet::new();
        let ctx = ConversionContext {
            params,
            float_ty: FloatTy::Unknown,
        };
        let result = expr_to_sexpr(&expr, &ctx).unwrap();
        // Should produce: (+ (* (sin x) (sin x)) (* (cos x) (cos x)))
        assert_eq!(result, "(+ (* (sin x) (sin x)) (* (cos x) (cos x)))");
    }

    #[test]
    fn test_expr_to_sexpr_sin_squared_plus_cos_squared_with_powi() {
        // x.sin().powi(2) + x.cos().powi(2)
        let expr: Expr = parse_quote! { x.sin().powi(2) + x.cos().powi(2) };
        let params = IndexSet::new();
        let ctx = ConversionContext {
            params,
            float_ty: FloatTy::Unknown,
        };
        let result = expr_to_sexpr(&expr, &ctx).unwrap();
        // Should produce: (+ (pow (sin x) 2) (pow (cos x) 2))
        assert_eq!(result, "(+ (pow (sin x) 2) (pow (cos x) 2))");
    }

    // ========================================================================
    // Test parse_atom
    // ========================================================================

    #[test]
    fn test_parse_atom_number() {
        let ts = parse_atom("42", FloatTy::Unknown);
        assert_eq!(ts.to_string(), "42");
    }

    #[test]
    fn test_parse_atom_identifier() {
        let ts = parse_atom("x", FloatTy::Unknown);
        assert_eq!(ts.to_string(), "x");
    }

    // ========================================================================
    // Test sexpr_to_tokens for simple cases
    // ========================================================================
    #[test]
    fn test_sexpr_to_tokens_number() {
        let tokens = vec!["42".to_string()];
        let (ts, pos) = sexpr_to_tokens(&tokens, 0, FloatTy::Unknown).unwrap();
        assert_eq!(pos, 1);
        assert_eq!(ts.to_string(), "42");
    }

    #[test]
    fn test_sexpr_to_tokens_identifier() {
        let tokens = vec!["x".to_string()];
        let (ts, pos) = sexpr_to_tokens(&tokens, 0, FloatTy::Unknown).unwrap();
        assert_eq!(pos, 1);
        assert_eq!(ts.to_string(), "x");
    }

    #[test]
    fn test_sexpr_to_tokens_add() {
        let tokens = tokenize_sexpr("(+ 1 2)");
        let (ts, pos) = sexpr_to_tokens(&tokens, 0, FloatTy::Unknown).unwrap();
        assert_eq!(pos, tokens.len());
        // The output will have parentheses and formatting
        assert!(ts.to_string().contains("+"));
    }

    #[test]
    fn test_sexpr_to_tokens_sin() {
        let tokens = tokenize_sexpr("(sin x)");
        let (ts, pos) = sexpr_to_tokens(&tokens, 0, FloatTy::Unknown).unwrap();
        assert_eq!(pos, tokens.len());
        assert!(ts.to_string().contains("sin"));
    }
}
