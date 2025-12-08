// symbolic_maths_macro/src/conv.rs
use anyhow::{Result, anyhow};
use egg::RecExpr;
use egg::SymbolLang;
use indexmap::IndexSet;
use proc_macro2::Span;
use quote::ToTokens;
use quote::quote;
use syn::Expr;
use syn::ExprBinary;
use syn::ExprCall;
use syn::ExprLit;
use syn::ExprMethodCall;
use syn::ExprPath;
use syn::ExprUnary;
use syn::Lit;
use syn::UnOp;
use syn::{FnArg, Pat};

use crate::literals::convert_literal;
use crate::types::ConversionContext;
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
// STEP 2: Convert individual expression types to s-expressions
// ============================================================================

// Convert a path expression (identifier or path) to its s-expression token.
fn convert_path(path: &syn::Path, _ctx: &ConversionContext) -> Result<String> {
    let s = path.segments.last().unwrap().ident.to_string();
    Ok(s)
}

// Convert a unary expression (e.g., negation) into an s-expression.
fn convert_unary(u: &ExprUnary, ctx: &ConversionContext) -> Result<String> {
    if let UnOp::Neg(_) = u.op {
        let inner = expr_to_sexpr(&u.expr, ctx)?;
        Ok(format!("(* -1 {})", inner))
    } else {
        Err(anyhow!("unsupported unary op"))
    }
}

// Convert a binary expression (+, -, *) into the corresponding s-expression.
fn convert_binary(binary: &ExprBinary, ctx: &ConversionContext) -> Result<String> {
    let l = expr_to_sexpr(&binary.left, ctx)?;
    let r = expr_to_sexpr(&binary.right, ctx)?;
    match binary.op {
        syn::BinOp::Add(_) => Ok(format!("(+ {} {})", l, r)),
        syn::BinOp::Mul(_) => Ok(format!("(* {} {})", l, r)),
        syn::BinOp::Sub(_) => Ok(format!("(+ {} (* -1 {}))", l, r)),
        _ => Err(anyhow!("unsupported binary op")),
    }
}

// Convert method calls (sin, cos, ln, powi, etc.) on receivers into s-expressions.
fn convert_method_call(method_call: &ExprMethodCall, ctx: &ConversionContext) -> Result<String> {
    let recv = expr_to_sexpr(&method_call.receiver, ctx)?;
    let m = method_call.method.to_string();
    let args = &method_call.args;

    match (m.as_str(), args.len()) {
        ("sin", 0) => Ok(format!("(sin {})", recv)),
        ("cos", 0) => Ok(format!("(cos {})", recv)),
        ("ln", 0) => Ok(format!("(log {})", recv)),
        ("powi", 1) => match &args[0] {
            Expr::Lit(ExprLit {
                lit: Lit::Int(li), ..
            }) => {
                let n: i64 = li.base10_parse()?;
                Ok(format!("(pow {} {})", recv, n))
            }
            _ => Err(anyhow!("powi arg must be integer literal")),
        },
        (name, _) => Err(anyhow!("unsupported method call: {}", name)),
    }
}

// Convert free function calls into s-expressions, handling argument conversion.
fn convert_function_call(call: &ExprCall, ctx: &ConversionContext) -> Result<String> {
    if let Expr::Path(ExprPath { path, .. }) = &*call.func {
        let fname = {
            let mut ts = proc_macro2::TokenStream::new();
            path.to_tokens(&mut ts);
            ts.to_string()
        };

        let mut arg_sexprs = Vec::new();
        for a in call.args.iter() {
            arg_sexprs.push(expr_to_sexpr(a, ctx)?);
        }

        if arg_sexprs.is_empty() {
            Ok(fname)
        } else {
            Ok(format!("({} {})", fname, arg_sexprs.join(" ")))
        }
    } else {
        Err(anyhow!("unsupported call form"))
    }
}

// ============================================================================
// STEP 3: Main expression to s-expression converter
// ============================================================================

/// Convert a syn::Expr into an s-expression string using the given ordered parameter set.
fn expr_to_sexpr(expr: &Expr, ctx: &ConversionContext) -> Result<String> {
    match expr {
        Expr::Lit(ExprLit { lit, .. }) => convert_literal(lit, ctx),
        Expr::Path(ExprPath { path, .. }) => convert_path(path, ctx),
        Expr::Unary(u) => convert_unary(u, ctx),
        Expr::Binary(binary) => convert_binary(binary, ctx),
        Expr::MethodCall(method_call) => convert_method_call(method_call, ctx),
        Expr::Call(call) => convert_function_call(call, ctx),
        Expr::Paren(paren) => expr_to_sexpr(&paren.expr, ctx),
        _ => {
            let mut ts = proc_macro2::TokenStream::new();
            expr.to_tokens(&mut ts);
            Err(anyhow!("unsupported expression form: {}", ts))
        }
    }
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

fn parse_binary_op(
    op: &str,
    tokens: &[String],
    pos: usize,
) -> Result<(proc_macro2::TokenStream, usize)> {
    use quote::quote;

    let (a, p1) = sexpr_to_tokens(tokens, pos + 2)?;
    let (b, p2) = sexpr_to_tokens(tokens, p1)?;

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

fn parse_unary_op(
    op: &str,
    tokens: &[String],
    pos: usize,
) -> Result<(proc_macro2::TokenStream, usize)> {
    use quote::quote;

    let (a, p1) = sexpr_to_tokens(tokens, pos + 2)?;

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

fn parse_function_call(
    fname: &str,
    tokens: &[String],
    pos: usize,
) -> Result<(proc_macro2::TokenStream, usize)> {
    use quote::quote;

    let mut args_ts: Vec<proc_macro2::TokenStream> = Vec::new();
    let mut p = pos + 2;

    while p < tokens.len() && tokens[p] != ")" {
        let (arg_ts, next) = sexpr_to_tokens(tokens, p)?;
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

pub fn sexpr_to_tokens(tokens: &[String], pos: usize) -> Result<(proc_macro2::TokenStream, usize)> {
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
            "+" | "*" => parse_binary_op(op, tokens, pos),
            "sin" | "cos" => parse_unary_op(op, tokens, pos),
            "pow" => parse_pow(tokens, pos),
            "log" => {
                let (a, p1) = sexpr_to_tokens(tokens, pos + 2)?;
                if p1 >= tokens.len() || tokens[p1] != ")" {
                    return Err(anyhow!("expected ) after log expression"));
                }
                Ok((quote! { (#a).ln() }, p1 + 1))
            }
            other => parse_function_call(other, tokens, pos),
        }
    } else if t == ")" {
        Err(anyhow!("unexpected ) at position {}", pos))
    } else {
        Ok((parse_atom(t), pos + 1))
    }
}

pub fn rec_expr_to_tokens(
    rec: &RecExpr<SymbolLang>,
    _sig: &syn::Signature,
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

    let (ts, pos) = sexpr_to_tokens(&tokens, 0)?;
    if pos != tokens.len() {
        return Err(anyhow!("trailing tokens after parse"));
    }

    Ok(ts)
}

fn parse_atom(token: &str) -> proc_macro2::TokenStream {
    if token.parse::<f64>().is_ok() {
        // Generate f32 literals to match function signatures
        let lit = syn::LitFloat::new(&format!("{}f32", token), Span::call_site());
        quote! { #lit }
    } else {
        let ident = syn::Ident::new(token, Span::call_site());
        quote! { #ident }
    }
}

fn parse_pow(tokens: &[String], pos: usize) -> Result<(proc_macro2::TokenStream, usize)> {
    let (base, p1) = sexpr_to_tokens(tokens, pos + 2)?;
    let (exp, p2) = sexpr_to_tokens(tokens, p1)?;

    if p2 >= tokens.len() || tokens[p2] != ")" {
        return Err(anyhow!("expected ) after pow expression"));
    }

    // Extract just the numeric part, strip type suffix like "f32" or "f64"
    let exp_str = exp.to_string();
    let numeric_part = exp_str
        .trim_end_matches("f32")
        .trim_end_matches("f64")
        .trim();
    let n: i32 = numeric_part
        .parse()
        .map_err(|_| anyhow!("non-const exponent in pow: {}", exp_str))?;

    Ok((quote! { (#base).powi(#n) }, p2 + 1))
}

// ============================================================================
// UNIT TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use crate::types::FloatTy;

    use super::*;
    use syn::parse_quote;

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
        use crate::types::{ConversionContext, FloatTy};
        use indexmap::IndexSet;

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
        use crate::types::{ConversionContext, FloatTy};
        use indexmap::IndexSet;

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
        use crate::types::{ConversionContext, FloatTy};
        use indexmap::IndexSet;

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
        use crate::types::{ConversionContext, FloatTy};
        use indexmap::IndexSet;

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
        use crate::types::{ConversionContext, FloatTy};
        use indexmap::IndexSet;

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
        use crate::types::{ConversionContext, FloatTy};
        use indexmap::IndexSet;

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
        use crate::types::{ConversionContext, FloatTy};
        use indexmap::IndexSet;

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
        use crate::types::{ConversionContext, FloatTy};
        use indexmap::IndexSet;

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
        use crate::types::{ConversionContext, FloatTy};
        use indexmap::IndexSet;

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
        use crate::types::{ConversionContext, FloatTy};
        use indexmap::IndexSet;

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
        use crate::types::{ConversionContext, FloatTy};
        use indexmap::IndexSet;

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
        use crate::types::{ConversionContext, FloatTy};
        use indexmap::IndexSet;

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
        let ts = parse_atom("42");
        assert_eq!(ts.to_string(), "42f32");
    }

    #[test]
    fn test_parse_atom_identifier() {
        let ts = parse_atom("x");
        assert_eq!(ts.to_string(), "x");
    }

    // ========================================================================
    // Test sexpr_to_tokens for simple cases
    // ========================================================================

    #[test]
    fn test_sexpr_to_tokens_number() {
        let tokens = vec!["42".to_string()];
        let (ts, pos) = sexpr_to_tokens(&tokens, 0).unwrap();
        assert_eq!(pos, 1);
        assert_eq!(ts.to_string(), "42f32");
    }

    #[test]
    fn test_sexpr_to_tokens_identifier() {
        let tokens = vec!["x".to_string()];
        let (ts, pos) = sexpr_to_tokens(&tokens, 0).unwrap();
        assert_eq!(pos, 1);
        assert_eq!(ts.to_string(), "x");
    }

    #[test]
    fn test_sexpr_to_tokens_add() {
        let tokens = tokenize_sexpr("(+ 1 2)");
        let (ts, pos) = sexpr_to_tokens(&tokens, 0).unwrap();
        assert_eq!(pos, tokens.len());
        // The output will have parentheses and formatting
        assert!(ts.to_string().contains("+"));
    }

    #[test]
    fn test_sexpr_to_tokens_sin() {
        let tokens = tokenize_sexpr("(sin x)");
        let (ts, pos) = sexpr_to_tokens(&tokens, 0).unwrap();
        assert_eq!(pos, tokens.len());
        assert!(ts.to_string().contains("sin"));
    }
}
