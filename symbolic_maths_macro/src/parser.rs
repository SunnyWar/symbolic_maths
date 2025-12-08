use anyhow::{Result, anyhow};
use quote::ToTokens;
use syn::Expr;
use syn::ExprBinary;
use syn::ExprLit;
use syn::ExprPath;
use syn::ExprUnary;
use syn::UnOp;

use crate::calls::{convert_function_call, convert_method_call};
use crate::literals::convert_literal;
use crate::types::ConversionContext;

/// Convert a syn::Expr into an s-expression string using the given ordered parameter set.
pub fn expr_to_sexpr(expr: &Expr, ctx: &ConversionContext) -> Result<String> {
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
