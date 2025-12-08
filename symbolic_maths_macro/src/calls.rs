use anyhow::{Result, anyhow};
use quote::ToTokens;
use syn::Expr;
use syn::ExprCall;
use syn::ExprLit;
use syn::ExprMethodCall;
use syn::ExprPath;
use syn::Lit;

use crate::parser::expr_to_sexpr;
use crate::types::ConversionContext;

// Convert method calls (sin, cos, ln, powi, etc.) on receivers into s-expressions.
pub fn convert_method_call(
    method_call: &ExprMethodCall,
    ctx: &ConversionContext,
) -> Result<String> {
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
pub fn convert_function_call(call: &ExprCall, ctx: &ConversionContext) -> Result<String> {
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
