// symbolic_maths_macro/src/conv.rs
use anyhow::Result;
use anyhow::anyhow;
use egg::RecExpr;
use egg::SymbolLang;
use proc_macro2::Span;
use syn::Expr;
use syn::ExprBinary;
use syn::ExprCall;
use syn::ExprLit;
use syn::ExprMethodCall;
use syn::ExprPath;
use syn::Lit;
use syn::UnOp;

/// Convert a syn::Expr into an s-expression string for
/// egg::RecExpr<SymbolLang>. We keep the s-expr small: operators are +, *, pow,
/// sin, cos, num, var
fn expr_to_sexpr(expr: &Expr) -> Result<String> {
    match expr {
        Expr::Lit(ExprLit {
            lit: Lit::Float(lf),
            ..
        }) => {
            let v: f64 = lf.base10_parse()?;
            Ok(format!("{}", v))
        }
        Expr::Lit(ExprLit {
            lit: Lit::Int(li), ..
        }) => {
            let v: f64 = li.base10_parse()?;
            Ok(format!("{}", v))
        }
        Expr::Path(ExprPath { path, .. }) => {
            let s = path.segments.last().unwrap().ident.to_string();
            Ok(s)
        }
        Expr::Unary(u) => {
            if let UnOp::Neg(_) = u.op {
                let inner = expr_to_sexpr(&u.expr)?;
                Ok(format!("(* -1 {})", inner))
            } else {
                Err(anyhow!("unsupported unary op"))
            }
        }
        Expr::Binary(ExprBinary {
            left, op, right, ..
        }) => {
            let l = expr_to_sexpr(left)?;
            let r = expr_to_sexpr(right)?;
            match op {
                syn::BinOp::Add(_) => Ok(format!("(+ {} {})", l, r)),
                syn::BinOp::Mul(_) => Ok(format!("(* {} {})", l, r)),
                syn::BinOp::Sub(_) => Ok(format!("(+ {} (* -1 {}))", l, r)),
                _ => Err(anyhow!("unsupported binary op")),
            }
        }
        Expr::MethodCall(ExprMethodCall {
            receiver,
            method,
            args,
            ..
        }) => {
            let recv = expr_to_sexpr(receiver)?;
            let m = method.to_string();
            if m == "sin" && args.is_empty() {
                Ok(format!("(sin {})", recv))
            } else if m == "cos" && args.is_empty() {
                Ok(format!("(cos {})", recv))
            } else if m == "powi" && args.len() == 1 {
                if let Expr::Lit(ExprLit {
                    lit: Lit::Int(li), ..
                }) = &args[0]
                {
                    let n: i64 = li.base10_parse()?;
                    Ok(format!("(pow {} {})", recv, n))
                } else {
                    Err(anyhow!("powi arg must be integer literal"))
                }
            } else {
                Err(anyhow!("unsupported method call {}", m))
            }
        }
        Expr::Call(ExprCall { func, args, .. }) => {
            // If the call is a simple path like `B(...)` or `m::B(...)`
            if let Expr::Path(ExprPath { path, .. }) = &**func {
                // Use the full path token stream so module paths are preserved
                let fname = {
                    use quote::ToTokens;
                    let mut ts = proc_macro2::TokenStream::new();
                    path.to_tokens(&mut ts);
                    ts.to_string()
                };

                // convert each arg to s-expr
                let mut arg_sexprs = Vec::new();
                for a in args.iter() {
                    arg_sexprs.push(expr_to_sexpr(a)?);
                }

                if arg_sexprs.is_empty() {
                    // zero-arg call -> treat as atom (bare path)
                    Ok(fname)
                } else {
                    // produce "(fname arg1 arg2 ...)"
                    Ok(format!("({} {})", fname, arg_sexprs.join(" ")))
                }
            } else {
                Err(anyhow!("unsupported call form"))
            }
        }
        _ => {
            // syn::Expr doesn't implement Debug; stringify the tokens for diagnostics
            let s = {
                use quote::ToTokens;
                let mut ts = proc_macro2::TokenStream::new();
                expr.to_tokens(&mut ts);
                ts.to_string()
            };
            Err(anyhow!("unsupported expression form: {}", s))
        }
    }
}

/// Top-level: convert syn::Expr -> RecExpr<SymbolLang>
pub fn to_rec_expr(expr: &Expr) -> Result<RecExpr<SymbolLang>> {
    let s = expr_to_sexpr(expr)?;
    // Wrap top-level in nothing; RecExpr::from_str expects an s-expression
    // If the expression is a bare number or var, it's fine; otherwise it's already
    // an s-expr. egg::RecExpr implements FromStr for SymbolLang.
    let rec: RecExpr<SymbolLang> = s.parse()?;
    Ok(rec)
}

/// Convert a RecExpr<SymbolLang> into a TokenStream (Rust code) by rendering
/// the root s-expr and mapping common patterns to Rust method calls.
pub fn rec_expr_to_tokens(
    rec: &RecExpr<SymbolLang>,
    _sig: &syn::Signature,
) -> Result<proc_macro2::TokenStream> {
    // Render the RecExpr as an s-expression string for the root
    let s = rec.to_string(); // e.g., "(+ (pow (sin x) 2) (pow (cos x) 2))" or "1"

    // Tokenize and guard against empty output
    let tokens = tokenize_sexpr(&s);
    if tokens.is_empty() {
        return Err(anyhow!(
            "empty s-expression produced by RecExpr; s = {:?}",
            s
        ));
    }

    // Parse tokens into TokenStream
    let (ts, pos) = sexpr_to_tokens(&tokens, 0)?;
    if pos != tokens.len() {
        return Err(anyhow!(
            "trailing tokens after parse: pos={} tokens={:?}",
            pos,
            tokens
        ));
    }
    Ok(ts)
}

fn tokenize_sexpr(s: &str) -> Vec<String> {
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
    // Remove any accidental empty tokens
    out.into_iter().filter(|t| !t.is_empty()).collect()
}

fn sexpr_to_tokens(tokens: &[String], pos: usize) -> Result<(proc_macro2::TokenStream, usize)> {
    use quote::quote;

    if tokens.is_empty() {
        return Err(anyhow!("empty token slice"));
    }
    if pos >= tokens.len() {
        return Err(anyhow!(
            "position {} out of bounds for tokens {:?}",
            pos,
            tokens
        ));
    }

    let t = &tokens[pos];
    if t == "(" {
        // ensure operator exists
        if pos + 1 >= tokens.len() {
            return Err(anyhow!(
                "malformed s-expression: missing operator after '('; tokens = {:?}",
                tokens
            ));
        }
        let op = &tokens[pos + 1];
        match op.as_str() {
            "+" => {
                let (a, p1) = sexpr_to_tokens(tokens, pos + 2)?;
                let (b, p2) = sexpr_to_tokens(tokens, p1)?;
                if p2 >= tokens.len() || tokens[p2] != ")" {
                    return Err(anyhow!(
                        "expected ) after + expression; tokens = {:?}",
                        tokens
                    ));
                }
                Ok((quote! { (#a) + (#b) }, p2 + 1))
            }
            "*" => {
                let (a, p1) = sexpr_to_tokens(tokens, pos + 2)?;
                let (b, p2) = sexpr_to_tokens(tokens, p1)?;
                if p2 >= tokens.len() || tokens[p2] != ")" {
                    return Err(anyhow!(
                        "expected ) after * expression; tokens = {:?}",
                        tokens
                    ));
                }
                Ok((quote! { (#a) * (#b) }, p2 + 1))
            }
            "pow" => {
                let (base, p1) = sexpr_to_tokens(tokens, pos + 2)?;
                let (exp, p2) = sexpr_to_tokens(tokens, p1)?;
                if p2 >= tokens.len() || tokens[p2] != ")" {
                    return Err(anyhow!(
                        "expected ) after pow expression; tokens = {:?}",
                        tokens
                    ));
                }
                // exp should be a literal number token; extract integer
                let exp_str = exp.to_string();
                let n: i32 = exp_str
                    .trim()
                    .parse()
                    .map_err(|_| anyhow!("non-const exponent in pow: {}", exp_str))?;
                Ok((quote! { (#base).powi(#n) }, p2 + 1))
            }
            "sin" => {
                let (a, p1) = sexpr_to_tokens(tokens, pos + 2)?;
                if p1 >= tokens.len() || tokens[p1] != ")" {
                    return Err(anyhow!(
                        "expected ) after sin expression; tokens = {:?}",
                        tokens
                    ));
                }
                Ok((quote! { (#a).sin() }, p1 + 1))
            }
            "cos" => {
                let (a, p1) = sexpr_to_tokens(tokens, pos + 2)?;
                if p1 >= tokens.len() || tokens[p1] != ")" {
                    return Err(anyhow!(
                        "expected ) after cos expression; tokens = {:?}",
                        tokens
                    ));
                }
                Ok((quote! { (#a).cos() }, p1 + 1))
            }
            other => {
                // Generic function call: (fname arg1 arg2 ...)
                let mut args_ts: Vec<proc_macro2::TokenStream> = Vec::new();
                let mut p = pos + 2;
                while p < tokens.len() && tokens[p] != ")" {
                    let (arg_ts, next) = sexpr_to_tokens(tokens, p)?;
                    args_ts.push(arg_ts);
                    p = next;
                }
                if p >= tokens.len() || tokens[p] != ")" {
                    return Err(anyhow!(
                        "expected ) at position {}, tokens = {:?}",
                        p,
                        tokens
                    ));
                }

                // Try to parse operator token as a path (supports m::B). Fallback to Ident.
                let func_ts = if syn::parse_str::<syn::Path>(other).is_ok() {
                    let path: syn::Path = syn::parse_str(other).unwrap();
                    quote! { #path }
                } else {
                    let ident = syn::Ident::new(other, Span::call_site());
                    quote! { #ident }
                };

                let call = quote! { #func_ts ( #(#args_ts),* ) };
                Ok((call, p + 1))
            }
        }
    } else if t == ")" {
        Err(anyhow!(
            "unexpected ) at position {} in tokens {:?}",
            pos,
            tokens
        ))
    } else {
        // atom: number or variable
        if t.parse::<f64>().is_ok() {
            // emit a float literal with f64 suffix
            let lit = syn::LitFloat::new(&format!("{}f64", t), Span::call_site());
            Ok((quote! { #lit }, pos + 1))
        } else {
            // variable/identifier: create an Ident (module paths are handled earlier)
            let ident = syn::Ident::new(t, Span::call_site());
            Ok((quote! { #ident }, pos + 1))
        }
    }
}
