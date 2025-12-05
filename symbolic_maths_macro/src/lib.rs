// symbolic_maths_macro/src/lib.rs
use proc_macro::TokenStream;
use quote::quote;
use syn::ItemFn;
use syn::Stmt;

mod conv;
mod rewrite;

#[proc_macro_attribute]
pub fn sym_math(attr: TokenStream, item: TokenStream) -> TokenStream {
    match try_expand_sym_math(attr.clone(), item.clone()) {
        Ok(ts) => ts.into(),
        Err(e) => {
            // Build a helpful compile_error! with context
            let msg = format!(
                "sym_math macro error: {}\n\nattr: {}\nitem: {}\n",
                e, attr, item
            );
            let compile_err = quote! { compile_error!(#msg); };
            compile_err.into()
        }
    }
}

fn try_expand_sym_math(
    _attr: TokenStream,
    item: TokenStream,
) -> Result<proc_macro2::TokenStream, anyhow::Error> {
    let mut func: ItemFn = syn::parse(item.clone())
        .map_err(|e| anyhow::anyhow!("failed to parse input as function: {}", e))?;

    let expr = match func.block.stmts.as_slice() {
        [Stmt::Expr(e, maybe_semi)] => {
            if maybe_semi.is_some() {
                return Err(anyhow::anyhow!(
                    "sym_math requires a single expression body without a trailing semicolon"
                ));
            }
            e.clone()
        }
        _ => {
            return Err(anyhow::anyhow!(
                "sym_math requires a single expression body (no statements)"
            ));
        }
    };

    // Pass the function signature to to_rec_expr
    let rec = conv::to_rec_expr(&expr, &func.sig)
        .map_err(|e| anyhow::anyhow!("conversion error: {}", e))?;

    let simplified =
        rewrite::simplify_rec_expr(rec).map_err(|e| anyhow::anyhow!("rewrite error: {}", e))?;

    let new_tokens = conv::rec_expr_to_tokens(&simplified, &func.sig)
        .map_err(|e| anyhow::anyhow!("emit error: {}", e))?;

    let new_expr: syn::Expr = syn::parse2(new_tokens.clone())
        .map_err(|e| anyhow::anyhow!("parse generated expr: {}", e))?;

    func.block.stmts.clear();
    func.block.stmts.push(Stmt::Expr(new_expr, None));

    Ok(quote! { #func })
}
