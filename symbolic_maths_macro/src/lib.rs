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
    // Parse the input function (don't use parse_macro_input! so we can return
    // errors)
    let mut func: ItemFn = syn::parse(item.clone())
        .map_err(|e| anyhow::anyhow!("failed to parse input as function: {}", e))?;

    // Ensure single-expression body (handle optional trailing semicolon)
    let expr = match func.block.stmts.as_slice() {
        // Expr(Expr, Option<Token![;]>)
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

    // Convert syn::Expr -> egg RecExpr
    let rec = conv::to_rec_expr(&expr).map_err(|e| anyhow::anyhow!("conversion error: {}", e))?;

    // Run rewrite rules
    let simplified =
        rewrite::simplify_rec_expr(rec).map_err(|e| anyhow::anyhow!("rewrite error: {}", e))?;

    // Convert simplified RecExpr back to a syn::Expr (as TokenStream)
    let new_tokens = conv::rec_expr_to_tokens(&simplified, &func.sig)
        .map_err(|e| anyhow::anyhow!("emit error: {}", e))?;

    // Parse generated tokens back into a syn::Expr
    let new_expr: syn::Expr = syn::parse2(new_tokens.clone())
        .map_err(|e| anyhow::anyhow!("parse generated expr: {}", e))?;

    // Replace the function body with the new expression (no trailing semicolon)
    func.block.stmts.clear();
    func.block.stmts.push(Stmt::Expr(new_expr, None));

    // Return the modified function as proc_macro2::TokenStream
    Ok(quote! { #func })
}
