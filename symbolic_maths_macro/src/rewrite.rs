// symbolic_maths_macro/src/rewrite.rs
use anyhow::Result;
use egg::{rewrite as rw, *};
use egg::SymbolLang;
use egg::RecExpr;

/// Simplify a RecExpr<SymbolLang> using a small rule set (sin^2 + cos^2 -> 1, etc.)
pub fn simplify_rec_expr(expr: RecExpr<SymbolLang>) -> Result<RecExpr<SymbolLang>> {
    // Build an egraph and add the input expression
    let mut egraph = EGraph::<SymbolLang, ()>::default();
    let _root_id = egraph.add_expr(&expr);

    // A small, conservative rule set
    let rules: &[Rewrite<SymbolLang, ()>] = &[
        // trig identity: sin(x)^2 + cos(x)^2 -> 1
        rw!("sin2-cos2"; "(+ (pow (sin ?x) 2) (pow (cos ?x) 2))" => "1"),
        // basic simplifications
        rw!("pow-1"; "(pow ?a 1)" => "?a"),
        rw!("mul-1"; "(* 1 ?a)" => "?a"),
        rw!("add-0"; "(+ 0 ?a)" => "?a"),
    ];

    // Run equality saturation with a modest iteration limit
   let runner = Runner::default()
    .with_egraph(egraph)
    .with_iter_limit(10)
    .run(rules);

    // Extract the best expression for the root
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let root = runner.roots[0];
    let (_cost, best) = extractor.find_best(root);

    // Convert the extracted AST back into a RecExpr<SymbolLang>
    let rec: RecExpr<SymbolLang> = best;
    Ok(rec)
}
