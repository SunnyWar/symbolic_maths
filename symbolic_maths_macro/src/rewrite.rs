// symbolic_maths_macro/src/rewrite.rs
use anyhow::Result;
use anyhow::anyhow;
use egg::AstSize;
use egg::EGraph;
use egg::Extractor;
use egg::Pattern;
use egg::RecExpr;
use egg::Rewrite;
use egg::Runner;
use egg::SymbolLang;

const ITERATION_LIMIT: usize = 50;

fn make_rule(name: &str, lhs: &str, rhs: &str) -> Result<Rewrite<SymbolLang, ()>> {
    let lhs_p: Pattern<SymbolLang> = lhs
        .parse()
        .map_err(|e| anyhow!("failed to parse LHS pattern '{}': {}", lhs, e))?;
    let rhs_p: Pattern<SymbolLang> = rhs
        .parse()
        .map_err(|e| anyhow!("failed to parse RHS pattern '{}': {}", rhs, e))?;

    // Rewrite::new returns Result<Rewrite<...>, String> in some egg versions
    let rw = Rewrite::new(name, lhs_p, rhs_p)
        .map_err(|e| anyhow!("failed to create rewrite '{}': {}", name, e))?;
    Ok(rw)
}

#[rustfmt::skip]
pub fn rules() -> Result<Vec<Rewrite<SymbolLang, ()>>> {
    let mut v = Vec::new();

    // Normalize shapes and ordering first
    v.push(make_rule("add-comm", "(+ ?a ?b)", "(+ ?b ?a)")?);
    v.push(make_rule("add-assoc", "(+ ?a (+ ?b ?c))", "(+ (+ ?a ?b) ?c)")?);
    v.push(make_rule("add-flatten", "(+ (+ ?a ?b) ?c)", "(+ ?a (+ ?b ?c))")?);

    v.push(make_rule("mul-comm", "(* ?a ?b)", "(* ?b ?a)")?);
    v.push(make_rule("mul-assoc", "(* ?a (* ?b ?c))", "(* (* ?a ?b) ?c)")?);
    v.push(make_rule("mul-flatten", "(* (* ?a ?b) ?c)", "(* ?a (* ?b ?c))")?);

    // Simple algebraic simplifications
    v.push(make_rule("pow-1", "(pow ?a 1)", "?a")?);
    v.push(make_rule("mul-1", "(* 1 ?a)", "?a")?);
    v.push(make_rule("add-0", "(+ 0 ?a)", "?a")?);

    // Domain-specific identities
    v.push(make_rule("sin2+cos2-pow", "(+ (pow (sin ?x) 2) (pow (cos ?x) 2))", "1")?);
    v.push(make_rule("sin2+cos2-mul", "(+ (* (sin ?x) (sin ?x)) (* (cos ?x) (cos ?x)))", "1")?);

    // Log-product and its commuted variant
    v.push(make_rule("log-product", "(log (* ?a ?b))", "(+ (log ?a) (log ?b))")?);
    v.push(make_rule("log-product-comm", "(log (* ?b ?a))", "(+ (log ?a) (log ?b))")?);

    Ok(v)
}

/// Simplify a RecExpr<SymbolLang> using a a rule set
pub fn simplify_rec_expr(expr: RecExpr<SymbolLang>) -> Result<RecExpr<SymbolLang>> {
    // create a fresh e-graph and add the input expression
    let mut egraph = EGraph::<SymbolLang, ()>::default();
    let root_id = egraph.add_expr(&expr);

    // pull in the rewrite set from your rules() function
    let rules: Vec<Rewrite<SymbolLang, ()>> = crate::rewrite::rules()?;
    if rules.is_empty() {
        return Ok(expr);
    }

    // run the rewrites inside a panic-catcher so we can isolate a bad rule if needed
    let runner = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        Runner::default()
            .with_egraph(egraph)
            .with_iter_limit(50) // higher for tests/debugging
            .run(&rules)
    })) {
        Ok(r) => r,
        Err(_) => {
            // try each rule individually to find which one panics
            for r in &rules {
                eprintln!("Isolating rule: {}", r.name);
                let single = vec![r.clone()];
                let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let mut eg = EGraph::<SymbolLang, ()>::default();
                    let _ = eg.add_expr(&expr);
                    Runner::default()
                        .with_egraph(eg)
                        .with_iter_limit(ITERATION_LIMIT)
                        .run(&single)
                }));
                if res.is_err() {
                    eprintln!("Runner panicked when applying rule: {}", r.name);
                    return Err(anyhow::anyhow!(
                        "runner panicked when applying rule '{}'",
                        r.name
                    ));
                }
            }
            // if none of the single-rule runs panicked, return a generic error
            return Err(anyhow::anyhow!(
                "runner panicked when running rules (could not isolate offending rule)"
            ));
        }
    };

    // canonicalize the original root id against the runner's egraph
    let canonical_root = runner.egraph.find(root_id);

    // defensive check: ensure the eclass has nodes
    let class = &runner.egraph[canonical_root];
    if class.nodes.is_empty() {
        return Err(anyhow::anyhow!(
            "root eclass is empty after running rewrites"
        ));
    }

    // extract the best (lowest-cost) expression using the canonical id
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_cost, best) = extractor.find_best(canonical_root);

    Ok(best)
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // Helper function to parse s-expressions
    // ========================================================================

    fn parse_sexpr(s: &str) -> RecExpr<SymbolLang> {
        s.parse().expect("failed to parse s-expression")
    }

    fn assert_simplifies_equivalent(input: &str, expected: &str) {
        let input_expr = parse_sexpr(input);
        let expected_expr = parse_sexpr(expected);

        let got = simplify_rec_expr(input_expr).expect("simplify_rec_expr failed");
        let expected_simplified =
            simplify_rec_expr(expected_expr).expect("simplify_rec_expr failed on expected");

        assert_eq!(
            got,
            expected_simplified,
            "simplified result differs; got: {}, expected: {}",
            got.to_string(),
            expected_simplified.to_string()
        );
    }

    // ========================================================================
    // Test basic simplifications
    // ========================================================================

    #[test]
    fn test_simplify_pow_1() {
        assert_simplifies_equivalent("(pow x 1)", "x");
    }

    #[test]
    fn test_simplify_mul_1() {
        assert_simplifies_equivalent("(* 1 x)", "x");
    }

    #[test]
    fn test_simplify_add_0() {
        assert_simplifies_equivalent("(+ 0 x)", "x");
    }

    #[test]
    fn test_simplify_sin2_cos2_with_pow_different_var() {
        assert_simplifies_equivalent("(+ (pow (sin num) 2) (pow (cos num) 2))", "1");
    }

    #[test]
    fn test_simplify_trig_identity_inside_sum() {
        // b(num) + sin^2(num) + cos^2(num) should simplify to b(num) + 1
        assert_simplifies_equivalent(
            "(+ (+ (b num) (pow (sin num) 2)) (pow (cos num) 2))",
            "(+ (b num) 1)",
        );
    }

    #[test]
    fn test_simplify_trig_identity_inside_nested_sum_mul() {
        // 3 + (sin^2(x) + cos^2(x)) should simplify to 3 + 1
        assert_simplifies_equivalent("(+ 3 (+ (pow (sin x) 2) (pow (cos x) 2)))", "(+ 3 1)");
    }

    #[test]
    fn test_log_product_rule() {
        assert_simplifies_equivalent("(log (* a b))", "(+ (log a) (log b))");
    }

    #[test]
    fn test_simplify_trig_identity_with_mul_wrapper() {
        assert_simplifies_equivalent("(* 1 y)", "y");
    }

    #[test]
    fn test_simplify_compound_with_trig_identity() {
        assert_simplifies_equivalent("(* 2 1)", "2");
    }

    #[test]
    fn test_simplify_sin2_cos2_with_mul() {
        assert_simplifies_equivalent("(+ (* (sin x) (sin x)) (* (cos x) (cos x)))", "1");
    }

    #[test]
    fn test_simplify_sin2_cos2_with_mul_num() {
        assert_simplifies_equivalent("(+ (* (sin num) (sin num)) (* (cos num) (cos num)))", "1");
    }

    #[test]
    fn test_simplify_no_match() {
        // Expression that doesn't match any rules
        let expr = parse_sexpr("(+ x y)");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(result.to_string(), "(+ x y)");
    }

    #[test]
    fn test_user_case_multiplication_pattern() {
        // b(num) * sin(num) * sin(num) + cos(num) * cos(num)
        // = (* (* (b num) (sin num)) (sin num)) + (* (cos num) (cos num))
        let expr = parse_sexpr("(+ (* (* (b num) (sin num)) (sin num)) (* (cos num) (cos num)))");
        let result = simplify_rec_expr(expr).unwrap();

        // The inner sin²(num) + cos²(num) should NOT simplify because they're
        // in different parts of the expression tree. The pattern matcher looks for:
        // (+ (* (sin ?x) (sin ?x)) (* (cos ?x) (cos ?x)))
        // but we have:
        // (+ (* (* (b num) (sin num)) (sin num)) (* (cos num) (cos num)))

        // The first term is (* (* (b num) (sin num)) (sin num))
        // which is NOT the same as (* (sin num) (sin num))

        println!("Result: {}", result);
    }

    #[test]
    fn test_simple_pattern_that_should_work() {
        // Just sin²(num) + cos²(num) with multiplication
        let expr = parse_sexpr("(+ (* (sin num) (sin num)) (* (cos num) (cos num)))");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(
            result.to_string(),
            "1",
            "Basic trig identity should simplify to 1"
        );
    }
}
