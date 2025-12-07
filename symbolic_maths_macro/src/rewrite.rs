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

pub fn rules() -> Result<Vec<Rewrite<SymbolLang, ()>>> {
    let mut v = Vec::new();
    v.push(make_rule(
        "sin2+cos2-pow",
        "(+ (pow (sin ?x) 2) (pow (cos ?x) 2))",
        "1",
    )?);
    v.push(make_rule(
        "sin2+cos2-mul",
        "(+ (* (sin ?x) (sin ?x)) (* (cos ?x) (cos ?x)))",
        "1",
    )?);
    v.push(make_rule("pow-1", "(pow ?a 1)", "?a")?);
    v.push(make_rule("mul-1", "(* 1 ?a)", "?a")?);
    v.push(make_rule("add-0", "(+ 0 ?a)", "?a")?);
    v.push(make_rule(
        "log-product",
        "(log (* ?a ?b))",
        "(+ (log ?a) (log ?b))",
    )?);
    v.push(make_rule(
        "add-assoc",
        "(+ ?a (+ ?b ?c))",
        "(+ (+ ?a ?b) ?c)",
    )?);
    v.push(make_rule("add-comm", "(+ ?a ?b)", "(+ ?b ?a)")?);
    v.push(make_rule(
        "mul-assoc",
        "(* ?a (* ?b ?c))",
        "(* (* ?a ?b) ?c)",
    )?);
    v.push(make_rule("mul-comm", "(* ?a ?b)", "(* ?b ?a)")?);
    v.push(make_rule(
        "add-flatten",
        "(+ (+ ?a ?b) ?c)",
        "(+ ?a (+ ?b ?c))",
    )?);
    v.push(make_rule(
        "mul-flatten",
        "(* (* ?a ?b) ?c)",
        "(* ?a (* ?b ?c))",
    )?);
    Ok(v)
}

/// Simplify a RecExpr<SymbolLang> using a a rule set
pub fn simplify_rec_expr(expr: RecExpr<SymbolLang>) -> Result<RecExpr<SymbolLang>> {
    // create a fresh e-graph and add the input expression
    let mut egraph = EGraph::<SymbolLang, ()>::default();
    let root_id = egraph.add_expr(&expr);

    // pull in the rewrite set from your rules() function
    let rules: Vec<Rewrite<SymbolLang, ()>> = crate::rewrite::rules()?;

    // run the rewrites
    let runner = Runner::default()
        .with_egraph(egraph)
        .with_iter_limit(10)
        .run(&rules);

    // extract the best (lowest-cost) expression
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_cost, best) = extractor.find_best(root_id);

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

    // ========================================================================
    // Test basic simplifications
    // ========================================================================

    #[test]
    fn test_simplify_pow_1() {
        let expr = parse_sexpr("(pow x 1)");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(result.to_string(), "x");
    }

    #[test]
    fn test_simplify_mul_1() {
        let expr = parse_sexpr("(* 1 x)");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(result.to_string(), "x");
    }

    #[test]
    fn test_simplify_add_0() {
        let expr = parse_sexpr("(+ 0 x)");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(result.to_string(), "x");
    }

    // ========================================================================
    // Test trig identity with pow
    // ========================================================================

    #[test]
    fn test_simplify_sin2_cos2_with_pow() {
        let expr = parse_sexpr("(+ (pow (sin x) 2) (pow (cos x) 2))");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(result.to_string(), "1");
    }

    #[test]
    fn test_simplify_sin2_cos2_with_pow_different_var() {
        let expr = parse_sexpr("(+ (pow (sin num) 2) (pow (cos num) 2))");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(result.to_string(), "1");
    }

    #[test]
    fn test_simplify_trig_identity_inside_sum() {
        // b(num) + sin^2(num) + cos^2(num) should simplify to b(num) + 1
        let expr = parse_sexpr("(+ (+ (b num) (pow (sin num) 2)) (pow (cos num) 2))");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(result.to_string(), "(+ (b num) 1)");
    }

    #[test]
    fn test_simplify_trig_identity_inside_nested_sum_mul() {
        // 3 + (sin^2(x) + cos^2(x)) should simplify to 3 + 1
        let expr = parse_sexpr("(+ 3 (+ (pow (sin x) 2) (pow (cos x) 2)))");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(result.to_string(), "(+ 3 1)");
    }

    #[test]
    fn test_simplify_trig_identity_with_mul_wrapper() {
        // (sin^2(x) + cos^2(x)) * y should simplify to 1 * y
        let expr = parse_sexpr("(* (+ (pow (sin x) 2) (pow (cos x) 2)) y)");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(result.to_string(), "(* 1 y)");
    }

    // ========================================================================
    // Test identities with log
    // ========================================================================

    #[test]
    fn test_log_product_rule() {
        let expr = parse_sexpr("(log (* a b))");
        let result = simplify_rec_expr(expr).expect("simplify_rec_expr failed");
        // Prefer comparing ASTs if possible; fallback to string compare:
        assert_eq!(result.to_string(), "(+ (log a) (log b))");
    }

    // ========================================================================
    // Test trig identity with multiplication (KEY TEST!)
    // ========================================================================

    #[test]
    fn test_simplify_sin2_cos2_with_mul() {
        let expr = parse_sexpr("(+ (* (sin x) (sin x)) (* (cos x) (cos x)))");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(result.to_string(), "1");
    }

    #[test]
    fn test_simplify_sin2_cos2_with_mul_num() {
        let expr = parse_sexpr("(+ (* (sin num) (sin num)) (* (cos num) (cos num)))");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(result.to_string(), "1");
    }

    // ========================================================================
    // Test compound expressions
    // ========================================================================

    #[test]
    fn test_simplify_compound_with_trig_identity() {
        // 2 * (sin(x)^2 + cos(x)^2) should simplify to 2 * 1 = 2
        let expr = parse_sexpr("(* 2 (+ (pow (sin x) 2) (pow (cos x) 2)))");
        let result = simplify_rec_expr(expr).unwrap();
        // After simplification, should be (* 2 1)
        assert_eq!(result.to_string(), "(* 2 1)");
    }

    #[test]
    fn test_simplify_no_match() {
        // Expression that doesn't match any rules
        let expr = parse_sexpr("(+ x y)");
        let result = simplify_rec_expr(expr).unwrap();
        assert_eq!(result.to_string(), "(+ x y)");
    }

    // ========================================================================
    // Test the actual failing case from the user's code
    // ========================================================================

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
