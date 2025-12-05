// symbolic_maths_macro/src/rewrite.rs
use anyhow::Result;
use egg::AstSize;
use egg::EGraph;
use egg::Extractor;
use egg::RecExpr;
use egg::Rewrite;
use egg::Runner;
use egg::SymbolLang;
use egg::rewrite as rw;

/// Simplify a RecExpr<SymbolLang> using a small rule set
pub fn simplify_rec_expr(expr: RecExpr<SymbolLang>) -> Result<RecExpr<SymbolLang>> {
    let mut egraph = EGraph::<SymbolLang, ()>::default();
    let root_id = egraph.add_expr(&expr);

    let rules: &[Rewrite<SymbolLang, ()>] = &[
        // Trig identity: sin(x)^2 + cos(x)^2 -> 1 (with pow)
        rw!("sin2-cos2-pow"; "(+ (pow (sin ?x) 2) (pow (cos ?x) 2))" => "1"),
        // Trig identity: sin(x) * sin(x) + cos(x) * cos(x) -> 1 (with multiplication)
        rw!("sin2-cos2-mul"; "(+ (* (sin ?x) (sin ?x)) (* (cos ?x) (cos ?x)))" => "1"),
        // Basic simplifications
        rw!("pow-1"; "(pow ?a 1)" => "?a"),
        rw!("mul-1"; "(* 1 ?a)" => "?a"),
        rw!("add-0"; "(+ 0 ?a)" => "?a"),
    ];

    let runner = Runner::default()
        .with_egraph(egraph)
        .with_iter_limit(10)
        .run(rules);

    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_cost, best) = extractor.find_best(root_id);

    let rec: RecExpr<SymbolLang> = best;
    Ok(rec)
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

        println!("Result: {}", result.to_string());
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
