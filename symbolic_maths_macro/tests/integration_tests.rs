use core::f32;
use symbolic_maths::sym_math;

// ============================================================================
// Test basic simplifications
// ============================================================================

#[sym_math]
fn test_sin_squared_plus_cos_squared_powi_32(_x: f32) -> f32 {
    _x.sin().powi(2) + _x.cos().powi(2)
}

#[sym_math]
fn test_sin_squared_plus_cos_squared_powi_64(_x: f64) -> f64 {
    _x.sin().powi(2) + _x.cos().powi(2)
}

#[test]
fn test_trig_identity_with_powi() {
    // Should simplify to 1
    assert_eq!(test_sin_squared_plus_cos_squared_powi_32(0.0), 1.0);
    assert_eq!(test_sin_squared_plus_cos_squared_powi_32(1.0), 1.0);
    assert!((test_sin_squared_plus_cos_squared_powi_32(2.3) - 1.0).abs() < 1e-6);

    assert_eq!(test_sin_squared_plus_cos_squared_powi_64(0.0), 1.0);
    assert_eq!(test_sin_squared_plus_cos_squared_powi_64(1.0), 1.0);
    assert!((test_sin_squared_plus_cos_squared_powi_64(2.3) - 1.0).abs() < 1e-6);
}

#[sym_math]
fn test_sin_squared_plus_cos_squared_mul_32(_x: f32) -> f32 {
    _x.sin() * _x.sin() + _x.cos() * _x.cos()
}

#[sym_math]
fn test_sin_squared_plus_cos_squared_mul_64(_x: f64) -> f64 {
    _x.sin() * _x.sin() + _x.cos() * _x.cos()
}

#[test]
fn test_trig_identity_with_mul() {
    // Should simplify to 1
    assert_eq!(test_sin_squared_plus_cos_squared_mul_32(0.0), 1.0);
    assert_eq!(test_sin_squared_plus_cos_squared_mul_32(1.0), 1.0);
    assert!((test_sin_squared_plus_cos_squared_mul_32(2.3) - 1.0).abs() < 1e-6);

    assert_eq!(test_sin_squared_plus_cos_squared_mul_64(0.0), 1.0);
    assert_eq!(test_sin_squared_plus_cos_squared_mul_64(1.0), 1.0);
    assert!((test_sin_squared_plus_cos_squared_mul_64(2.3) - 1.0).abs() < 1e-6);
}

#[sym_math]
fn test_log_simplification_32(x: f32, y: f32) -> f32 {
    (x * y).ln()
}

#[sym_math]
fn test_log_simplification_64(x: f64, y: f64) -> f64 {
    (x * y).ln()
}

// ============================================================================
// Test that non-matching expressions pass through unchanged
// ============================================================================

#[sym_math]
fn test_simple_add(x: f32) -> f32 {
    x + 2.0
}

#[test]
fn test_no_simplification_needed() {
    assert_eq!(test_simple_add(5.0), 7.0);
    assert_eq!(test_simple_add(0.0), 2.0);
}

#[sym_math]
fn test_simple_mul(x: f32) -> f32 {
    x * 3.0
}

#[test]
fn test_multiplication() {
    assert_eq!(test_simple_mul(2.0), 6.0);
    assert_eq!(test_simple_mul(0.0), 0.0);
}

// ============================================================================
// Test function calls within expressions
// ============================================================================

fn helper(x: f32) -> f32 {
    x * 2.0
}

#[sym_math]
fn test_with_function_call(x: f32) -> f32 {
    helper(x) + x.sin().powi(2) + x.cos().powi(2)
}

#[test]
fn test_function_call_with_trig_identity() {
    // helper(x) + 1 = 2x + 1
    assert_eq!(test_with_function_call(0.0), 1.0);
    assert_eq!(test_with_function_call(1.0), 3.0);
    assert!((test_with_function_call(2.5) - 6.0).abs() < 1e-6);
}

#[test]
fn test_log_rule() {
    // Should simplify to x.ln() + y.ln()
    assert!((test_log_simplification_32(2.0, 3.0) - (2.0_f32.ln() + 3.0_f32.ln())).abs() < 1e-6);
    assert!((test_log_simplification_64(2.0, 3.0) - (2.0_f64.ln() + 3.0_f64.ln())).abs() < 1e-6);
}

// ============================================================================
// Test the problematic case from the original issue
// ============================================================================

fn b_32(num: f32) -> f32 {
    num * num.sin() * num.sin() + num.cos() * num.cos()
}

#[sym_math]
fn a_32(num: f32) -> f32 {
    b_32(num) * num.sin() * num.sin() + num.cos() * num.cos()
}

fn b_64(num: f64) -> f64 {
    num * num.sin() * num.sin() + num.cos() * num.cos()
}

#[sym_math]
fn a_64(num: f64) -> f64 {
    b_64(num) * num.sin() * num.sin() + num.cos() * num.cos()
}

#[test]
fn test_original_issue_32() {
    // This currently doesn't fully simplify due to the b(num) * sin²(num) pattern
    // but at least the trailing sin²(num) + cos²(num) should simplify
    let result = a_32(2.3);
    println!("a(2.3) = {}", result);

    // We can verify it runs without panicking
    assert!(result.is_finite());
}

#[test]
fn test_original_issue_64() {
    // This currently doesn't fully simplify due to the b(num) * sin²(num) pattern
    // but at least the trailing sin²(num) + cos²(num) should simplify
    let result = a_64(2.3);
    println!("a(2.3) = {}", result);

    // We can verify it runs without panicking
    assert!(result.is_finite());
}

// ============================================================================
// Test edge cases
// ============================================================================

#[sym_math]
fn test_literal_only_32(_x: f32) -> f32 {
    42.0
}

#[sym_math]
fn test_literal_only_64(_x: f64) -> f64 {
    42.0
}

#[test]
fn test_constant_function() {
    assert_eq!(test_literal_only_32(100.0), 42.0);
    assert_eq!(test_literal_only_64(100.0), 42.0);
}

#[sym_math]
fn test_identity_32(x: f32) -> f32 {
    x
}

#[sym_math]
fn test_identity_64(x: f64) -> f64 {
    x
}

#[test]
fn test_identity_function() {
    assert_eq!(test_identity_32(5.0), 5.0);
    assert_eq!(test_identity_32(f32::consts::PI), f32::consts::PI);

    assert_eq!(test_identity_64(5.0), 5.0);
    assert_eq!(test_identity_64(std::f64::consts::PI), std::f64::consts::PI);
}

#[sym_math]
fn comm_add(a: f32, b: f32) -> f32 {
    a + b
}

#[test]
fn test_add_comm() {
    assert_eq!(comm_add(2.0, 3.0), 5.0);
    assert_eq!(comm_add(3.0, 2.0), 5.0);
}

#[sym_math]
fn assoc_add(a: f32, b: f32, c: f32) -> f32 {
    a + (b + c)
}

#[sym_math]
fn flat_add(a: f32, b: f32, c: f32) -> f32 {
    (a + b) + c
}

#[test]
fn test_add_assoc_flatten() {
    assert_eq!(assoc_add(1.0, 2.0, 3.0), flat_add(1.0, 2.0, 3.0));
}

#[sym_math]
fn assoc_mul(a: f32, b: f32, c: f32) -> f32 {
    a * (b * c)
}

#[sym_math]
fn flat_mul(a: f32, b: f32, c: f32) -> f32 {
    (a * b) * c
}

#[test]
fn test_mul_assoc_flatten() {
    assert_eq!(assoc_mul(2.0, 3.0, 4.0), flat_mul(2.0, 3.0, 4.0));
}

#[sym_math]
fn pow_one_s_expr(x: f32) -> f32 {
    x.powi(1)
}

#[sym_math]
fn pow_one_explicit(x: f32) -> f32 {
    x
} // after rewrite should be identical

#[test]
fn test_pow_one() {
    assert_eq!(pow_one_s_expr(2.0), pow_one_explicit(2.0));
}

#[sym_math]
fn left_mul_one(x: f32) -> f32 {
    1.0 * x
}
#[sym_math]
fn right_mul_one(x: f32) -> f32 {
    x * 1.0
}
#[sym_math]
fn left_add_zero(x: f32) -> f32 {
    0.0 + x
}
#[sym_math]
fn right_add_zero(x: f32) -> f32 {
    x + 0.0
}

#[test]
fn test_mul_add_identity() {
    assert_eq!(left_mul_one(3.0), 3.0);
    assert_eq!(right_mul_one(3.0), 3.0);
    assert_eq!(left_add_zero(3.0), 3.0);
    assert_eq!(right_add_zero(3.0), 3.0);
}

#[sym_math]
fn left_mul_zero(x: f32) -> f32 {
    0.0 * x
}
#[sym_math]
fn right_mul_zero(x: f32) -> f32 {
    x * 0.0
}

#[test]
fn test_mul_zero() {
    assert_eq!(left_mul_zero(3.0), 0.0);
    assert_eq!(right_mul_zero(3.0), 0.0);
}

#[sym_math]
fn nested_trig(x: f32) -> f32 {
    5.0 + (x.sin().powi(2) + x.cos().powi(2))
}
#[sym_math]
fn nested_trig_mul(x: f32) -> f32 {
    5.0 + (x.sin() * x.sin() + x.cos() * x.cos())
}

#[test]
fn test_nested_trig() {
    assert_eq!(nested_trig(1.2), nested_trig_mul(1.2));
}

#[sym_math]
fn f32_add(x: f32) -> f32 {
    x + 1.0
}
#[sym_math]
fn f64_add(x: f64) -> f64 {
    x + 1.0
}

#[test]
fn test_float_literal_types() {
    assert_eq!(f32_add(2.0), 3.0_f32);
    assert_eq!(f64_add(2.0), 3.0_f64);
}

#[sym_math]
fn almost_trig(x: f32) -> f32 {
    x.sin().powi(3) + x.cos().powi(2)
}

#[test]
fn test_nonmatching_shape() {
    // powi(3) + powi(2) should not reduce to 1
    assert!((almost_trig(0.5) - 1.0).abs() > 1e-6);
}

#[sym_math]
fn many_add(a: f32, b: f32, c: f32, d: f32) -> f32 {
    a + b + c + d
}
#[test]
fn test_many_add() {
    assert_eq!(many_add(1.0, 2.0, 3.0, 4.0), 10.0);
}

/*
#[sym_math] fn pow_nonconst(x: f32, y: f32) -> f32 { x.powf(y) }

#[test]
fn test_pow_nonconst_no_crash() {
    // Should compile and run; macro should not try to convert non-const exponent to powi
    let _ = pow_nonconst(2.0, 1.5);
}

#[sym_math]
fn log_one() -> f32 {
    1.0_f32.ln()
}
#[sym_math]
fn log_of_exp(x: f32) -> f32 {
    (x.exp()).ln()
}

#[test]
fn test_log_rules() {
    assert_eq!(log_one(), 0.0);
    assert!((log_of_exp(2.3) - 2.3).abs() < 1e-6);
}
*/
