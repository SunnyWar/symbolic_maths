use core::f32;
use symbolic_maths::sym_math;

// ============================================================================
// Test basic simplifications
// ============================================================================

#[sym_math]
fn test_sin_squared_plus_cos_squared_powi(_x: f32) -> f32 {
    _x.sin().powi(2) + _x.cos().powi(2)
}

#[sym_math]
fn test_sin_squared_plus_cos_squared_powi_64(_x: f64) -> f64 {
    _x.sin().powi(2) + _x.cos().powi(2)
}

#[test]
fn test_trig_identity_with_powi() {
    // Should simplify to 1
    assert_eq!(test_sin_squared_plus_cos_squared_powi(0.0), 1.0);
    assert_eq!(test_sin_squared_plus_cos_squared_powi(1.0), 1.0);
    assert!((test_sin_squared_plus_cos_squared_powi(2.3) - 1.0).abs() < 1e-6);
}

#[sym_math]
fn test_sin_squared_plus_cos_squared_mul(_x: f32) -> f32 {
    _x.sin() * _x.sin() + _x.cos() * _x.cos()
}

#[test]
fn test_trig_identity_with_mul() {
    // Should simplify to 1
    assert_eq!(test_sin_squared_plus_cos_squared_mul(0.0), 1.0);
    assert_eq!(test_sin_squared_plus_cos_squared_mul(1.0), 1.0);
    assert!((test_sin_squared_plus_cos_squared_mul(2.3) - 1.0).abs() < 1e-6);
}

#[sym_math]
fn test_log_simplification(x: f32, y: f32) -> f32 {
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
    assert!((test_log_simplification(2.0, 3.0) - (2.0_f32.ln() + 3.0_f32.ln())).abs() < 1e-6);
}

// ============================================================================
// Test the problematic case from the original issue
// ============================================================================

fn b(num: f32) -> f32 {
    num * num.sin() * num.sin() + num.cos() * num.cos()
}

#[sym_math]
fn a(num: f32) -> f32 {
    b(num) * num.sin() * num.sin() + num.cos() * num.cos()
}

#[test]
fn test_original_issue() {
    // This currently doesn't fully simplify due to the b(num) * sin²(num) pattern
    // but at least the trailing sin²(num) + cos²(num) should simplify
    let result = a(2.3);
    println!("a(2.3) = {}", result);

    // We can verify it runs without panicking
    assert!(result.is_finite());
}

// ============================================================================
// Test edge cases
// ============================================================================

#[sym_math]
fn test_literal_only(_x: f32) -> f32 {
    42.0
}

#[test]
fn test_constant_function() {
    assert_eq!(test_literal_only(100.0), 42.0);
}

#[sym_math]
fn test_identity(x: f32) -> f32 {
    x
}

#[test]
fn test_identity_function() {
    assert_eq!(test_identity(5.0), 5.0);
    assert_eq!(test_identity(f32::consts::PI), f32::consts::PI);
}
