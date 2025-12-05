// example_runtime/src/main.rs

use symbolic_maths::sym_math;

fn b(num: f32) -> f32 {
    // return the expression as the function value (no trailing semicolon)
    num * num.sin() * num.sin() + num.cos() * num.cos()
}

#[sym_math]
pub fn a(num: f32) -> f32 {
    // same pattern: expression as return value
    b(num) * num.sin() * num.sin() + num.cos() * num.cos()
}

fn main() {
    for &x in &[0.0_f32, 0.1, 1.0, 2.3, std::f32::consts::PI] {
        println!("x={} a(x)={}", x, a(x));
    }
}
