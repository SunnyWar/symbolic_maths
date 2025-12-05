// example_runtime/src/main.rs

use symbolic_maths::sym_math;

fn b(num: f32) -> f32 {
    num * 2.0
}

#[sym_math]
pub fn a(num: f32) -> f32 {
    b(num) + num.sin().powi(2) + num.cos().powi(2)
}

fn main() {
    for &x in &[0.0_f32, 0.1, 1.0, 2.3, std::f32::consts::PI] {
        println!("x={} a(x)={}", x, a(x));
    }
}
