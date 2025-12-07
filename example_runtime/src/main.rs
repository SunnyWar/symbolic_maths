// example_runtime/src/main.rs
use std::time::Instant;
use symbolic_maths::sym_math;

/// A small helper function used by both variants.
fn b(num: f32) -> f32 {
    num * 2.0
}

/// The version that the proc macro will simplify at compile time.
/// The macro should recognize `sin^2 + cos^2 == 1` and produce
/// a simpler body (conceptually `b(num) + 1.0`).
#[sym_math]
pub fn with_macro(num: f32) -> f32 {
    b(num) + num.sin().powi(2) + num.cos().powi(2)
}

/// The original, unsimplified version for comparison.
pub fn without(num: f32) -> f32 {
    b(num) + num.sin().powi(2) + num.cos().powi(2)
}

/// Run a small correctness check across sample inputs.
fn correctness_check() {
    let samples = [0.0_f32, 0.1, 1.0, 2.3, std::f32::consts::PI];
    println!("Correctness check:");
    for &x in &samples {
        let a = with_macro(x);
        let b = without(x);
        println!(
            "  x = {:>6.3}  with_macro = {:>10.6}  without = {:>10.6}  diff = {:>10.6}",
            x,
            a,
            b,
            (a - b).abs()
        );
    }
    println!();
}

/// Microbenchmark: run each function many times and measure elapsed time.
/// This is a tiny, noisy benchmark intended only to show relative cost
/// differences on a single machine; use Criterion for robust benchmarking.
fn micro_benchmark() {
    const N: usize = 5_000_000;
    let mut acc = 0.0_f32;

    // Warmup
    for i in 0..10_000 {
        acc += with_macro(i as f32 * 0.001);
        acc += without(i as f32 * 0.001);
    }

    // Benchmark with_macro
    let start = Instant::now();
    for i in 0..N {
        acc += with_macro((i % 1000) as f32 * 0.001);
    }
    let dur_with = start.elapsed();

    // Benchmark without
    let start = Instant::now();
    for i in 0..N {
        acc += without((i % 1000) as f32 * 0.001);
    }
    let dur_without = start.elapsed();

    // Print results (include accumulator so optimizer can't elide loops)
    println!("Microbenchmark ({} iterations each):", N);
    println!("  with_macro:   {:>10?}", dur_with);
    println!("  without:      {:>10?}", dur_without);
    println!("  acc (ignore): {:>10.6}", acc);
    println!();
}

fn main() {
    println!("example_runtime: demonstrating symbolic_maths macro\n");

    // Show a few sample values and correctness
    correctness_check();

    // Run microbenchmark (may take a second or two)
    micro_benchmark();

    // Show a small table of values for human inspection
    println!("Sample table:");
    for &x in &[
        0.0_f32,
        0.25,
        0.5,
        0.75,
        1.0,
        1.5,
        std::f32::consts::PI / 2.0,
    ] {
        println!(
            "  x = {:>5.3}  with_macro = {:>8.5}  without = {:>8.5}",
            x,
            with_macro(x),
            without(x)
        );
    }

    println!("\nNotes:");
    println!("  - The macro is expected to simplify `sin^2 + cos^2` to `1.0` at compile time.");
    println!(
        "  - Microbenchmark is illustrative and noisy; use a proper benchmarking crate for accurate measurements."
    );
}
