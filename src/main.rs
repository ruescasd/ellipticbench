mod curve25519_ops;
mod p256_ops;
mod secp256k1_ops;
mod utils;
mod p521_ops;
mod p384_ops;
mod test;

use utils::format_result;

fn main() {
    println!("Elliptic Curve Point Multiplication Benchmark");
    println!("=============================================");
    println!();

    let iterations = 1000;
    println!("Running benchmarks with {} iterations each...", iterations);
    println!();

    // Benchmark generator point multiplication
    let p256_gen_results = p256_ops::bench_generator_multiplication(iterations);
    let curve25519_gen_results = curve25519_ops::bench_generator_multiplication(iterations);
    let secp256k1_gen_results = secp256k1_ops::bench_generator_multiplication(iterations);
    let p521_gen_results = p521_ops::bench_generator_multiplication(iterations);
    let p384_gen_results = p384_ops::bench_generator_multiplication(iterations);
    
    // Benchmark random point multiplication
    let p256_random_results = p256_ops::bench_random_point_multiplication(iterations);
    let curve25519_random_results = curve25519_ops::bench_random_point_multiplication(iterations);
    let secp256k1_random_results = secp256k1_ops::bench_random_point_multiplication(iterations);
    let p521_random_results = p521_ops::bench_random_point_multiplication(iterations);
    let p384_random_results = p384_ops::bench_random_point_multiplication(iterations);

    // Print results
    println!("Results:");
    println!("--------");
    println!("{}", format_result(
        "Generator Point Multiplication", 
        p256_gen_results, 
        curve25519_gen_results,
        secp256k1_gen_results,
        p521_gen_results,
        p384_random_results,
    ));
    println!("{}", format_result(
        "Random Point Multiplication", 
        p256_random_results, 
        curve25519_random_results,
        secp256k1_random_results,
        p521_random_results,
        p384_random_results,
    ));
}