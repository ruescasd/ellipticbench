use std::time::Instant;

use crate::secp256k1_ops;

/// Times an operation over multiple iterations and returns statistics (avg, min, max) in milliseconds
pub fn time_operation<F>(mut operation: F, iterations: usize) -> (f64, f64, f64)
where
    F: FnMut(),
{
    let mut times = Vec::with_capacity(iterations);
    
    for _ in 0..iterations {
        let start = Instant::now();
        operation();
        let duration = start.elapsed();
        times.push(duration.as_micros() as f64 / 1000.0); // Convert to milliseconds
    }
    
    // Calculate statistics
    let avg = times.iter().sum::<f64>() / times.len() as f64;
    let min = *times.iter().min_by(|a, b| a.partial_cmp(b).unwrap()).unwrap();
    let max = *times.iter().max_by(|a, b| a.partial_cmp(b).unwrap()).unwrap();
    
    (avg, min, max)
}

pub fn format_result(
    name: &str, 
    p256_results: (f64, f64, f64), 
    curve25519_results: (f64, f64, f64), 
    secp256k1_results: (f64, f64, f64),
    p521_results: (f64, f64, f64),
    p384_results: (f64, f64, f64)
) -> String {
    let (p256_avg, p256_min, p256_max) = p256_results;
    let (c25519_avg, c25519_min, c25519_max) = curve25519_results;
    let (secp256k1_avg, secp256k1_min, secp256k1_max) = secp256k1_results;
    let (p521_avg, p521_min, p521_max) = p521_results;
    let (p384_avg, p384_min, p384_max) = p384_results;
    
    // Find the fastest average time
    let min_avg = f64::min(
        p256_avg,
        f64::min(
            c25519_avg,
            f64::min(secp256k1_avg, p521_avg)
        )
    );
    
    // Calculate relative performance ratios (normalized to fastest = 1.0)
    let p256_ratio = p256_avg / min_avg;
    let c25519_ratio = c25519_avg / min_avg;
    let secp256k1_ratio = secp256k1_avg / min_avg;
    let p521_ratio = p521_avg / min_avg;
    let p384_ratio = p384_avg / min_avg;
    
    format!(
        "{:<30} |\n\
         P-256:              avg={:.3}ms, min={:.3}ms, max={:.3}ms (relative: {:.2}x) |\n\
         Curve25519:         avg={:.3}ms, min={:.3}ms, max={:.3}ms (relative: {:.2}x) |\n\
         secp256k1:          avg={:.3}ms, min={:.3}ms, max={:.3}ms (relative: {:.2}x) |\n\
         P-521:              avg={:.3}ms, min={:.3}ms, max={:.3}ms (relative: {:.2}x) |\n\
         P-384:              avg={:.3}ms, min={:.3}ms, max={:.3}ms (relative: {:.2}x)",
        name, 
        p256_avg, p256_min, p256_max, p256_ratio,
        c25519_avg, c25519_min, c25519_max, c25519_ratio,
        secp256k1_avg, secp256k1_min, secp256k1_max, secp256k1_ratio,
        p521_avg, p521_min, p521_max, p521_ratio,
        p384_avg, p384_min, p384_max, p384_ratio
    )
}
