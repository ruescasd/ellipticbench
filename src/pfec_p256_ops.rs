use elgamal_p256::algebra::groups::inst::pfec_group_p256;
use elgamal_p256::algebra::groups::inst::pfec_group_p256::Inimportat32point;
use num::bigint::{BigInt, Sign};
use p256::Scalar;
use p256::elliptic_curve::Field;
use rand::Rng;
use rand::rngs::ThreadRng;

pub fn random_scalar(rng: &mut ThreadRng) -> Scalar {
    Scalar::random(rng)
}

pub fn random_point(_rng: &mut ThreadRng) -> Inimportat32point {
    // Use the same method as in test.rs
    let mut rng = rand::thread_rng();
    let random_number = rng.r#gen::<u128>();
    let bv = elgamal_p256::dword::DWord::from_u128(240, random_number);
    pfec_group_p256::in_import_at__32_enc_bits_inst_sz_sz(240, 15, bv.as_ref())
}

pub fn multiply_generator(exponent: BigInt) -> Inimportat32point {
    pfec_group_p256::in_import_at__32_scmul(&exponent, &pfec_group_p256::g)
}

pub fn multiply_random_point(point: &Inimportat32point, exponent: BigInt) -> Inimportat32point {
    pfec_group_p256::in_import_at__32_scmul(&exponent, point)
}

fn random_pfec_scalar(random_scalar: &Scalar) -> BigInt {
    let scalar_bytes = random_scalar.to_bytes();
    BigInt::from_bytes_be(Sign::Plus, &scalar_bytes)
}

pub fn bench_generator_multiplication(iterations: usize) -> (f64, f64, f64) {
    use std::time::Instant;
    let mut rng = rand::thread_rng();
    let scalars: Vec<Scalar> = (0..iterations).map(|_| random_scalar(&mut rng)).collect();
    let mut times = Vec::with_capacity(iterations);

    for scalar in &scalars {
        let exponent_bigint = random_pfec_scalar(scalar);
        let start = Instant::now();
        let _result = multiply_generator(exponent_bigint);
        let duration = start.elapsed();
        times.push(duration.as_micros() as f64 / 1000.0);
    }

    let avg = times.iter().sum::<f64>() / times.len() as f64;
    let min = *times
        .iter()
        .min_by(|a, b| a.partial_cmp(b).unwrap())
        .unwrap();
    let max = *times
        .iter()
        .max_by(|a, b| a.partial_cmp(b).unwrap())
        .unwrap();

    (avg, min, max)
}

pub fn bench_random_point_multiplication(iterations: usize) -> (f64, f64, f64) {
    use std::time::Instant;
    let mut rng = rand::thread_rng();
    let points: Vec<Inimportat32point> = (0..iterations).map(|_| random_point(&mut rng)).collect();
    let scalars: Vec<Scalar> = (0..iterations).map(|_| random_scalar(&mut rng)).collect();
    let mut times = Vec::with_capacity(iterations);

    for i in 0..iterations {
        let exponent_bigint = random_pfec_scalar(&scalars[i]);
        let start = Instant::now();
        let _result = multiply_random_point(&points[i], exponent_bigint);
        let duration = start.elapsed();
        times.push(duration.as_micros() as f64 / 1000.0);
    }

    let avg = times.iter().sum::<f64>() / times.len() as f64;
    let min = *times
        .iter()
        .min_by(|a, b| a.partial_cmp(b).unwrap())
        .unwrap();
    let max = *times
        .iter()
        .max_by(|a, b| a.partial_cmp(b).unwrap())
        .unwrap();

    (avg, min, max)
}
