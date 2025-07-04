use elgamal_p256::algebra::groups::inst::pfec_group_p256;
use elgamal_p256::algebra::groups::inst::pfec_group_p256::Inimportat32point;
use num::bigint::{BigInt, Sign};
use p256::Scalar;
use p256::elliptic_curve::Field;
use rand::RngCore;
use rand::rngs::ThreadRng;

pub fn random_scalar(rng: &mut ThreadRng) -> Scalar {
    Scalar::random(rng)
}

// generating a random point by try and increment encoding is not uniform but we don't care
pub fn random_point() -> Inimportat32point {
    let bigint = generate_random_bigint_up_to(247);
    let bv = elgamal_p256::dword::DWord::from_int(247, &bigint);
    pfec_group_p256::enc(bv.as_ref())
    // pfec_group_p256::in_import_at__32_enc_bits_inst_sz_sz(242, 15, bv.as_ref())
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
    let mut rng = rand::thread_rng();
    let scalars: Vec<Scalar> = (0..iterations).map(|_| random_scalar(&mut rng)).collect();
    let mut times = Vec::with_capacity(iterations);

    for scalar in &scalars {
        let exponent_bigint = random_pfec_scalar(scalar);
        let start = crate::utils::now();
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
    let mut rng = rand::thread_rng();
    let points: Vec<Inimportat32point> = (0..iterations).map(|_| random_point()).collect();
    let scalars: Vec<Scalar> = (0..iterations).map(|_| random_scalar(&mut rng)).collect();
    let mut times = Vec::with_capacity(iterations);

    for i in 0..iterations {
        let exponent_bigint = random_pfec_scalar(&scalars[i]);
        let start = crate::utils::now();
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

fn generate_random_bigint_up_to(bits: u64) -> BigInt {
    if bits == 0 {
        return BigInt::from(0);
    }

    // Determine the number of bytes needed to hold the specified number of bits.
    // The `+ 7` is a common trick to round up to the nearest whole byte.
    let num_bytes = ((bits + 7) / 8) as usize;

    // Generate that many random bytes.
    let mut bytes = vec![0u8; num_bytes];
    rand::thread_rng().fill_bytes(&mut bytes);

    // Convert the bytes to a BigInt. We treat them as a big-endian positive number.
    let mut random_bigint = BigInt::from_bytes_be(Sign::Plus, &bytes);

    // The number of bits in our generated bytes might be more than requested.
    // We need to clear the excess bits to stay within the range [0, 2^bits - 1].
    // This is done by right-shifting to discard the excess high bits.
    let excess_bits = (num_bytes * 8) as u64 - bits;
    random_bigint >>= excess_bits;

    random_bigint
}
