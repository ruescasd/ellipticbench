#[cfg(test)]
mod tests {
    use elgamal_p256::algebra::groups::inst::pfec_group_p256;
    use elgamal_p256::algebra::groups::inst::pfec_group_p256::Inimportat32point;
    use num::bigint::{BigInt, Sign};
    use p256::{
        EncodedPoint, ProjectivePoint, Scalar, U256,
        elliptic_curve::{Field, Group, bigint::Encoding, sec1::ToEncodedPoint},
    };
    use rand::Rng;

    #[test]
    fn benchmark_scalar_multiplication_performance() {
        use std::time::Instant;

        // --- SETUP ---
        const NUM_ITERATIONS: u32 = 1000;
        let mut rng = rand::thread_rng();

        // Initialize duration trackers
        let mut pfec_total_duration = std::time::Duration::new(0, 0);
        let mut rust_crypto_total_duration = std::time::Duration::new(0, 0);

        // Get the generator points for both implementations
        let generator_pfec = &pfec_group_p256::g;
        let generator_rust_crypto = ProjectivePoint::generator();

        println!(
            "\n--- Running Scalar Multiplication Benchmark ({} iterations) ---",
            NUM_ITERATIONS
        );

        for _i in 0..NUM_ITERATIONS {
            // --- 1. Generate a common random exponent for this iteration ---

            let random_scalar = Scalar::random(&mut rng);
            let exponent_bigint = random_pfec_scalar(&random_scalar);

            // --- 2. Time the `pfec_group_p256` implementation ---

            let start_pfec = Instant::now();
            let result_pfec =
                pfec_group_p256::in_import_at__32_scmul(&exponent_bigint, generator_pfec);
            pfec_total_duration += start_pfec.elapsed();

            // --- 3. Time the `p256` (rust-crypto) implementation ---

            let start_rust_crypto = Instant::now();
            // The idiomatic way to do scalar multiplication in the rust-crypto crates is with the `*` operator
            let result_rust_crypto = generator_rust_crypto * random_scalar;
            rust_crypto_total_duration += start_rust_crypto.elapsed();

            // --- 4. (Optional but recommended) Verify results match to ensure we're timing the same operation ---
            // Only assert on the first run to avoid overhead in the benchmark loop
            let (x_pfec_raw, y_pfec_raw) = match result_pfec {
                Inimportat32point::Affine(x, y) => (x, y),
                _ => panic!("Expected a Point from pfec, got infinity"),
            };

            let (_sign_x, x_pfec_bytes) = x_pfec_raw.from_z().to_bytes_be();
            let (_sign_y, y_pfec_bytes) = y_pfec_raw.from_z().to_bytes_be();

            let y_pfec_bytes = if y_pfec_bytes.len() < 32 {
                // Pad with leading zeros if necessary
                let mut padded = vec![0u8; 32 - y_pfec_bytes.len()];
                padded.extend_from_slice(&y_pfec_bytes);
                padded
            } else {
                y_pfec_bytes
            };

            // Ensure the x coordinate is also 32 bytes
            let x_pfec_bytes = if x_pfec_bytes.len() < 32 {
                // Pad with leading zeros if necessary
                let mut padded = vec![0u8; 32 - x_pfec_bytes.len()];
                padded.extend_from_slice(&x_pfec_bytes);
                padded
            } else {
                x_pfec_bytes
            };

            let affine_rust_crypto = result_rust_crypto.to_affine();
            let encoded_point: EncodedPoint = affine_rust_crypto.to_encoded_point(false);
            let x_bytes = encoded_point.x().expect("x coordinate should exist");
            let y_bytes = encoded_point.y().expect("y coordinate should exist");

            let x_bigint = U256::from_be_slice(x_bytes);
            let y_bigint = U256::from_be_slice(y_bytes);

            let x_bytes_be_: [u8; 32] = x_bigint.to_be_bytes();
            let y_bytes_be_: [u8; 32] = y_bigint.to_be_bytes();

            assert_eq!(
                x_pfec_bytes,
                x_bytes_be_.to_vec(),
                "X coordinates do not match!"
            );
            assert_eq!(
                y_pfec_bytes,
                y_bytes_be_.to_vec(),
                "Y coordinates do not match!"
            );
            // println!("{:?} {:?}", sign_x, sign_y);
        }

        // --- 5. Print the results ---
        println!("\n--- Benchmark Results ---");
        println!(
            "Total time for `pfec_group_p256` implementation: {:?}",
            pfec_total_duration
        );
        println!(
            "Total time for `p256` (rust-crypto) implementation: {:?}",
            rust_crypto_total_duration
        );
        println!("\nAverage time per operation:");
        println!(
            "  - `pfec_group_p256`: {:?}",
            pfec_total_duration / NUM_ITERATIONS
        );
        println!(
            "  - `p256` (rust-crypto): {:?}",
            rust_crypto_total_duration / NUM_ITERATIONS
        );

        let pfec_micros = pfec_total_duration.as_micros() as f64;
        let rust_crypto_micros = rust_crypto_total_duration.as_micros() as f64;
        let ratio = pfec_micros / rust_crypto_micros;

        println!("Ratio (pfec_time / rust_crypto_time): {:.2}", ratio);
    }

    // we don't care about it being half the range
    fn random_pfec_point() -> Inimportat32point {
        let mut rng = rand::thread_rng();
        let random_number = rng.r#gen::<u128>();
        let bv = elgamal_p256::dword::DWord::from_u128(240, random_number);
        pfec_group_p256::in_import_at__32_enc_bits_inst_sz_sz(240, 15, bv.as_ref())
    }

    fn random_pfec_scalar(random_scalar: &Scalar) -> BigInt {
        // Convert the p256::Scalar to a num::BigInt for the pfec implementation
        let scalar_bytes = random_scalar.to_bytes(); // This is a GenericArray
        BigInt::from_bytes_be(Sign::Plus, &scalar_bytes)
    }
}
