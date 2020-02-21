mod elgamal_proof;
mod cross_base_proof;

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use rand::rngs::OsRng;
use sha2::{Digest, Sha512};
use rand::{CryptoRng, RngCore};
use curve25519_dalek::constants::{RISTRETTO_BASEPOINT_POINT, RISTRETTO_BASEPOINT_TABLE};
use rand::Rng;
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use elgamal_proof::ElgamalProof;
use cross_base_proof::CrossBaseProof;
use merlin::Transcript;
use curve25519_dalek::traits::Identity;


const NUM_REP_SHARES: usize = 11;
const NUM_REP_SHARES_NEEDED: usize = NUM_REP_SHARES * 2 / 3;
const DOMAIN_NAME: &[u8] = b"Fiono11/orv-privacy";

fn main() {

    let mut rng = OsRng;
    let basepoint = RISTRETTO_BASEPOINT_POINT;
    let mut public_keys = Vec::with_capacity(usize::from(NUM_REP_SHARES)); 
    let mut private_keys = Vec::with_capacity(usize::from(NUM_REP_SHARES));
    let mut points = Vec::with_capacity(usize::from(NUM_REP_SHARES));
    let mut total_shares = Vec::with_capacity(usize::from(NUM_REP_SHARES));

    /// Each participant generates his public key
    for x in 0..NUM_REP_SHARES {
        let private_key = Scalar::random(&mut rng);
        private_keys.push(private_key);
        let public_key = private_key * basepoint;
        public_keys.push(public_key);
    }

    /// The dealer chooses a random polynomial f(x) of degree NUM_REP_SHARES_NEEDED-1, where f(0) is the subsecret
    for i in 0..NUM_REP_SHARES {
        let mut coeffs = Vec::with_capacity(usize::from(NUM_REP_SHARES_NEEDED));
        points.push(Scalar::from((i+1) as u64));
        coeffs.push(private_keys[i]);

        for j in 1..NUM_REP_SHARES_NEEDED {
            coeffs.push(Scalar::random(&mut rng));
        }

        /// Commitments to the NUM_REP_SHARES_NEEDED coefficients of the f(x) polynomial
        let committed_coeffs: Vec<RistrettoPoint> = coeffs.iter().map(|c| c * basepoint).collect();

        /// The dealer computes the encrypted shares
        let mut encrypted_shares = Vec::with_capacity(usize::from(NUM_REP_SHARES));
        let mut committed_shares = Vec::with_capacity(usize::from(NUM_REP_SHARES));
        let mut shares = Vec::with_capacity(usize::from(NUM_REP_SHARES));
        
        for x in 0..NUM_REP_SHARES {
            let x_scalar = Scalar::from((x+1) as u64);
            let mut curr_x_pow = Scalar::one();
            let mut share = Scalar::zero();
            for coeff in &coeffs {
                share += coeff * curr_x_pow;
                curr_x_pow *= x_scalar;
            }
            let committed_share = share * basepoint;
            let encrypted_share = share * public_keys[x];
            committed_shares.push(committed_share);
            encrypted_shares.push(encrypted_share);
            shares.push(share);
            if total_shares.len() == NUM_REP_SHARES {
                total_shares[x] += share;
            }
            else {
                total_shares.push(share);
            }
        }

        /// The dealer proves in zero-knowledge that the committed shares and the encrypted shares have the same exponent
        for i in 0..NUM_REP_SHARES {
            let pubkey = public_keys[i];
            let proof = CrossBaseProof::new(&mut rng, &basepoint, &pubkey, shares[i]);
            let com = committed_shares[i];
            let enc = encrypted_shares[i];
            proof.validate(&basepoint, &com, &pubkey, &enc).unwrap();
        }
    }

    let elgamal_public_key = public_keys.iter().sum();

    println!("Done secret sharing, initializing bulletproofs..");
    let bulletproof_gens = BulletproofGens::new(32, 1);
    let pedersen_gens = PedersenGens {
        B: RISTRETTO_BASEPOINT_POINT,
        B_blinding: elgamal_public_key,
    };

    println!("Done initializing bulletproofs, generating 2 commitments and proofs..");
    let blinding_key1 = Scalar::random(&mut rng);
    let decryption_key1 = blinding_key1 * RISTRETTO_BASEPOINT_POINT;
    let balance1 = u64::from(rng.gen::<u32>() / 10);
    let (range_proof1, commitment1) = RangeProof::prove_single(
        &bulletproof_gens,
        &pedersen_gens,
        &mut Transcript::new(DOMAIN_NAME),
        balance1,
        &blinding_key1,
        32,
    )
    .expect("Failed to prove range with bulletpoof");
    let elgamal_proof1 = ElgamalProof::new(
        &mut rng,
        blinding_key1,
        &elgamal_public_key,
        balance1,
        &RISTRETTO_BASEPOINT_POINT,
    );

    let blinding_key2 = Scalar::random(&mut rng);
    let decryption_key2 = blinding_key2 * RISTRETTO_BASEPOINT_POINT;
    let balance2 = u64::from(rng.gen::<u32>() / 10);
    let (range_proof2, commitment2) = RangeProof::prove_single(
        &bulletproof_gens,
        &pedersen_gens,
        &mut Transcript::new(DOMAIN_NAME),
        balance2,
        &blinding_key2,
        32,
    )
    .expect("Failed to prove range with bulletpoof");
    let elgamal_proof2 = ElgamalProof::new(
        &mut rng,
        blinding_key2,
        &elgamal_public_key,
        balance2,
        &RISTRETTO_BASEPOINT_POINT,
    );

    println!("Done generating commitments and proofs, verifying them..");
    assert_eq!(
        range_proof1.verify_single(
            &bulletproof_gens,
            &pedersen_gens,
            &mut Transcript::new(DOMAIN_NAME),
            &commitment1,
            32,
        ),
        Ok(())
    );
    assert_eq!(
        range_proof2.verify_single(
            &bulletproof_gens,
            &pedersen_gens,
            &mut Transcript::new(DOMAIN_NAME),
            &commitment2,
            32,
        ),
        Ok(())
    );
    let commitment1 = commitment1
        .decompress()
        .expect("Failed to decompress commitment");
    let commitment2 = commitment2
        .decompress()
        .expect("Failed to decompress commitment");
    assert!(elgamal_proof1
        .verify(
            &commitment1,
            &decryption_key1,
            &elgamal_public_key,
            &RISTRETTO_BASEPOINT_POINT
        )
        .is_ok());
    assert!(elgamal_proof2
        .verify(
            &commitment2,
            &decryption_key2,
            &elgamal_public_key,
            &RISTRETTO_BASEPOINT_POINT
        )
        .is_ok());

    println!("Done verifying proofs, decrypting total balance..");

    let total_weight = balance1 + balance2;
    let total_commitment = commitment1 + commitment2;
    let total_blinding_key = blinding_key1 + blinding_key2;
    let elgamal_private_key: Scalar = private_keys.iter().sum();
    let g = RISTRETTO_BASEPOINT_POINT;
    let y = elgamal_public_key;

    // ElGamal ciphertext
    let (c1, c2) = (g * total_blinding_key, total_commitment);

    assert_eq!(commitment1, Scalar::from(balance1) * g + y * blinding_key1);
    assert_eq!(total_commitment, Scalar::from(balance1+balance2) * g + y * total_blinding_key);
    
    println!("Done verifying proofs, decrypting total balance with lagrange interpolation..");

    let mut acc = Scalar::from(0u64);
    let mut d = RistrettoPoint::identity();

    for i in 0..total_shares.len() {
            
        let xi: Scalar = points[i];
        let yi = total_shares[i];
        let mut num = Scalar::from(1u64);
        let mut denum = Scalar::from(1u64);
            
        for j in 0..total_shares.len() {
            if j != i {
                let xj = points[j];
                num = num * &xj;
                denum = denum * &(xj - &xi);
            }
        }

        acc = acc + &(yi * &(num * &denum.invert())); 
        // The decryption shares
        d = d + &(c1 * (&(yi * &(num * &denum.invert()))));
    }

    assert_eq!(elgamal_public_key, elgamal_private_key * RISTRETTO_BASEPOINT_POINT);
    assert_eq!(Scalar::from(balance1+balance2) * g, c2 - &d);
    assert_eq!(elgamal_private_key, acc);
}
