use core::marker::PhantomData;

use plonky2::field::extension::Extendable;
use plonky2::field::secp256k1_scalar::Secp256K1Scalar;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;

use crate::curve::curve_types::Curve;
use crate::curve::secp256k1::Secp256K1;
use crate::gadgets::curve::{AffinePointTarget, CircuitBuilderCurve};
use crate::gadgets::curve_fixed_base::fixed_base_curve_mul_circuit;
use crate::gadgets::glv::CircuitBuilderGlv;
use crate::gadgets::nonnative::{CircuitBuilderNonNative, NonNativeTarget};

#[derive(Clone, Debug)]
pub struct ECElGamalSecretKeyTarget<C: Curve>(pub NonNativeTarget<C::ScalarField>);

#[derive(Clone, Debug)]
pub struct ECElGamalPublicKeyTarget<C: Curve>(pub AffinePointTarget<C>);

#[derive(Clone, Debug)]
pub struct ECElGamalCipherTextTarget<C: Curve> {
    pub R: AffinePointTarget<C>,
    pub C: AffinePointTarget<C>,
}

//https://medium.com/asecuritysite-when-bob-met-alice/elgamal-and-elliptic-curve-cryptography-ecc-8b72c3c3555e
//Enc:
//PK = sk*G
//R = r*G
//D = r*PK
//C = D + M
//ciphertext = R, C
//Dec:
//D = sk*R
//M = C - D
/* TEST SUITE
Private key (Alice):    7182fa86214b1672f36113d139b2f84ca6acbbf1dbe2202e2ad99665e4fdac00
Public key (Alice): 31dfde321f1f56228feeacaeff9550c3d489ee5fd3e4e9d2e48fd41cfd9f09f6
--- Now Bob will cipher the message for Alice
Bob's message:  Testing 123
Message point:  0b54657374696e6720313233aca5a2888970256a3bb93cde2898f95fcdfd96ef
Bob cipher (K): c794b9c278298dc3abd64b0e3af62a2f7390c6c51c13a491930dea6b2dbc6ce4
Bob cipher (C): 27ac77843effff5b723abe990e7175ba0c7659da0f5aec98421f0a89b78f2d82
--- Now Alice will decipher the ciphertext (K,C) with her private key (a)
Output: Testing 123
*/

pub fn enc_message_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    M: AffinePointTarget<Secp256K1>,
    r: NonNativeTarget<C::ScalarField>,
    ciphertext: ECElGamalCipherTextTarget<Secp256K1>,
    PK: ECElGamalPublicKeyTarget<Secp256K1>,
) {
    let ECElGamalCipherTextTarget { R, C } = ciphertext;

    builder.curve_assert_valid(&pk.0);
    builder.curve_assert_valid(&R.0);
    builder.curve_assert_valid(&C.0);

    let RTarget = builder.curve_multiplication(&r, Secp256K1::GENERATOR_AFFINE);
    let DTarget = builder.curve_multiplication(&r, PK);

    let CTarget = builder.curve_add(&M, &DTarget);
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::field::types::Sample;
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    use super::*;
    use crate::curve::curve_types::CurveScalar;
    use crate::curve::ecdsa::{enc_message, ECElGamalPublicKey, ECElGamalSecretKey, ECElGamalCipherText};

    fn test_ecelgamal_circuit_with_config(config: CircuitConfig) -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        type Curve = Secp256K1;

        let pw = PartialWitness::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let msg = Secp256K1Scalar::rand();
        let M = (CurveScalar(msg) * C::GENERATOR_PROJECTIVE).to_affine();
        let MTarget = builder.constant_affine_point(M);

        let sk = ECElGamalSecretKey::<Curve>(Secp256K1Scalar::rand());
        let PK = ECElGamalPublicKey((CurveScalar(sk.0) * Curve::GENERATOR_PROJECTIVE).to_affine());

        let PKTarget = ECElGamalPublicKeyTarget(builder.constant_affine_point(pk.0));

        let ciphertext = enc_message(M, PK);

        let ECElGamalCipherText { R, C } = ciphertext;
        let RTarget = builder.constant_affine_point(R);
        let CTarget = builder.constant_affine_point(C);
        let ciphertextTarget = ECElGamalCipherTextTarget {
            R: RTareget,
            C: CTarget,
        };

        enc_message_circuit(&mut builder, MTarget, rTarget, ciphertextTarget, PKTarget);

        dbg!(builder.num_gates());
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof)
    }

    #[test]
    #[ignore]
    fn test_ecelgamal_circuit_narrow() -> Result<()> {
        test_ecelgamal_circuit_with_config(CircuitConfig::standard_ecc_config())
    }

    #[test]
    #[ignore]
    fn test_ecelgamal_circuit_wide() -> Result<()> {
        test_ecelgamal_circuit_with_config(CircuitConfig::wide_ecc_config())
    }
}
