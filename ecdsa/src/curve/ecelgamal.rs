use plonky2::field::types::{Field, Sample};
use serde::{Deserialize, Serialize};

use crate::curve::curve_msm::msm_parallel;
use crate::curve::curve_types::{base_to_scalar, AffinePoint, Curve, CurveScalar};

#[derive(Copy, Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct ECElGamalCipherText<C: Curve> {
    pub r: AffinePoint<C>,
    pub c: AffinePoint<C>,
}

#[derive(Copy, Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct ECElGamalSecretKey<C: Curve>(pub C::ScalarField);

impl<C: Curve> ECElGamalSecretKey<C> {
    pub fn to_public(&self) -> ECElGamalPublicKey<C> {
        ECElGamalPublicKey((CurveScalar(self.0) * C::GENERATOR_PROJECTIVE).to_affine())
    }
}

#[derive(Copy, Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
pub struct ECElGamalPublicKey<C: Curve>(pub AffinePoint<C>);

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

pub fn enc_message<C: Curve>(m: AffinePoint<C>, pk_point: ECElGamalPublicKey<C>) -> ECElGamalCipherText<C> {
    let (r, R) = {
        let mut r = C::ScalarField::rand();
        let mut R = (CurveScalar(r) * C::GENERATOR_PROJECTIVE).to_affine();
        while R.x == C::BaseField::ZERO || R.y == C::BaseField::ZERO {
            r = C::ScalarField::rand();
            R = (CurveScalar(r) * C::GENERATOR_PROJECTIVE).to_affine();
        }
        (r, R)
    };
    let D = (CurveScalar(r) * pk_point.0.to_projective()).to_affine();
    let C = D.to_projective() + m.to_projective();

    ECElGamalCipherText { r: R, c: C.to_affine() }
}

pub fn dec_message<C: Curve>(
    ciphertext: ECElGamalCipherText<C>,
    sk: ECElGamalSecretKey<C>
) -> (bool, C::ScalarField) {
    let ECElGamalCipherText { r: R, c: C } = ciphertext;

    assert!(R.is_valid());
    assert!(C.is_valid());

    let D = (CurveScalar(sk.0) * R.to_projective()).to_affine();
    let M = C.to_projective() + D.to_projective().neg(); //(C + (-D))

    (true, base_to_scalar::<C>(M.x))
}

mod tests {
    use plonky2::field::secp256k1_scalar::Secp256K1Scalar;
    use plonky2::field::types::Sample;
    use crate::curve::curve_types::{base_to_scalar, AffinePoint, Curve, CurveScalar};
    use crate::curve::ecelgamal::{ECElGamalSecretKey, enc_message, dec_message};
    use crate::curve::secp256k1::Secp256K1;

    #[test]
    fn test_ecelgamal_native() {
        type C = Secp256K1;

        let msg = Secp256K1Scalar::rand();
        let M = (CurveScalar(msg) * C::GENERATOR_PROJECTIVE).to_affine();
        let sk = ECElGamalSecretKey::<C>(Secp256K1Scalar::rand());
        let PK = sk.to_public();

        let ciphertext = enc_message(M, PK);
        let (result, oM) = dec_message(ciphertext, sk);
        assert!(result);
        assert!(msg == oM);
    }
}
