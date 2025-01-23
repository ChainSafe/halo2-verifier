use crate::arithmetic::{best_multiexp, parallelize, FieldExt};
use crate::helpers::SerdeCurveAffine;
use crate::helpers::SerdeFormat;
use crate::poly::commitment::{Blind, CommitmentScheme, Params, ParamsVerifier};
use crate::poly::{LagrangeCoeff, Polynomial};
use alloc::vec::Vec;
use group::GroupEncoding;
use halo2curves::Group;

use core::fmt::Debug;
use core::marker::PhantomData;
use ff::{Field, PrimeField};
use group::{prime::PrimeCurveAffine, Curve};
use halo2curves::pairing::Engine;
use rand_core::RngCore;

use crate::io;

use super::msm::MSMKZG;

/// These are the public parameters for the polynomial commitment scheme.
#[derive(Debug, Clone)]
pub struct ParamsKZG<E: Engine> {
    pub k: u32,
    pub n: u64,
    pub g: E::G1Affine,
    // pub g_lagrange: E::G1Affine,
    pub g2: E::G2Affine,
    pub s_g2: E::G2Affine,
}

/// Umbrella commitment scheme construction for all KZG variants
#[derive(Debug)]
pub struct KZGCommitmentScheme<E: Engine> {
    _marker: PhantomData<E>,
}

impl<E: Engine + Debug> CommitmentScheme for KZGCommitmentScheme<E>
where
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
{
    type Scalar = E::Scalar;
    type Curve = E::G1Affine;

    type ParamsVerifier = ParamsVerifierKZG<E>;
}

impl<E: Engine + Debug> ParamsKZG<E> {
    /// Initializes parameters for the curve, draws toxic secret from given rng.
    /// MUST NOT be used in production.
    pub fn setup<R: RngCore>(k: u32, rng: R) -> Self {
        let s = <E::Scalar>::random(rng);
        Self::unsafe_setup_with_s(k, s)
    }

    /// Initializes parameters for the curve, Draws random toxic point inside of the function
    /// MUST NOT be used in production
    pub fn unsafe_setup(k: u32) -> Self {
        let s = E::Scalar::random(crate::get_rng());
        Self::unsafe_setup_with_s(k, s)
    }

    /// Initializes parameters for the curve, using given random `s`
    /// MUST NOT be used in production
    pub fn unsafe_setup_with_s(k: u32, s: <E as Engine>::Scalar) -> Self {
        // Largest root of unity exponent of the Engine is `2^E::Scalar::S`, so we can
        // only support FFTs of polynomials below degree `2^E::Scalar::S`.
        assert!(k <= E::Scalar::S);
        let n: u64 = 1 << k;

        // Calculate g = [G1, [s] G1, [s^2] G1, ..., [s^(n-1)] G1] in parallel.
        let g1 = E::G1Affine::generator();
        let mut g_projective = vec![E::G1::group_zero(); n as usize];
        parallelize(&mut g_projective, |g, start| {
            let mut current_g: E::G1 = g1.into();
            current_g *= s.pow_vartime(&[start as u64]);
            for g in g.iter_mut() {
                *g = current_g;
                current_g *= s;
            }
        });

        let g = {
            let mut g = vec![E::G1Affine::identity(); n as usize];
            parallelize(&mut g, |g, starts| {
                E::G1::batch_normalize(&g_projective[starts..(starts + g.len())], g);
            });
            g[0]
        };

        let mut g_lagrange_projective = vec![E::G1::group_zero(); n as usize];
        let mut root = E::Scalar::ROOT_OF_UNITY_INV.invert().unwrap();
        for _ in k..E::Scalar::S {
            root = root.square();
        }
        let n_inv = Option::<E::Scalar>::from(E::Scalar::from(n).invert())
            .expect("inversion should be ok for n = 1<<k");
        let multiplier = (s.pow_vartime(&[n as u64]) - E::Scalar::one()) * n_inv;
        parallelize(&mut g_lagrange_projective, |g, start| {
            for (idx, g) in g.iter_mut().enumerate() {
                let offset = start + idx;
                let root_pow = root.pow_vartime(&[offset as u64]);
                let scalar = multiplier * root_pow * (s - root_pow).invert().unwrap();
                *g = g1 * scalar;
            }
        });

        let g2 = <E::G2Affine as PrimeCurveAffine>::generator();
        let s_g2 = (g2 * s).into();

        Self {
            k,
            n,
            g,
            // g_lagrange,
            g2,
            s_g2,
        }
    }

    /// Returns gernerator on G2
    pub fn g2(&self) -> E::G2Affine {
        self.g2
    }

    /// Returns first power of secret on G2
    pub fn s_g2(&self) -> E::G2Affine {
        self.s_g2
    }

    /// Writes parameters to buffer
    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()>
    where
        E::G1Affine: SerdeCurveAffine,
        E::G2Affine: SerdeCurveAffine,
    {
        self.write_custom(writer, SerdeFormat::Processed)
    }

    pub fn read<R: io::Read>(reader: &mut R) -> io::Result<Self>
    where
        E::G1Affine: SerdeCurveAffine,
        E::G2Affine: SerdeCurveAffine,
    {
        Self::read_custom(reader, SerdeFormat::Processed)
    }

    /// Writes parameters to buffer
    pub fn write_custom<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()>
    where
        E::G1Affine: SerdeCurveAffine,
        E::G2Affine: SerdeCurveAffine,
    {
        writer.write_all(&self.k.to_le_bytes())?;
        self.g.write(writer, format)?;
        self.g2.write(writer, format)?;
        self.s_g2.write(writer, format)?;
        Ok(())
    }

    /// Reads params from a buffer.
    pub fn read_custom<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self>
    where
        E::G1Affine: SerdeCurveAffine,
        E::G2Affine: SerdeCurveAffine,
    {
        let mut k = [0u8; 4];
        reader.read_exact(&mut k[..])?;
        let k = u32::from_le_bytes(k);
        let n = 1 << k;

        let g = match format {
            SerdeFormat::Processed => {
                use group::GroupEncoding;
                let load_points_from_file_parallelly =
                    |reader: &mut R| -> io::Result<Option<E::G1Affine>> {
                        let mut points_compressed =
                            vec![<<E as Engine>::G1Affine as GroupEncoding>::Repr::default(); 1];
                        for points_compressed in points_compressed.iter_mut() {
                            reader.read_exact((*points_compressed).as_mut())?;
                        }

                        let mut points = vec![Option::<E::G1Affine>::None; 1];
                        parallelize(&mut points, |points, chunks| {
                            for (i, point) in points.iter_mut().enumerate() {
                                *point = Option::from(E::G1Affine::from_bytes(
                                    &points_compressed[chunks + i],
                                ));
                            }
                        });
                        Ok(points[0])
                    };

                let g = load_points_from_file_parallelly(reader)?;
                g.ok_or("invalid point encoding")?
            }
            SerdeFormat::RawBytes => <E::G1Affine as SerdeCurveAffine>::read(reader, format)?,
            SerdeFormat::RawBytesUnchecked => {
                // avoid try branching for performance
                <E::G1Affine as SerdeCurveAffine>::read(reader, format).unwrap()
            }
        };

        let g2 = E::G2Affine::read(reader, format)?;
        let s_g2 = E::G2Affine::read(reader, format)?;

        Ok(Self {
            k,
            n: n as u64,
            g,
            g2,
            s_g2,
        })
    }

    pub fn bytes_length() -> usize {
        E::G1Affine::default().to_bytes().as_ref().len()
            + E::G2Affine::default().to_bytes().as_ref().len() * 2
            + 4
    }

    pub fn to_bytes(&self) -> Vec<u8>
    where
        E::G1Affine: SerdeCurveAffine,
        E::G2Affine: SerdeCurveAffine,
    {
        let mut bytes = Vec::<u8>::with_capacity(Self::bytes_length());
        Self::write_custom(self, &mut bytes, SerdeFormat::Processed).expect("Writing to vector should not fail");
        bytes
    }

    pub fn from_bytes(mut bytes: &[u8]) -> io::Result<Self>
    where
        E::G1Affine: SerdeCurveAffine,
        E::G2Affine: SerdeCurveAffine,
    {
        Self::read_custom(&mut bytes, SerdeFormat::Processed)
    }
}

// TODO: see the issue at https://github.com/appliedzkp/halo2/issues/45
// So we probably need much smaller verifier key. However for new bases in g1 should be in verifier keys.
/// KZG multi-open verification parameters
pub type ParamsVerifierKZG<C> = ParamsKZG<C>;

impl<'params, E: Engine + Debug> Params<'params, E::G1Affine> for ParamsKZG<E>
where
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
{
    type MSM = MSMKZG<E>;

    fn k(&self) -> u32 {
        self.k
    }

    fn n(&self) -> u64 {
        self.n
    }

    // fn downsize(&mut self, k: u32) {
    //     assert!(k <= self.k);

    //     self.k = k;
    //     self.n = 1 << k;

    //     self.g.truncate(self.n as usize);
    //     self.g_lagrange = g_to_lagrange(self.g.iter().map(|g| g.to_curve()).collect(), k);
    // }

    fn empty_msm(&'params self) -> MSMKZG<E> {
        MSMKZG::new()
    }

    /// Writes params to a buffer.
    fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.write_custom(writer, SerdeFormat::RawBytes)
    }

    /// Reads params from a buffer.
    fn read<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        Self::read_custom(reader, SerdeFormat::RawBytes)
    }
}

impl<'params, E: Engine + Debug> ParamsVerifier<'params, E::G1Affine> for ParamsKZG<E>
where
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
{
}
