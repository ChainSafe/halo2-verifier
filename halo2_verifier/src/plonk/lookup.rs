use core::marker::PhantomData;

use crate::{
    arithmetic::CurveAffine,
    helpers::{ReadExt, SerdeFormat, SerdePrimeField, WriteExt},
    io,
    plonk::{ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, Error, VerifyingKey},
    poly::{commitment::MSM, Rotation, VerifierQuery},
    transcript::{EncodedChallenge, TranscriptRead},
};
use alloc::vec::Vec;
use ff::Field;

use super::IndexedExpressionPoly;

#[derive(Clone, Debug, Default)]
pub struct Argument<F: Field> {
    pub input_expressions: Vec<IndexedExpressionPoly>,
    pub table_expressions: Vec<IndexedExpressionPoly>,

    _marker: PhantomData<F>,
}

impl<F: Field> Argument<F> {
    pub fn new(
        input_expressions: Vec<IndexedExpressionPoly>,
        table_expressions: Vec<IndexedExpressionPoly>,
    ) -> Self {
        Self {
            input_expressions,
            table_expressions,
            _marker: PhantomData,
        }
    }

    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()>
    where
        F: SerdePrimeField,
    {
        writer.write_u32(self.input_expressions.len() as u32)?;

        for expr in &self.input_expressions {
            expr.write(writer, format)?;
        }
        for expr in &self.table_expressions {
            expr.write(writer, format)?;
        }
        Ok(())
    }

    pub fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self>
    where
        F: SerdePrimeField,
    {
        let num_expressions = reader.read_u32()?;
        let mut input_expressions = Vec::new();
        let mut table_expressions = Vec::new();
        for _ in 0..num_expressions {
            input_expressions.push(IndexedExpressionPoly::read(reader, format)?);
            table_expressions.push(IndexedExpressionPoly::read(reader, format)?);
        }

        Ok(Argument {
            input_expressions,
            table_expressions,
            _marker: PhantomData,
        })
    }

    pub fn bytes_length(&self) -> usize {
        self.input_expressions
            .iter()
            .map(|expr| expr.bytes_length())
            .sum::<usize>()
            + self
                .table_expressions
                .iter()
                .map(|expr| expr.bytes_length())
                .sum::<usize>()
    }

    pub fn read_permuted_commitments<
        C: CurveAffine,
        E: EncodedChallenge<C>,
        T: TranscriptRead<C, E>,
    >(
        &self,
        transcript: &mut T,
    ) -> Result<PermutationCommitments<C>, Error> {
        let permuted_input_commitment = transcript.read_point()?;
        let permuted_table_commitment = transcript.read_point()?;

        Ok(PermutationCommitments {
            permuted_input_commitment,
            permuted_table_commitment,
        })
    }
}

#[derive(Debug)]
pub struct PermutationCommitments<C: CurveAffine> {
    pub permuted_input_commitment: C,
    pub permuted_table_commitment: C,
}

impl<C: CurveAffine> PermutationCommitments<C> {
    pub fn read_product_commitment<E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
        self,
        transcript: &mut T,
    ) -> Result<Committed<C>, Error> {
        let product_commitment = transcript.read_point()?;

        Ok(Committed {
            permuted: self,
            product_commitment,
        })
    }
}

#[derive(Debug)]
pub struct Committed<C: CurveAffine> {
    pub permuted: PermutationCommitments<C>,
    pub product_commitment: C,
}

impl<C: CurveAffine> Committed<C> {
    pub fn evaluate<E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
        self,
        transcript: &mut T,
    ) -> Result<Evaluated<C>, Error> {
        let product_eval = transcript.read_scalar()?;
        let product_next_eval = transcript.read_scalar()?;
        let permuted_input_eval = transcript.read_scalar()?;
        let permuted_input_inv_eval = transcript.read_scalar()?;
        let permuted_table_eval = transcript.read_scalar()?;

        Ok(Evaluated {
            committed: self,
            product_eval,
            product_next_eval,
            permuted_input_eval,
            permuted_input_inv_eval,
            permuted_table_eval,
        })
    }
}

#[derive(Debug)]
pub struct Evaluated<C: CurveAffine> {
    pub committed: Committed<C>,
    pub product_eval: C::Scalar,
    pub product_next_eval: C::Scalar,
    pub permuted_input_eval: C::Scalar,
    pub permuted_input_inv_eval: C::Scalar,
    pub permuted_table_eval: C::Scalar,
}

impl<C: CurveAffine> Evaluated<C> {
    pub fn expressions<'a>(
        &'a self,
        l_0: C::Scalar,
        l_last: C::Scalar,
        l_blind: C::Scalar,
        argument: &'a Argument<C::Scalar>,
        theta: ChallengeTheta<C>,
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        coeff_vals: &[C::Scalar],
        advice_evals: &[C::Scalar],
        fixed_evals: &[C::Scalar],
        instance_evals: &[C::Scalar],
        challenges: &[C::Scalar],
    ) -> impl Iterator<Item = C::Scalar> + 'a {
        let active_rows = C::Scalar::ONE - (l_last + l_blind);

        let product_expression = || {
            // z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
            // - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
            let left = self.product_next_eval
                * &(self.permuted_input_eval + &*beta)
                * &(self.permuted_table_eval + &*gamma);

            let compress_expressions = |expressions: &[IndexedExpressionPoly]| {
                expressions
                    .iter()
                    .map(|expression| {
                        expression.evaluate(
                            coeff_vals,
                            advice_evals,
                            fixed_evals,
                            instance_evals,
                            challenges,
                        )
                    })
                    .fold(C::Scalar::ZERO, |acc, eval| acc * &*theta + &eval)
            };
            let right = self.product_eval
                * &(compress_expressions(&argument.input_expressions) + &*beta)
                * &(compress_expressions(&argument.table_expressions) + &*gamma);

            (left - &right) * &active_rows
        };

        core::iter::empty()
            .chain(
                // l_0(X) * (1 - z'(X)) = 0
                Some(l_0 * &(C::Scalar::ONE - &self.product_eval)),
            )
            .chain(
                // l_last(X) * (z(X)^2 - z(X)) = 0
                Some(l_last * &(self.product_eval.square() - &self.product_eval)),
            )
            .chain(
                // (1 - (l_last(X) + l_blind(X))) * (
                //   z(\omega X) (a'(X) + \beta) (s'(X) + \gamma)
                //   - z(X) (\theta^{m-1} a_0(X) + ... + a_{m-1}(X) + \beta) (\theta^{m-1} s_0(X) + ... + s_{m-1}(X) + \gamma)
                // ) = 0
                Some(product_expression()),
            )
            .chain(Some(
                // l_0(X) * (a'(X) - s'(X)) = 0
                l_0 * &(self.permuted_input_eval - &self.permuted_table_eval),
            ))
            .chain(Some(
                // (1 - (l_last(X) + l_blind(X))) * (a′(X) − s′(X))⋅(a′(X) − a′(\omega^{-1} X)) = 0
                (self.permuted_input_eval - &self.permuted_table_eval)
                    * &(self.permuted_input_eval - &self.permuted_input_inv_eval)
                    * &active_rows,
            ))
    }

    pub fn queries<'r, M: MSM<C> + 'r>(
        &'r self,
        vk: &'r VerifyingKey<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = VerifierQuery<'r, C, M>> + Clone {
        let x_inv = vk.domain.rotate_omega(*x, Rotation::prev());
        let x_next = vk.domain.rotate_omega(*x, Rotation::next());

        core::iter::empty()
            // Open lookup product commitment at x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.product_commitment,
                *x,
                self.product_eval,
            )))
            // Open lookup input commitments at x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.permuted.permuted_input_commitment,
                *x,
                self.permuted_input_eval,
            )))
            // Open lookup table commitments at x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.permuted.permuted_table_commitment,
                *x,
                self.permuted_table_eval,
            )))
            // Open lookup input commitments at \omega^{-1} x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.permuted.permuted_input_commitment,
                x_inv,
                self.permuted_input_inv_eval,
            )))
            // Open lookup product commitment at \omega x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.product_commitment,
                x_next,
                self.product_next_eval,
            )))
    }
}
