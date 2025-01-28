use super::{
    ChallengeGamma, ChallengeTheta, ChallengeX, Error, IndexedExpressionPoly, VerifyingKey,
};
use crate::{
    helpers::{ReadExt, SerdeFormat, SerdePrimeField, WriteExt},
    poly::{commitment::MSM, Rotation, VerifierQuery},
    transcript::{EncodedChallenge, TranscriptRead},
};
use alloc::vec::Vec;
use core::{
    fmt::{self, Debug},
    marker::PhantomData,
};
use ff::Field;
use halo2curves::{io, CurveAffine};

#[derive(Clone, Default)]
pub struct Argument<F: Field> {
    pub input_expressions: Vec<IndexedExpressionPoly>,
    pub shuffle_expressions: Vec<IndexedExpressionPoly>,
    _marker: PhantomData<F>,
}

impl<F: Field> Debug for Argument<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Argument")
            .field("input_expressions", &self.input_expressions)
            .field("shuffle_expressions", &self.shuffle_expressions)
            .finish()
    }
}

impl<F: Field> Argument<F> {
    /// Constructs a new shuffle argument.
    ///
    /// `shuffle` is a sequence of `(input, shuffle)` tuples.
    pub fn new(
        input_expressions: Vec<IndexedExpressionPoly>,
        shuffle_expressions: Vec<IndexedExpressionPoly>,
    ) -> Self {
        Argument {
            input_expressions,
            shuffle_expressions,
            _marker: PhantomData,
        }
    }

    /// Returns input of this argument
    pub fn input_expressions(&self) -> &Vec<IndexedExpressionPoly> {
        &self.input_expressions
    }

    /// Returns table of this argument
    pub fn shuffle_expressions(&self) -> &Vec<IndexedExpressionPoly> {
        &self.shuffle_expressions
    }
}

pub struct Committed<C: CurveAffine> {
    product_commitment: C,
}

pub struct Evaluated<C: CurveAffine> {
    committed: Committed<C>,
    product_eval: C::Scalar,
    product_next_eval: C::Scalar,
}

impl<F: Field> Argument<F> {
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()>
    where
        F: SerdePrimeField,
    {
        writer.write_u32(self.input_expressions.len() as u32)?;

        for expr in &self.input_expressions {
            expr.write(writer, format)?;
        }
        for expr in &self.shuffle_expressions {
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
        let mut shuffle_expressions = Vec::new();
        for _ in 0..num_expressions {
            input_expressions.push(IndexedExpressionPoly::read(reader, format)?);
            shuffle_expressions.push(IndexedExpressionPoly::read(reader, format)?);
        }

        Ok(Argument {
            input_expressions,
            shuffle_expressions,
            _marker: PhantomData,
        })
    }

    pub fn bytes_length(&self) -> usize {
        self.input_expressions
            .iter()
            .map(|expr| expr.bytes_length())
            .sum::<usize>()
            + self
                .shuffle_expressions
                .iter()
                .map(|expr| expr.bytes_length())
                .sum::<usize>()
    }

    pub(crate) fn read_product_commitment<
        C: CurveAffine<ScalarExt = F>,
        E: EncodedChallenge<C>,
        T: TranscriptRead<C, E>,
    >(
        &self,
        transcript: &mut T,
    ) -> Result<Committed<C>, Error> {
        let product_commitment = transcript.read_point()?;

        Ok(Committed { product_commitment })
    }
}

impl<C: CurveAffine> Committed<C> {
    pub(crate) fn evaluate<E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
        self,
        transcript: &mut T,
    ) -> Result<Evaluated<C>, Error> {
        let product_eval = transcript.read_scalar()?;
        let product_next_eval = transcript.read_scalar()?;

        Ok(Evaluated {
            committed: self,
            product_eval,
            product_next_eval,
        })
    }
}

impl<C: CurveAffine> Evaluated<C> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn expressions<'a>(
        &'a self,
        l_0: C::Scalar,
        l_last: C::Scalar,
        l_blind: C::Scalar,
        argument: &'a Argument<C::Scalar>,
        theta: ChallengeTheta<C>,
        gamma: ChallengeGamma<C>,
        coeff_vals: &[C::Scalar],
        advice_evals: &[C::Scalar],
        fixed_evals: &[C::Scalar],
        instance_evals: &[C::Scalar],
        challenges: &[C::Scalar],
    ) -> impl Iterator<Item = C::Scalar> + 'a {
        let active_rows = C::Scalar::ONE - (l_last + l_blind);

        let product_expression = || {
            // z(\omega X) (s(X) + \gamma) - z(X) (a(X) + \gamma)
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
            // z(\omega X) (s(X) + \gamma)
            let left = self.product_next_eval
                * &(compress_expressions(&argument.shuffle_expressions) + &*gamma);
            // z(X) (a(X) + \gamma)
            let right =
                self.product_eval * &(compress_expressions(&argument.input_expressions) + &*gamma);

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
                // (1 - (l_last(X) + l_blind(X))) * ( z(\omega X) (s(X) + \gamma) - z(X) (a(X) + \gamma))
                Some(product_expression()),
            )
    }

    pub fn queries<'r, M: MSM<C> + 'r>(
        &'r self,
        vk: &'r VerifyingKey<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = VerifierQuery<'r, C, M>> + Clone {
        let x_next = vk.domain.rotate_omega(*x, Rotation::next());

        core::iter::empty()
            // Open shuffle product commitment at x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.product_commitment,
                *x,
                self.product_eval,
            )))
            // Open shuffle product commitment at \omega x
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.product_commitment,
                x_next,
                self.product_next_eval,
            )))
    }
}
