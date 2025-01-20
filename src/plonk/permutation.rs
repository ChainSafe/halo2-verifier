use core::iter;

use halo2_proofs::{
    arithmetic::CurveAffine, plonk::{Any, ChallengeBeta, ChallengeGamma, ChallengeX, Column, Error}, poly::{commitment::MSM, Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, Rotation, VerifierQuery}, transcript::{EncodedChallenge, TranscriptRead}, SerdeFormat
};
use alloc::vec::Vec;
use ff::{Field, PrimeField};
use halo2_proofs::arithmetic::FieldExt;

/// A permutation argument.
#[derive(Debug, Clone)]
pub struct Argument {
    /// A sequence of columns involved in the argument.
    pub columns: Vec<Column<Any>>,
}

impl From<halo2_proofs::plonk::permutation::Argument> for Argument {
    fn from(arg: halo2_proofs::plonk::permutation::Argument) -> Self {
        Argument { columns: arg.columns }
    }
}

impl Argument {
    pub(crate) fn new() -> Self {
        Argument { columns: vec![] }
    }

    /// Returns the minimum circuit degree required by the permutation argument.
    /// The argument may use larger degree gates depending on the actual
    /// circuit's degree and how many columns are involved in the permutation.
    pub(crate) fn required_degree(&self) -> usize {
        3
    }

    pub(crate) fn add_column(&mut self, column: Column<Any>) {
        if !self.columns.contains(&column) {
            self.columns.push(column);
        }
    }

    pub fn get_columns(&self) -> Vec<Column<Any>> {
        self.columns.clone()
    }
    
    pub fn read_product_commitments<
        C: CurveAffine,
        E: EncodedChallenge<C>,
        T: TranscriptRead<C, E>,
    >(
        &self,
        vk: &crate::VerifyingKey<C>,
        transcript: &mut T,
    ) -> Result<Committed<C>, Error> {
        let chunk_len = vk.cs_degree - 2;

        let permutation_product_commitments = self
            .columns
            .chunks(chunk_len)
            .map(|_| transcript.read_point())
            .collect::<Result<Vec<_>, _>>()?;

        Ok(Committed {
            permutation_product_commitments,
        })
    }
}

#[derive(Debug)]
pub struct Committed<C: CurveAffine> {
    permutation_product_commitments: Vec<C>,
}

#[derive(Debug)]
pub struct Evaluated<C: CurveAffine> {
    pub sets: Vec<EvaluatedSet<C>>,
}

#[derive(Debug)]
pub struct EvaluatedSet<C: CurveAffine> {
    pub permutation_product_commitment: C,
    pub permutation_product_eval: C::Scalar,
    pub permutation_product_next_eval: C::Scalar,
    pub permutation_product_last_eval: Option<C::Scalar>,
}

impl<C: CurveAffine> Committed<C> {
    pub fn evaluate<E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
        self,
        transcript: &mut T,
    ) -> Result<Evaluated<C>, Error> {
        let mut sets = vec![];

        let mut iter = self.permutation_product_commitments.into_iter();

        while let Some(permutation_product_commitment) = iter.next() {
            let permutation_product_eval = transcript.read_scalar()?;
            let permutation_product_next_eval = transcript.read_scalar()?;
            let permutation_product_last_eval = if iter.len() > 0 {
                Some(transcript.read_scalar()?)
            } else {
                None
            };

            sets.push(EvaluatedSet {
                permutation_product_commitment,
                permutation_product_eval,
                permutation_product_next_eval,
                permutation_product_last_eval,
            });
        }

        Ok(Evaluated { sets })
    }
}


/// The verifying key for a single permutation argument.
#[derive(Debug, Clone)]
pub struct PermutationVk<C: CurveAffine> {
    pub commitments: Vec<C>,
}

impl<C: CurveAffine> From<halo2_proofs::plonk::permutation::VerifyingKey<C>> for PermutationVk<C> {
    fn from(vk: halo2_proofs::plonk::permutation::VerifyingKey<C>) -> Self {
        PermutationVk {
            commitments: vk.commitments,
        }
    }
}

impl<C: CurveAffine> PermutationVk<C> {
    pub fn evaluate<E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
        &self,
        transcript: &mut T,
    ) -> Result<CommonEvaluated<C>, Error> {
        let permutation_evals = self
            .commitments
            .iter()
            .map(|_| transcript.read_scalar())
            .collect::<Result<Vec<_>, _>>()?;

        Ok(CommonEvaluated { permutation_evals })
    }
}

#[derive(Debug)]
pub struct CommonEvaluated<C: CurveAffine> {
    pub permutation_evals: Vec<C::Scalar>,
}


impl<C: CurveAffine> Evaluated<C> {
    pub fn expressions<'a>(
        &'a self,
        vk: &'a crate::vk::VerifyingKey<C>,
        p: &'a Argument,
        common: &'a CommonEvaluated<C>,
        advice_evals: &'a [C::Scalar],
        fixed_evals: &'a [C::Scalar],
        instance_evals: &'a [C::Scalar],
        l_0: C::Scalar,
        l_last: C::Scalar,
        l_blind: C::Scalar,
        beta: ChallengeBeta<C>,
        gamma: ChallengeGamma<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = C::Scalar> + 'a {
        let chunk_len = vk.cs_degree - 2;
        iter::empty()
            // Enforce only for the first set.
            // l_0(X) * (1 - z_0(X)) = 0
            .chain(
                self.sets.first().map(|first_set| {
                    l_0 * &(C::Scalar::one() - &first_set.permutation_product_eval)
                }),
            )
            // Enforce only for the last set.
            // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
            .chain(self.sets.last().map(|last_set| {
                (last_set.permutation_product_eval.square() - &last_set.permutation_product_eval)
                    * &l_last
            }))
            // Except for the first set, enforce.
            // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
            .chain(
                self.sets
                    .iter()
                    .skip(1)
                    .zip(self.sets.iter())
                    .map(|(set, last_set)| {
                        (
                            set.permutation_product_eval,
                            last_set.permutation_product_last_eval.unwrap(),
                        )
                    })
                    .map(move |(set, prev_last)| (set - &prev_last) * &l_0),
            )
            // And for all the sets we enforce:
            // (1 - (l_last(X) + l_blind(X))) * (
            //   z_i(\omega X) \prod (p(X) + \beta s_i(X) + \gamma)
            // - z_i(X) \prod (p(X) + \delta^i \beta X + \gamma)
            // )
            .chain(
                self.sets
                    .iter()
                    .zip(p.columns.chunks(chunk_len))
                    .zip(common.permutation_evals.chunks(chunk_len))
                    .enumerate()
                    .map(move |(chunk_index, ((set, columns), permutation_evals))| {
                        let mut left = set.permutation_product_next_eval;
                        for (eval, permutation_eval) in columns
                            .iter()
                            .map(|&column| match column.column_type() {
                                Any::Advice(_) => {
                                    advice_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                                }
                                Any::Fixed => {
                                    fixed_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                                }
                                Any::Instance => {
                                    instance_evals
                                        [vk.cs.get_any_query_index(column, Rotation::cur())]
                                }
                            })
                            .zip(permutation_evals.iter())
                        {
                            left *= &(eval + &(*beta * permutation_eval) + &*gamma);
                        }

                        let mut right = set.permutation_product_eval;
                        let mut current_delta = (*beta * &*x)
                            * &(C::Scalar::DELTA.pow_vartime(&[(chunk_index * chunk_len) as u64]));
                        for eval in columns.iter().map(|&column| match column.column_type() {
                            Any::Advice(_) => {
                                advice_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                            }
                            Any::Fixed => {
                                fixed_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                            }
                            Any::Instance => {
                                instance_evals[vk.cs.get_any_query_index(column, Rotation::cur())]
                            }
                        }) {
                            right *= &(eval + &current_delta + &*gamma);
                            current_delta *= &C::Scalar::DELTA;
                        }

                        (left - &right) * (C::Scalar::one() - &(l_last + &l_blind))
                    }),
            )
    }

    pub fn queries<'r, M: MSM<C> + 'r>(
        &'r self,
        vk: &'r crate::vk::VerifyingKey<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = VerifierQuery<'r, C, M>> + Clone {
        let blinding_factors = vk.cs.blinding_factors();
        let x_next = vk.domain.rotate_omega(*x, Rotation::next());
        let x_last = vk
            .domain
            .rotate_omega(*x, Rotation(-((blinding_factors + 1) as i32)));

        iter::empty()
            .chain(self.sets.iter().flat_map(move |set| {
                iter::empty()
                    // Open permutation product commitments at x and \omega^{-1} x
                    // Open permutation product commitments at x and \omega x
                    .chain(Some(VerifierQuery::new_commitment(
                        &set.permutation_product_commitment,
                        *x,
                        set.permutation_product_eval,
                    )))
                    .chain(Some(VerifierQuery::new_commitment(
                        &set.permutation_product_commitment,
                        x_next,
                        set.permutation_product_next_eval,
                    )))
            }))
            // Open it at \omega^{last} x for all but the last set
            .chain(self.sets.iter().rev().skip(1).flat_map(move |set| {
                Some(VerifierQuery::new_commitment(
                    &set.permutation_product_commitment,
                    x_last,
                    set.permutation_product_last_eval.unwrap(),
                ))
            }))
    }
}

impl<C: CurveAffine> CommonEvaluated<C> {
    pub fn queries<'r, M: MSM<C> + 'r>(
        &'r self,
        vkey: &'r PermutationVk<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = VerifierQuery<'r, C, M>> + Clone {
        // Open permutation commitments for each permutation argument at x
        vkey.commitments
            .iter()
            .zip(self.permutation_evals.iter())
            .map(move |(commitment, &eval)| VerifierQuery::new_commitment(commitment, *x, eval))
    }
}
