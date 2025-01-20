use core::marker::PhantomData;

use alloc::vec::Vec;
use ff::Field;
use halo2_proofs::{
    arithmetic::CurveAffine,
    halo2curves, io,
    plonk::{
        lookup::{Committed, PermutationCommitments},
        Advice, Any, Column, Error, Fixed, Instance, Selector, VirtualCell,
    },
    poly::{EvaluationDomain, Rotation},
    transcript::{EncodedChallenge, Transcript, TranscriptRead},
};

use crate::{
    plonk::{lookup, permutation},
    poly::{SparsePolynomial, SparseTerm, Term},
};

/// This is a verifying key which allows for the verification of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct VerifyingKey<C: CurveAffine> {
    pub domain: EvaluationDomain<C::Scalar>,
    pub fixed_commitments: Vec<C>,
    pub permutation: permutation::PermutationVk<C>,
    pub cs: ConstraintSystem<C::Scalar>,
    /// Cached maximum degree of `cs` (which doesn't change after construction).
    pub cs_degree: usize,
    /// The representative of this `VerifyingKey` in transcripts.
    pub transcript_repr: C::Scalar,
    pub selectors: Vec<Vec<bool>>,
}

impl<C: CurveAffine> VerifyingKey<C> {
    /// Hashes a verification key into a transcript.
    pub fn hash_into<E: EncodedChallenge<C>, T: Transcript<C, E>>(
        &self,
        transcript: &mut T,
    ) -> io::Result<()> {
        transcript.common_scalar(self.transcript_repr)?;

        Ok(())
    }
}

impl<C: CurveAffine> From<halo2_proofs::plonk::VerifyingKey<C>> for VerifyingKey<C> {
    fn from(vk: halo2_proofs::plonk::VerifyingKey<C>) -> Self {
        Self {
            domain: vk.domain,
            fixed_commitments: vk.fixed_commitments,
            permutation: vk.permutation.into(),
            cs: vk.cs.into(),
            cs_degree: vk.cs_degree,
            transcript_repr: vk.transcript_repr,
            selectors: vk.selectors,
        }
    }
}

/// This is a description of the circuit environment, such as the gate, column and
/// permutation arrangements.
#[derive(Debug, Clone)]
pub struct ConstraintSystem<F: Field> {
    pub num_fixed_columns: usize,
    pub num_advice_columns: usize,
    pub num_instance_columns: usize,
    pub num_selectors: usize,
    pub num_challenges: usize,

    /// Contains the phase for each advice column. Should have same length as num_advice_columns.
    pub advice_column_phase: Vec<u8>,
    /// Contains the phase for each challenge. Should have same length as num_challenges.
    pub challenge_phase: Vec<u8>,

    /// This is a cached vector that maps virtual selectors to the concrete
    /// fixed column that they were compressed into. This is just used by dev
    /// tooling right now.
    // pub(crate) selector_map: Vec<Column<Fixed>>,
    pub gates: Vec<ExpressionPoly<F>>,
    pub advice_queries: Vec<(Column<Advice>, Rotation)>,
    // Contains an integer for each advice column
    // identifying how many distinct queries it has
    // so far; should be same length as num_advice_columns.
    num_advice_queries: Vec<usize>,
    pub instance_queries: Vec<(Column<Instance>, Rotation)>,
    pub fixed_queries: Vec<(Column<Fixed>, Rotation)>,

    // Permutation argument for performing equality constraints
    pub permutation: permutation::Argument,

    // Vector of lookup arguments, where each corresponds to a sequence of
    // input expressions and a sequence of table expressions involved in the lookup.
    pub lookups: Vec<lookup::Argument<F>>,
    // Vector of fixed columns, which can be used to store constant values
    // that are copied into advice columns.
    // pub(crate) constants: Vec<Column<Fixed>>,

    // pub(crate) minimum_degree: Option<usize>,

    // pub fields_pool: Vec<F>,
}

impl<F: Field + Ord> From<halo2_proofs::plonk::ConstraintSystem<F>> for ConstraintSystem<F> {
    fn from(cs: halo2_proofs::plonk::ConstraintSystem<F>) -> Self {
        let gates = cs
            .gates
            .iter()
            .flat_map(|gate| {
                gate.polynomials()
                    .iter()
                    .map(|expr| expression_transform(&cs, expr))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // let mut fields_pool: Vec<F> = Vec::new();
        // let gates = gates
        //     .iter()
        //     .map(|expr| {
        //         let terms = expr
        //             .0
        //             .terms
        //             .iter()
        //             .map(|(coff, t)| {
        //                 let new_coff = index_element(&mut fields_pool, *coff);
        //                 (new_coff as u16, t.clone())
        //             })
        //             .collect::<Vec<_>>();
        //         IndexedExpressionPoly::new(SparsePolynomial {
        //             num_vars: expr.0.num_vars,
        //             terms,
        //         })
        //     })
        //     .collect();

        let lookups = cs
            .lookups
            .iter()
            .map(|lookup| lookup::Argument {
                input_expressions: lookup
                    .input_expressions
                    .iter()
                    .map(|expr| expression_transform(&cs, expr))
                    .collect(),
                table_expressions: lookup
                    .table_expressions
                    .iter()
                    .map(|expr| expression_transform(&cs, expr))
                    .collect(),
            })
            .collect();

        Self {
            num_fixed_columns: cs.num_fixed_columns,
            num_advice_columns: cs.num_advice_columns,
            num_instance_columns: cs.num_instance_columns,
            num_selectors: cs.num_selectors,
            num_challenges: cs.num_challenges,
            advice_column_phase: cs.advice_column_phase(),
            challenge_phase: cs.challenge_phase(),
            num_advice_queries: cs.num_advice_queries,
            gates,
            advice_queries: cs.advice_queries,
            instance_queries: cs.instance_queries,
            fixed_queries: cs.fixed_queries,
            permutation: cs.permutation.into(),
            lookups,
            // fields_pool,
        }
    }
}

impl<F: Field> ConstraintSystem<F> {
    /// Compute the number of blinding factors necessary to perfectly blind
    /// each of the prover's witness polynomials.
    pub fn blinding_factors(&self) -> usize {
        let factors = *self.num_advice_queries.iter().max().unwrap_or(&1);
        let factors = core::cmp::max(3, factors);
        let factors = factors + 1;
        factors + 1
    }

    pub fn phases(&self) -> impl Iterator<Item = u8> {
        let max_phase = self
            .advice_column_phase
            .iter()
            .max()
            .map(|phase| *phase)
            .unwrap_or_default();
        0..=max_phase
    }

    pub fn get_any_query_index(&self, column: Column<Any>, at: Rotation) -> usize {
        match column.column_type() {
            Any::Advice(_) => {
                self.get_advice_query_index(Column::<Advice>::try_from(column).unwrap(), at)
            }
            Any::Fixed => {
                self.get_fixed_query_index(Column::<Fixed>::try_from(column).unwrap(), at)
            }
            Any::Instance => {
                self.get_instance_query_index(Column::<Instance>::try_from(column).unwrap(), at)
            }
        }
    }

    pub(crate) fn get_advice_query_index(&self, column: Column<Advice>, at: Rotation) -> usize {
        for (index, advice_query) in self.advice_queries.iter().enumerate() {
            if advice_query == &(column, at) {
                return index;
            }
        }

        panic!("get_advice_query_index called for non-existent query");
    }

    pub(crate) fn get_fixed_query_index(&self, column: Column<Fixed>, at: Rotation) -> usize {
        for (index, fixed_query) in self.fixed_queries.iter().enumerate() {
            if fixed_query == &(column, at) {
                return index;
            }
        }

        panic!("get_fixed_query_index called for non-existent query");
    }

    pub(crate) fn get_instance_query_index(&self, column: Column<Instance>, at: Rotation) -> usize {
        for (index, instance_query) in self.instance_queries.iter().enumerate() {
            if instance_query == &(column, at) {
                return index;
            }
        }

        panic!("get_instance_query_index called for non-existent query");
    }
}

// /// Gate
// #[derive(Clone, Debug)]
// // pub struct Gate<F: Field> {
//     pub polys: Vec<IndexedExpressionPoly<F>>,
//     /// We track queried selectors separately from other cells, so that we can use them to
//     /// trigger debug checks on gates.
//     // queried_selectors: Vec<Selector>,
//     // queried_cells: Vec<VirtualCell>,
// }

// impl<F: Field> Gate<F> {
//     /// Returns constraints of this gate
//     pub fn polynomials(&self) -> &[ExpressionPoly<F>] {
//         self.polys.as_slice()
//     }

//     // pub fn queried_selectors(&self) -> &[Selector] {
//     //     &self.queried_selectors
//     // }

//     // pub fn queried_cells(&self) -> &[VirtualCell] {
//     //     &self.queried_cells
//     // }
// }

#[derive(Clone, Debug)]
pub struct ExpressionPoly<F: Field>(SparsePolynomial<F, SparseTerm>);

#[derive(Clone, Debug)]
pub struct IndexedExpressionPoly<F: Field>(SparsePolynomial<F, SparseTerm>, PhantomData<F>);

impl<F: Field> ExpressionPoly<F> {
    pub fn evaluate(
        &self,
        // coeffs: &Vec<F>,
        advice_evals: &[F],
        fixed_evals: &[F],
        instance_evals: &[F],
        challenges: &[F],
    ) -> F {
        let advice_range = advice_evals.len();
        let fixed_range = advice_range + fixed_evals.len();
        let instance_range = fixed_range + instance_evals.len();
        let challenge_range = instance_range + challenges.len();

        self.0.evaluate(
            |term| {
                let coeff = term.0;
                let sparse_term = &term.1;
                // let coeff = &coeffs[coeff_idx as usize];
                eval(&coeff, &sparse_term.0, |idx| {
                    if idx < advice_range {
                        advice_evals[idx]
                    } else if idx < fixed_range {
                        fixed_evals[idx - advice_range]
                    } else if idx < instance_range {
                        instance_evals[idx - fixed_range]
                    } else if idx < challenge_range {
                        challenges[idx - instance_range]
                    } else {
                        panic!("index out of range");
                    }
                })
            },
            |a, b| a + b,
        )
    }

    pub fn degree(&self) -> usize {
        self.0.degree()
    }
}

#[inline]
fn eval<F: Field>(coeff: &F, terms: &[(usize, usize)], var_access: impl Fn(usize) -> F) -> F {
    let mut result = F::one();
    terms.iter().for_each(|term| {
        let var = &var_access(term.0);
        result *= var.pow_vartime([term.1 as u64, 0, 0, 0]);
    });
    *coeff * result
}

/// basicly, we treat every queries and challenges as a variable, so there will be `advice_queries_len+fixed_queries_len+instance_queries_len+challenges_len` variables.
/// and the orders should be the same as that in `expression.move`.
fn expression_transform<F: Field + Ord>(
    cs: &halo2_proofs::plonk::ConstraintSystem<F>,
    expr: &halo2_proofs::plonk::Expression<F>,
) -> ExpressionPoly<F> {
    let advice_range = cs.advice_queries().len();
    let fixed_range = advice_range + cs.fixed_queries().len();
    let instance_range = fixed_range + cs.instance_queries().len();
    let challenge_range = instance_range + cs.challenge_phase().len();

    ExpressionPoly(expr.evaluate(
        &|c| {
            SparsePolynomial::from_coefficients_vec(
                challenge_range,
                vec![(c, SparseTerm::default())],
            )
        },
        &|_| panic!("virtual selectors are removed during optimization"),
        &|query| {
            let query_index = get_fixed_query_index(cs, query.column_index(), query.rotation());
            SparsePolynomial::from_coefficients_vec(
                challenge_range,
                vec![(
                    F::one(),
                    SparseTerm::new(vec![(advice_range + query_index, 1)]),
                )],
            )
        },
        &|query| {
            let query_index =
                get_advice_query_index(cs, query.column_index(), query.phase(), query.rotation());
            SparsePolynomial::from_coefficients_vec(
                challenge_range,
                vec![(F::one(), SparseTerm::new(vec![(query_index, 1)]))],
            )
        },
        &|query| {
            let query_index = get_instance_query_index(cs, query.column_index(), query.rotation());
            SparsePolynomial::from_coefficients_vec(
                challenge_range,
                vec![(
                    F::one(),
                    SparseTerm::new(vec![(fixed_range + query_index, 1)]),
                )],
            )
        },
        &|challenge| {
            SparsePolynomial::from_coefficients_vec(
                challenge_range,
                vec![(
                    F::one(),
                    SparseTerm::new(vec![(instance_range + challenge.index(), 1)]),
                )],
            )
        },
        &|a| -a,
        &|a, b| a + b,
        &|a, b| &a * &b,
        &|a, scalar| a * &scalar,
    ))
}

pub(crate) fn get_advice_query_index<F: Field>(
    cs: &halo2_proofs::plonk::ConstraintSystem<F>,
    column_index: usize,
    phase: u8,
    at: Rotation,
) -> usize {
    for (index, (query_column, rotation)) in cs.advice_queries().iter().enumerate() {
        if (
            query_column.index(),
            query_column.column_type().phase(),
            rotation,
        ) == (column_index, phase, &at)
        {
            return index;
        }
    }

    panic!("get_advice_query_index called for non-existent query");
}

pub(crate) fn get_fixed_query_index<F: Field>(
    cs: &halo2_proofs::plonk::ConstraintSystem<F>,
    column_index: usize,
    at: Rotation,
) -> usize {
    for (index, (query_column, rotation)) in cs.fixed_queries().iter().enumerate() {
        if (query_column.index(), query_column.column_type(), rotation)
            == (column_index, &Fixed, &at)
        {
            return index;
        }
    }

    panic!("get_fixed_query_index called for non-existent query");
}

pub(crate) fn get_instance_query_index<F: Field>(
    cs: &halo2_proofs::plonk::ConstraintSystem<F>,
    column_index: usize,
    at: Rotation,
) -> usize {
    for (index, (query_column, rotation)) in cs.instance_queries().iter().enumerate() {
        if (query_column.index(), query_column.column_type(), rotation)
            == (column_index, &Instance, &at)
        {
            return index;
        }
    }

    panic!("get_instance_query_index called for non-existent query");
}

fn index_element<T: Eq>(pool: &mut Vec<T>, elem: T) -> usize {
    if let Some(pos) = pool.iter().position(|e| e == &elem) {
        pos
    } else {
        pool.push(elem);
        pool.len() - 1
    }
}
