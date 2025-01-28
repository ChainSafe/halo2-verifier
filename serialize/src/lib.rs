use halo2_proofs::arithmetic::Field;
use halo2_proofs::poly::commitment::Params;
use halo2_verifier::plonk::{
    shuffle, Advice, Column, ExpressionPoly, Fixed, IndexedExpressionPoly, Instance,
};
use halo2_verifier::poly::kzg::commitment::ParamsKZG;
use halo2_verifier::poly::{EvaluationDomain, Rotation, SparsePolynomial, SparseTerm, Term};
use halo2_verifier::{plonk::lookup, ConstraintSystem, VerifyingKey};
use halo2curves::bn256::{Bn256, G1Affine};
use halo2curves::CurveAffine;

pub fn convert_verifier_key(
    vk: halo2_proofs::plonk::VerifyingKey<G1Affine>,
) -> VerifyingKey<G1Affine> {
    VerifyingKey {
        domain: EvaluationDomain::new(vk.cs().degree() as u32, vk.get_domain().k()),
        fixed_commitments: vk.fixed_commitments().to_vec(),
        permutation: permutation::convert_permutation_vk(vk.permutation().clone()),
        cs: convert_constraint_system(vk.cs()),
        cs_degree: vk.cs().degree(),
        transcript_repr: vk.transcript_repr(),
        selectors: vk.selectors().to_vec(),
    }
}

pub fn convert_params(
    params: halo2_proofs::poly::kzg::commitment::ParamsKZG<Bn256>,
) -> ParamsKZG<Bn256> {
    ParamsKZG {
        k: params.k(),
        n: params.n(),
        g: params.g()[0],
        g2: params.g2(),
        s_g2: params.s_g2(),
    }
}

fn convert_constraint_system<F: Field + Ord>(
    cs: &halo2_proofs::plonk::ConstraintSystem<F>,
) -> ConstraintSystem<F> {
    let gates = cs
        .gates()
        .iter()
        .flat_map(|gate| {
            gate.polynomials()
                .iter()
                .map(|expr| expression_transform(cs, expr))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let mut field_values: Vec<F> = Vec::new();
    let gates = gates
        .iter()
        .map(|expr| {
            let terms = expr
                .terms()
                .iter()
                .map(|(coff, t)| {
                    let new_coff = index_element(&mut field_values, *coff);
                    (new_coff as u16, t.clone())
                })
                .collect::<Vec<_>>();
            IndexedExpressionPoly::new(SparsePolynomial {
                num_vars: expr.num_vars(),
                terms,
            })
        })
        .collect();

    let lookups = cs
        .lookups()
        .iter()
        .map(|lookup| {
            (
                lookup
                    .input_expressions()
                    .iter()
                    .map(|expr| expression_transform(cs, expr))
                    .collect::<Vec<_>>(),
                lookup
                    .table_expressions()
                    .iter()
                    .map(|expr| expression_transform(cs, expr))
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();

    let lookups = lookups
        .into_iter()
        .map(|l| {
            lookup::Argument::new(
                l.0.into_iter()
                    .map(|expr| {
                        let terms = expr
                            .terms()
                            .iter()
                            .map(|(coff, t)| {
                                let new_coff = index_element(&mut field_values, *coff);
                                (new_coff as u16, t.clone())
                            })
                            .collect::<Vec<_>>();
                        IndexedExpressionPoly::new(SparsePolynomial {
                            num_vars: expr.num_vars(),
                            terms,
                        })
                    })
                    .collect(),
                l.1.into_iter()
                    .map(|expr| {
                        let terms = expr
                            .terms()
                            .iter()
                            .map(|(coff, t)| {
                                let new_coff = index_element(&mut field_values, *coff);
                                (new_coff as u16, t.clone())
                            })
                            .collect::<Vec<_>>();
                        IndexedExpressionPoly::new(SparsePolynomial {
                            num_vars: expr.num_vars(),
                            terms,
                        })
                    })
                    .collect(),
            )
        })
        .collect();

    let shuffles = cs
        .shuffles()
        .iter()
        .map(|s| {
            (
                s.input_expressions()
                    .iter()
                    .map(|e| expression_transform(cs, e))
                    .collect::<Vec<_>>(),
                s.shuffle_expressions()
                    .iter()
                    .map(|e| expression_transform(cs, e))
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();

    let shuffles = shuffles
        .into_iter()
        .map(|s| {
            shuffle::Argument::new(
                s.0.into_iter()
                    .map(|expr| {
                        let terms = expr
                            .terms()
                            .iter()
                            .map(|(coff, t)| {
                                let new_coff = index_element(&mut field_values, *coff);
                                (new_coff as u16, t.clone())
                            })
                            .collect::<Vec<_>>();
                        IndexedExpressionPoly::new(SparsePolynomial {
                            num_vars: expr.num_vars(),
                            terms,
                        })
                    })
                    .collect(),
                s.1.into_iter()
                    .map(|expr| {
                        let terms = expr
                            .terms()
                            .iter()
                            .map(|(coff, t)| {
                                let new_coff = index_element(&mut field_values, *coff);
                                (new_coff as u16, t.clone())
                            })
                            .collect::<Vec<_>>();
                        IndexedExpressionPoly::new(SparsePolynomial {
                            num_vars: expr.num_vars(),
                            terms,
                        })
                    })
                    .collect(),
            )
        })
        .collect();

    ConstraintSystem {
        num_fixed_columns: cs.num_fixed_columns(),
        num_advice_columns: cs.num_advice_columns(),
        num_instance_columns: cs.num_instance_columns(),
        num_selectors: cs.num_selectors(),
        num_challenges: cs.num_challenges(),
        advice_column_phase: cs.advice_column_phase(),
        challenge_phase: cs.challenge_phase(),
        num_advice_queries: cs.num_advice_queries().clone(),
        gates,
        advice_queries: cs
            .advice_queries()
            .iter()
            .map(convert_advice_query)
            .collect(),
        instance_queries: cs
            .instance_queries()
            .iter()
            .map(convert_instance_query)
            .collect(),
        fixed_queries: cs.fixed_queries().iter().map(convert_fixed_query).collect(),
        permutation: permutation::convert_permutation_argument(cs.permutation().clone()),
        lookups,
        shuffles,
        coeff_vals: field_values,
    }
}

mod permutation {
    use super::*;
    use halo2_verifier::plonk::{
        permutation::{Argument, VerifyingKey},
        Advice, Any, Column,
    };

    pub fn convert_permutation_argument(
        arg: halo2_proofs::plonk::permutation::Argument,
    ) -> Argument {
        Argument {
            columns: arg
                .get_columns()
                .into_iter()
                .map(|col| Column {
                    index: col.index(),
                    column_type: match col.column_type() {
                        halo2_proofs::plonk::Any::Fixed => Any::Fixed,
                        halo2_proofs::plonk::Any::Advice(a) => Any::Advice(Advice::new(a.phase())),
                        halo2_proofs::plonk::Any::Instance => Any::Instance,
                    },
                })
                .collect(),
        }
    }

    pub fn convert_permutation_vk<C: CurveAffine>(
        vk: halo2_proofs::plonk::permutation::VerifyingKey<C>,
    ) -> VerifyingKey<C> {
        VerifyingKey {
            commitments: vk.commitments().to_vec(),
        }
    }
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

    expr.evaluate(
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
                    F::ONE,
                    SparseTerm::new(vec![(advice_range + query_index, 1)]),
                )],
            )
        },
        &|query| {
            let query_index =
                get_advice_query_index(cs, query.column_index(), query.phase(), query.rotation());
            SparsePolynomial::from_coefficients_vec(
                challenge_range,
                vec![(F::ONE, SparseTerm::new(vec![(query_index, 1)]))],
            )
        },
        &|query| {
            let query_index = get_instance_query_index(cs, query.column_index(), query.rotation());
            SparsePolynomial::from_coefficients_vec(
                challenge_range,
                vec![(
                    F::ONE,
                    SparseTerm::new(vec![(fixed_range + query_index, 1)]),
                )],
            )
        },
        &|challenge| {
            SparsePolynomial::from_coefficients_vec(
                challenge_range,
                vec![(
                    F::ONE,
                    SparseTerm::new(vec![(instance_range + challenge.index(), 1)]),
                )],
            )
        },
        &|a| -a,
        &|a, b| a + b,
        &|a, b| &a * &b,
        &|a, scalar| a * &scalar,
    )
    .into()
}

pub(crate) fn get_advice_query_index<F: Field>(
    cs: &halo2_proofs::plonk::ConstraintSystem<F>,
    column_index: usize,
    phase: u8,
    at: halo2_proofs::poly::Rotation,
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
    at: halo2_proofs::poly::Rotation,
) -> usize {
    for (index, (query_column, rotation)) in cs.fixed_queries().iter().enumerate() {
        if (query_column.index(), query_column.column_type(), rotation)
            == (column_index, &halo2_proofs::plonk::Fixed, &at)
        {
            return index;
        }
    }

    panic!("get_fixed_query_index called for non-existent query");
}

pub(crate) fn get_instance_query_index<F: Field>(
    cs: &halo2_proofs::plonk::ConstraintSystem<F>,
    column_index: usize,
    at: halo2_proofs::poly::Rotation,
) -> usize {
    for (index, (query_column, rotation)) in cs.instance_queries().iter().enumerate() {
        if (query_column.index(), query_column.column_type(), rotation)
            == (column_index, &halo2_proofs::plonk::Instance, &at)
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

fn convert_advice_query(
    (col, rot): &(
        halo2_proofs::plonk::Column<halo2_proofs::plonk::Advice>,
        halo2_proofs::poly::Rotation,
    ),
) -> (Column<Advice>, Rotation) {
    (
        Column {
            index: col.index(),
            column_type: Advice::new(col.column_type().phase()),
        },
        Rotation(rot.0),
    )
}

fn convert_fixed_query(
    (col, rot): &(
        halo2_proofs::plonk::Column<halo2_proofs::plonk::Fixed>,
        halo2_proofs::poly::Rotation,
    ),
) -> (Column<Fixed>, Rotation) {
    (
        Column {
            index: col.index(),
            column_type: Fixed,
        },
        Rotation(rot.0),
    )
}

fn convert_instance_query(
    (col, rot): &(
        halo2_proofs::plonk::Column<halo2_proofs::plonk::Instance>,
        halo2_proofs::poly::Rotation,
    ),
) -> (Column<Instance>, Rotation) {
    (
        Column {
            index: col.index(),
            column_type: Instance,
        },
        Rotation(rot.0),
    )
}
