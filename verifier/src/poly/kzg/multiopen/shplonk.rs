use crate::arithmetic::{
    eval_polynomial, evaluate_vanishing_polynomial, lagrange_interpolate, powers, Field,
};
use crate::helpers::SerdeCurveAffine;
use crate::poly::commitment::Verifier;
use crate::poly::commitment::MSM;
use crate::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use crate::poly::kzg::msm::DualMSM;
use crate::poly::kzg::msm::{PreMSM, MSMKZG};
use crate::poly::kzg::strategy::GuardKZG;
use crate::poly::query::Query;
use crate::poly::query::{CommitmentReference, VerifierQuery};
use crate::poly::Error;
use crate::transcript::{ChallengeScalar, EncodedChallenge, TranscriptRead};
use alloc::{collections::BTreeSet, vec::Vec};
use core::fmt::Debug;
use core::ops::MulAssign;
use halo2curves::pairing::{Engine, MultiMillerLoop};
use halo2curves::CurveExt;

#[derive(Clone, Copy, Debug)]
struct U {}
type ChallengeU<F> = ChallengeScalar<F, U>;

#[derive(Clone, Copy, Debug)]
struct V {}
type ChallengeV<F> = ChallengeScalar<F, V>;

#[derive(Clone, Copy, Debug)]
struct Y {}
type ChallengeY<F> = ChallengeScalar<F, Y>;

#[derive(Debug, Clone, PartialEq)]
struct Commitment<F: Field, T: PartialEq + Clone>((T, Vec<F>));

impl<F: Field, T: PartialEq + Clone> Commitment<F, T> {
    fn get(&self) -> T {
        self.0 .0.clone()
    }

    fn evals(&self) -> Vec<F> {
        self.0 .1.clone()
    }
}

#[derive(Debug, Clone, PartialEq)]
struct RotationSet<F: Field, T: PartialEq + Clone> {
    commitments: Vec<Commitment<F, T>>,
    points: Vec<F>,
}

#[derive(Debug, PartialEq)]
struct IntermediateSets<F: Field, Q: Query<F>> {
    rotation_sets: Vec<RotationSet<F, Q::Commitment>>,
    super_point_set: BTreeSet<F>,
}

fn construct_intermediate_sets<F: Field + Ord, I, Q: Query<F, Eval = F>>(
    queries: I,
) -> IntermediateSets<F, Q>
where
    I: IntoIterator<Item = Q> + Clone,
{
    let queries = queries.into_iter().collect::<Vec<_>>();

    // Find evaluation of a commitment at a rotation
    let get_eval = |commitment: Q::Commitment, rotation: F| -> F {
        queries
            .iter()
            .find(|query| query.get_commitment() == commitment && query.get_point() == rotation)
            .unwrap()
            .get_eval()
    };

    // All points that appear in queries
    let mut super_point_set = BTreeSet::new();

    // Collect rotation sets for each commitment
    // Example elements in the vector:
    // (C_0, {r_5}),
    // (C_1, {r_1, r_2, r_3}),
    // (C_2, {r_2, r_3, r_4}),
    // (C_3, {r_2, r_3, r_4}),
    // ...
    let mut commitment_rotation_set_map: Vec<(Q::Commitment, BTreeSet<F>)> = vec![];
    for query in queries.iter() {
        let rotation = query.get_point();
        super_point_set.insert(rotation);
        if let Some(commitment_rotation_set) = commitment_rotation_set_map
            .iter_mut()
            .find(|(commitment, _)| *commitment == query.get_commitment())
        {
            let (_, rotation_set) = commitment_rotation_set;
            rotation_set.insert(rotation);
        } else {
            commitment_rotation_set_map.push((
                query.get_commitment(),
                BTreeSet::from_iter(core::iter::once(rotation)),
            ));
        };
    }

    // Flatten rotation sets and collect commitments that opens against each commitment set
    // Example elements in the vector:
    // {r_5}: [C_0],
    // {r_1, r_2, r_3} : [C_1]
    // {r_2, r_3, r_4} : [C_2, C_3],
    // ...
    // NOTE: we want to make the order of the collection of rotation sets independent of the opening points, to ease the verifier computation
    let mut rotation_set_commitment_map: Vec<(BTreeSet<F>, Vec<Q::Commitment>)> = vec![];
    for (commitment, rotation_set) in commitment_rotation_set_map.into_iter() {
        if let Some(rotation_set_commitment) = rotation_set_commitment_map
            .iter_mut()
            .find(|(set, _)| set == &rotation_set)
        {
            let (_, commitments) = rotation_set_commitment;
            commitments.push(commitment);
        } else {
            rotation_set_commitment_map.push((rotation_set, vec![commitment]));
        };
    }

    let rotation_sets = rotation_set_commitment_map
        .into_iter()
        .map(|(rotations, commitments)| {
            let rotations_vec = rotations.iter().collect::<Vec<_>>();
            let commitments: Vec<Commitment<F, Q::Commitment>> = commitments
                .into_iter()
                .map(|commitment| {
                    let evals: Vec<F> = rotations_vec
                        .iter()
                        .map(|&&rotation| get_eval(commitment, rotation))
                        .collect();
                    Commitment((commitment, evals))
                })
                .collect();

            RotationSet {
                commitments,
                points: rotations.into_iter().collect(),
            }
        })
        .collect::<Vec<RotationSet<_, _>>>();

    IntermediateSets {
        rotation_sets,
        super_point_set,
    }
}

/// Concrete KZG multiopen verifier with SHPLONK variant
#[derive(Debug)]
pub struct VerifierSHPLONK<'params, E: Engine> {
    params: &'params ParamsKZG<E>,
}

impl<'params, E> Verifier<'params, KZGCommitmentScheme<E>> for VerifierSHPLONK<'params, E>
where
    E: MultiMillerLoop + Debug,
    E::Fr: Ord,
    E::G1Affine: SerdeCurveAffine<ScalarExt = <E as Engine>::Fr, CurveExt = <E as Engine>::G1>,
    E::G1: CurveExt<AffineExt = E::G1Affine>,
    E::G2Affine: SerdeCurveAffine,
{
    type Guard = GuardKZG<'params, E>;
    type MSMAccumulator = DualMSM<'params, E>;

    const QUERY_INSTANCE: bool = false;

    fn new(params: &'params ParamsKZG<E>) -> Self {
        Self { params }
    }

    /// Verify a multi-opening proof
    fn verify_proof<
        'com,
        Ch: EncodedChallenge<E::G1Affine>,
        T: TranscriptRead<E::G1Affine, Ch>,
        I,
    >(
        &self,
        transcript: &mut T,
        queries: I,
        mut msm_accumulator: DualMSM<'params, E>,
    ) -> Result<Self::Guard, Error>
    where
        I: IntoIterator<Item = VerifierQuery<'com, E::G1Affine, MSMKZG<E>>> + Clone,
    {
        let intermediate_sets = construct_intermediate_sets(queries);
        let (rotation_sets, super_point_set) = (
            intermediate_sets.rotation_sets,
            intermediate_sets.super_point_set,
        );

        let y: ChallengeY<_> = transcript.squeeze_challenge_scalar();
        let v: ChallengeV<_> = transcript.squeeze_challenge_scalar();

        let h1 = transcript.read_point().map_err(|_| Error::SamplingError)?;
        let u: ChallengeU<_> = transcript.squeeze_challenge_scalar();
        let h2 = transcript.read_point().map_err(|_| Error::SamplingError)?;

        let (mut z_0_diff_inverse, mut z_0) = (E::Fr::ZERO, E::Fr::ZERO);
        let (mut outer_msm, mut r_outer_acc) = (PreMSM::<E>::new(), E::Fr::ZERO);
        for (i, (rotation_set, power_of_v)) in rotation_sets.iter().zip(powers(*v)).enumerate() {
            let diffs: Vec<E::Fr> = super_point_set
                .iter()
                .filter(|point| !rotation_set.points.contains(point))
                .copied()
                .collect();
            let mut z_diff_i = evaluate_vanishing_polynomial(&diffs[..], *u);

            // normalize coefficients by the coefficient of the first commitment
            if i == 0 {
                z_0 = evaluate_vanishing_polynomial(&rotation_set.points[..], *u);
                z_0_diff_inverse = z_diff_i.invert().unwrap();
                z_diff_i = E::Fr::ONE;
            } else {
                z_diff_i.mul_assign(z_0_diff_inverse);
            }

            let (mut inner_msm, r_inner_acc) = rotation_set
                .commitments
                .iter()
                .zip(powers(*y))
                .map(|(commitment_data, power_of_y)| {
                    // calculate low degree equivalent
                    let r_x = lagrange_interpolate(
                        &rotation_set.points[..],
                        &commitment_data.evals()[..],
                    );
                    let r_eval = power_of_y * eval_polynomial(&r_x[..], *u);
                    let msm = match commitment_data.get() {
                        CommitmentReference::Commitment(c) => {
                            let mut msm = MSMKZG::<E>::new();
                            msm.append_term(power_of_y, (*c).into());
                            msm
                        }
                        CommitmentReference::MSM(msm) => {
                            let mut msm = msm.clone();
                            msm.scale(power_of_y);
                            msm
                        }
                    };
                    (msm, r_eval)
                })
                .reduce(|(mut msm_acc, r_eval_acc), (msm, r_eval)| {
                    msm_acc.add_msm(&msm);
                    (msm_acc, r_eval_acc + r_eval)
                })
                .unwrap();

            inner_msm.scale(power_of_v * z_diff_i);
            outer_msm.add_msm(inner_msm);
            r_outer_acc += power_of_v * r_inner_acc * z_diff_i;
        }
        let mut outer_msm = outer_msm.normalize();
        let g1: E::G1 = self.params.g.into();
        outer_msm.append_term(-r_outer_acc, g1);
        outer_msm.append_term(-z_0, h1.into());
        outer_msm.append_term(*u, h2.into());

        msm_accumulator.left.append_term(E::Fr::ONE, h2.into());

        msm_accumulator.right.add_msm(&outer_msm);

        Ok(Self::Guard::new(msm_accumulator))
    }
}
