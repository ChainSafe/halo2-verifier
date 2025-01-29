use core::iter;
use ff::BatchInvert;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{floor_planner::V1, Layouter, Value},
    plonk::{
        keygen_pk, keygen_vk, Advice, Challenge, Circuit, Column, ConstraintSystem, Error,
        Expression, FirstPhase, SecondPhase, Selector,
    },
    poly::{commitment::Params, Rotation},
    transcript::TranscriptWriterBuffer,
};
use halo2_verifier::{
    poly::kzg::{
        commitment::KZGCommitmentScheme, multiopen::VerifierSHPLONK, strategy::SingleStrategy,
    },
    transcript::{Blake2bRead, Challenge255, TranscriptReadBuffer},
};
use halo2curves::bn256;
use rand::{rngs::StdRng, RngCore, SeedableRng};

use rand_chacha::ChaCha20Rng;

fn rand_2d_array<F: Field, R: RngCore, const W: usize, const H: usize>(rng: &mut R) -> [[F; H]; W] {
    [(); W].map(|_| [(); H].map(|_| F::random(&mut *rng)))
}

fn shuffled<F: Field, R: RngCore, const W: usize, const H: usize>(
    original: [[F; H]; W],
    rng: &mut R,
) -> [[F; H]; W] {
    let mut shuffled = original;

    for row in (1..H).rev() {
        let rand_row = (rng.next_u32() as usize) % row;
        for column in shuffled.iter_mut() {
            column.swap(row, rand_row);
        }
    }

    shuffled
}

#[derive(Clone)]
struct MyConfig<const W: usize> {
    q_shuffle: Selector,
    q_first: Selector,
    q_last: Selector,
    original: [Column<Advice>; W],
    shuffled: [Column<Advice>; W],
    theta: Challenge,
    gamma: Challenge,
    z: Column<Advice>,
}

impl<const W: usize> MyConfig<W> {
    fn configure<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        let [q_shuffle, q_first, q_last] = [(); 3].map(|_| meta.selector());
        // First phase
        let original = [(); W].map(|_| meta.advice_column_in(FirstPhase));
        let shuffled = [(); W].map(|_| meta.advice_column_in(FirstPhase));
        let [theta, gamma] = [(); 2].map(|_| meta.challenge_usable_after(FirstPhase));
        // Second phase
        let z = meta.advice_column_in(SecondPhase);

        meta.create_gate("z should start with 1", |meta| {
            let q_first = meta.query_selector(q_first);
            let z = meta.query_advice(z, Rotation::cur());
            let one = Expression::Constant(F::ONE);

            vec![q_first * (one - z)]
        });

        meta.create_gate("z should end with 1", |meta| {
            let q_last = meta.query_selector(q_last);
            let z = meta.query_advice(z, Rotation::cur());
            let one = Expression::Constant(F::ONE);

            vec![q_last * (one - z)]
        });

        meta.create_gate("z should have valid transition", |meta| {
            let q_shuffle = meta.query_selector(q_shuffle);
            let original = original.map(|advice| meta.query_advice(advice, Rotation::cur()));
            let shuffled = shuffled.map(|advice| meta.query_advice(advice, Rotation::cur()));
            let [theta, gamma] = [theta, gamma].map(|challenge| meta.query_challenge(challenge));
            let [z, z_w] =
                [Rotation::cur(), Rotation::next()].map(|rotation| meta.query_advice(z, rotation));

            // Compress
            let original = original
                .iter()
                .cloned()
                .reduce(|acc, a| acc * theta.clone() + a)
                .unwrap();
            let shuffled = shuffled
                .iter()
                .cloned()
                .reduce(|acc, a| acc * theta.clone() + a)
                .unwrap();

            vec![q_shuffle * (z * (original + gamma.clone()) - z_w * (shuffled + gamma))]
        });

        Self {
            q_shuffle,
            q_first,
            q_last,
            original,
            shuffled,
            theta,
            gamma,
            z,
        }
    }
}

#[derive(Clone, Default)]
struct MyCircuit<F: Field, const W: usize, const H: usize> {
    original: Value<[[F; H]; W]>,
    shuffled: Value<[[F; H]; W]>,
}

impl<F: Field, const W: usize, const H: usize> MyCircuit<F, W, H> {
    fn rand<R: RngCore>(rng: &mut R) -> Self {
        let original = rand_2d_array::<F, _, W, H>(rng);
        let shuffled = shuffled(original, rng);

        Self {
            original: Value::known(original),
            shuffled: Value::known(shuffled),
        }
    }
}

impl<F: Field, const W: usize, const H: usize> Circuit<F> for MyCircuit<F, W, H> {
    type Config = MyConfig<W>;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MyConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let theta = layouter.get_challenge(config.theta);
        let gamma = layouter.get_challenge(config.gamma);

        layouter.assign_region(
            || "Shuffle original into shuffled",
            |mut region| {
                // Keygen
                config.q_first.enable(&mut region, 0)?;
                config.q_last.enable(&mut region, H)?;
                for offset in 0..H {
                    config.q_shuffle.enable(&mut region, offset)?;
                }

                // First phase
                for (idx, (&column, values)) in config
                    .original
                    .iter()
                    .zip(self.original.transpose_array().iter())
                    .enumerate()
                {
                    for (offset, &value) in values.transpose_array().iter().enumerate() {
                        region.assign_advice(
                            || format!("original[{}][{}]", idx, offset),
                            column,
                            offset,
                            || value,
                        )?;
                    }
                }
                for (idx, (&column, values)) in config
                    .shuffled
                    .iter()
                    .zip(self.shuffled.transpose_array().iter())
                    .enumerate()
                {
                    for (offset, &value) in values.transpose_array().iter().enumerate() {
                        region.assign_advice(
                            || format!("shuffled[{}][{}]", idx, offset),
                            column,
                            offset,
                            || value,
                        )?;
                    }
                }

                // Second phase
                let z = self.original.zip(self.shuffled).zip(theta).zip(gamma).map(
                    |(((original, shuffled), theta), gamma)| {
                        let mut product = vec![F::ZERO; H];
                        for (idx, product) in product.iter_mut().enumerate() {
                            let mut compressed = F::ZERO;
                            for value in shuffled.iter() {
                                compressed *= theta;
                                compressed += value[idx];
                            }

                            *product = compressed + gamma
                        }

                        product.iter_mut().batch_invert();

                        for (idx, product) in product.iter_mut().enumerate() {
                            let mut compressed = F::ZERO;
                            for value in original.iter() {
                                compressed *= theta;
                                compressed += value[idx];
                            }

                            *product *= compressed + gamma
                        }

                        #[allow(clippy::let_and_return)]
                        let z = iter::once(F::ONE)
                            .chain(product)
                            .scan(F::ONE, |state, cur| {
                                *state *= &cur;
                                Some(*state)
                            })
                            .collect::<Vec<_>>();

                        z
                    },
                );
                for (offset, value) in z.transpose_vec(H + 1).into_iter().enumerate() {
                    region.assign_advice(
                        || format!("z[{}]", offset),
                        config.z,
                        offset,
                        || value,
                    )?;
                }

                Ok(())
            },
        )
    }
}

// ANCHOR_END: circuit

fn main() {
    const W: usize = 4;
    const H: usize = 32;
    const K: u32 = 8;

    let rng = &mut StdRng::from_seed(Default::default());

    let circuit = &MyCircuit::<_, W, H>::rand(rng);

    let params = gen_srs(K);

    let vk = keygen_vk(&params, circuit).unwrap();
    let pk = keygen_pk(&params, vk.clone(), circuit).unwrap();

    let rng = &mut StdRng::from_seed(Default::default());

    let proof = {
        let mut transcript = halo2_proofs::transcript::Blake2bWrite::<
            _,
            _,
            halo2_proofs::transcript::Challenge255<_>,
        >::init(vec![]);
        let instance = [];

        halo2_proofs::plonk::create_proof::<
            halo2_proofs::poly::kzg::commitment::KZGCommitmentScheme<bn256::Bn256>,
            halo2_proofs::poly::kzg::multiopen::ProverSHPLONK<bn256::Bn256>,
            _,
            _,
            _,
            _,
        >(
            &params,
            &pk,
            std::slice::from_ref(circuit),
            &[&instance[..]],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");

        transcript.finalize()
    };

    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

    let instance = [];
    let params = serialize::convert_params(params);
    let vk = serialize::convert_verifier_key(vk);
    let strategy = SingleStrategy::new(&params);
    let result = halo2_verifier::verify_proof::<
        KZGCommitmentScheme<bn256::Bn256>,
        VerifierSHPLONK<bn256::Bn256>,
        _,
        _,
        _,
    >(&params, &vk, strategy, &[&instance[..]], &mut transcript)
    .is_ok();

    assert!(result);
}

pub fn gen_srs(k: u32) -> halo2_proofs::poly::kzg::commitment::ParamsKZG<bn256::Bn256> {
    let dir = "./params".to_string();
    let path = format!("{dir}/kzg_bn254_{k}.srs");
    match std::fs::read(path.as_str()) {
        Ok(b) => {
            println!("read params from {path}");
            halo2_proofs::poly::kzg::commitment::ParamsKZG::<bn256::Bn256>::read(&mut b.as_slice())
                .unwrap()
        }
        Err(_) => {
            println!("creating params for {k}");
            std::fs::create_dir_all(dir).unwrap();
            let params = halo2_proofs::poly::kzg::commitment::ParamsKZG::<bn256::Bn256>::setup(
                k,
                ChaCha20Rng::from_seed(Default::default()),
            );
            let mut bytes = vec![];
            params.write(&mut bytes).unwrap();
            std::fs::write(path.as_str(), bytes).unwrap();
            params
        }
    }
}
