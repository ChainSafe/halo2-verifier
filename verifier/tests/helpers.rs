use halo2_proofs::{
    halo2curves::bn256::{self, Bn256},
    plonk::{create_proof, keygen_pk, keygen_vk, Circuit},
    poly::{commitment::Params, kzg::commitment::ParamsKZG},
    transcript::TranscriptWriterBuffer as _,
};
use halo2_verifier::{
    poly::kzg::{
        commitment::KZGCommitmentScheme, multiopen::VerifierSHPLONK, strategy::SingleStrategy,
    },
    transcript::{Blake2bRead, Challenge255, TranscriptReadBuffer},
    verify_proof, VerifyingKey,
};
use rand::{rngs::StdRng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use serialize::convert_params;

pub fn test_verifier<ConcreteCircuit: Circuit<bn256::Fr>>(
    k: u32,
    circuit: &ConcreteCircuit,
    pi: Option<Vec<bn256::Fr>>,
    expected: bool,
) {
    let params = gen_srs(k);

    let vk = keygen_vk(&params, circuit).unwrap();
    let pk = keygen_pk(&params, vk.clone(), circuit).unwrap();
    let vk: VerifyingKey<_> = serialize::convert_verifier_key(vk);
    // let vk_bytes = vk.to_bytes(SerdeFormat::Processed);
    // let vk = VerifyingKey::<_>::from_bytes(&vk_bytes, SerdeFormat::Processed).unwrap();

    let rng = &mut StdRng::from_seed(Default::default());

    let proof = {
        let mut transcript = halo2_proofs::transcript::Blake2bWrite::<
            _,
            _,
            halo2_proofs::transcript::Challenge255<_>,
        >::init(vec![]);
        let instance = if let Some(ref pi) = pi {
            vec![&pi[..]]
        } else {
            vec![]
        };

        create_proof::<
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

    let instance = if let Some(ref pi) = pi {
        vec![&pi[..]]
    } else {
        vec![]
    };
    let params = convert_params(params);
    let strategy = SingleStrategy::new(&params);
    let result = verify_proof::<
        KZGCommitmentScheme<bn256::Bn256>,
        VerifierSHPLONK<bn256::Bn256>,
        _,
        _,
        _,
    >(&params, &vk, strategy, &[&instance[..]], &mut transcript)
    .is_ok();

    assert_eq!(result, expected);
}

pub fn gen_srs(k: u32) -> ParamsKZG<Bn256> {
    let dir = "./params".to_string();
    let path = format!("{dir}/kzg_bn254_{k}.srs");
    match std::fs::read(path.as_str()) {
        Ok(b) => {
            println!("read params from {path}");
            ParamsKZG::<Bn256>::read(&mut b.as_slice()).unwrap()
        }
        Err(_) => {
            println!("creating params for {k}");
            std::fs::create_dir_all(dir).unwrap();
            let params = ParamsKZG::<Bn256>::setup(k, ChaCha20Rng::from_seed(Default::default()));
            let mut bytes = vec![];
            params.write(&mut bytes).unwrap();
            std::fs::write(path.as_str(), bytes).unwrap();
            params
        }
    }
}
