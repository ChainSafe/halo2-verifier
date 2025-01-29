// CLI method that reads a params file from a specified path and converts it to a space efficient format

use std::fs::File;
use std::io::{self, BufReader, Read, Write};

use halo2_proofs::poly::commitment::Params;
use halo2curves::bn256;

fn main() -> io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let file_path = &args[1];
    let absolute_path = std::env::current_dir()?.join(file_path);
    let file_name = absolute_path.file_name().unwrap().to_str().unwrap().split('.').next().unwrap();
    let out_path_dir = absolute_path.parent().unwrap();
    let out_path = args
        .get(2)
        .map(std::path::PathBuf::from)
        .unwrap_or(out_path_dir.join(format!("{}.zkverify.srs", file_name)));

    println!("Converting params from {} to {}", absolute_path.display(), out_path.display());

    let file = File::open(absolute_path)?;
    let mut reader = BufReader::new(file);

    let mut bytes = Vec::new();
    reader.read_to_end(&mut bytes)?;

    let params =
        halo2_proofs::poly::kzg::commitment::ParamsKZG::<bn256::Bn256>::read(&mut bytes.as_slice())
            .unwrap();

    let params = serialize::convert_params(params);

    let params_bytes = params.to_bytes();

    let mut file = File::create(out_path)?;
    file.write_all(&params_bytes)?;

    Ok(())
}
