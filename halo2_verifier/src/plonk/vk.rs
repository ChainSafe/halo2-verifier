use crate::{
    arithmetic::{CurveAffine, Field},
    helpers::{ReadExt, SerdeCurveAffine, SerdeFormat, SerdePrimeField, WriteExt},
    io,
    plonk::{lookup, permutation, Advice, Any, Column, Fixed, Instance},
    poly::{EvaluationDomain, Rotation, SparsePolynomial, SparseTerm},
    transcript::{EncodedChallenge, Transcript},
};
use alloc::vec::Vec;

use super::shuffle;

/// This is a verifying key which allows for the verification of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct VerifyingKey<C: CurveAffine> {
    pub domain: EvaluationDomain<C::Scalar>,
    pub fixed_commitments: Vec<C>,
    pub permutation: permutation::VerifyingKey<C>,
    pub cs: ConstraintSystem<C::Scalar>,
    /// Cached maximum degree of `cs` (which doesn't change after construction).
    pub cs_degree: usize,
    /// The representative of this `VerifyingKey` in transcripts.
    pub transcript_repr: C::Scalar,
    pub selectors: Vec<Vec<bool>>,
}

impl<C: SerdeCurveAffine> VerifyingKey<C>
where
    C::Scalar: SerdePrimeField,
{
    /// Writes a verifying key to a buffer.
    ///
    /// Writes a curve element according to `format`:
    /// - `Processed`: Writes a compressed curve element with coordinates in standard form.
    ///   Writes a field element in standard form, with endianness specified by the
    ///   `PrimeField` implementation.
    /// - Otherwise: Writes an uncompressed curve element with coordinates in Montgomery form
    ///   Writes a field element into raw bytes in its internal Montgomery representation,
    ///   WITHOUT performing the expensive Montgomery reduction.
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        writer.write_u32(self.domain.k())?;
        writer.write_u32(self.fixed_commitments.len() as u32)?;
        for commitment in &self.fixed_commitments {
            commitment.write(writer, format)?;
        }

        writer.write_u32(self.cs_degree as u32)?;
        self.cs.write(writer, format)?;

        self.permutation.write(writer, format)?;

        // write self.selectors
        for selector in &self.selectors {
            // since `selector` is filled with `bool`, we pack them 8 at a time into bytes and then write
            for bits in selector.chunks(8) {
                writer.write_all(&[crate::helpers::pack(bits)])?;
            }
        }

        self.transcript_repr.write(writer, format)?;

        Ok(())
    }

    /// Reads a verification key from a buffer.
    ///
    /// Reads a curve element from the buffer and parses it according to the `format`:
    /// - `Processed`: Reads a compressed curve element and decompresses it.
    ///   Reads a field element in standard form, with endianness specified by the
    ///   `PrimeField` implementation, and checks that the element is less than the modulus.
    /// - `RawBytes`: Reads an uncompressed curve element with coordinates in Montgomery form.
    ///   Checks that field elements are less than modulus, and then checks that the point is on the curve.
    /// - `RawBytesUnchecked`: Reads an uncompressed curve element with coordinates in Montgomery form;
    ///   does not perform any checks
    pub fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let k = reader.read_u32()?;
        let num_fixed_columns = reader.read_u32()?;

        let fixed_commitments: Vec<_> = (0..num_fixed_columns)
            .map(|_| C::read(reader, format))
            .collect::<Result<_, _>>()?;

        let cs_degree = reader.read_u32()?;
        let cs = ConstraintSystem::read(reader, format)?;

        let domain = EvaluationDomain::new(cs_degree, k);

        let permutation = permutation::VerifyingKey::read(reader, &cs.permutation, format)?;

        // read selectors
        let selectors: Vec<Vec<bool>> = vec![vec![false; 1 << k]; cs.num_selectors]
            .into_iter()
            .map(|mut selector| {
                let mut selector_bytes = vec![0u8; (selector.len() + 7) / 8];
                reader.read_exact(&mut selector_bytes)?;
                for (bits, byte) in selector.chunks_mut(8).zip(selector_bytes) {
                    crate::helpers::unpack(byte, bits);
                }
                Ok(selector)
            })
            .collect::<io::Result<_>>()?;

        let transcript_repr = C::Scalar::read(reader, format)?;

        Ok(Self {
            domain,
            fixed_commitments,
            permutation,
            cs,
            cs_degree: cs_degree as usize,
            transcript_repr,
            selectors,
        })
    }

    /// Writes a verifying key to a vector of bytes using [`Self::write`].
    pub fn to_bytes(&self, format: SerdeFormat) -> Vec<u8> {
        let mut bytes = Vec::<u8>::with_capacity(self.bytes_length());
        Self::write(self, &mut bytes, format).expect("Writing to vector should not fail");
        bytes
    }

    /// Reads a verification key from a slice of bytes using [`Self::read`].
    pub fn from_bytes(mut bytes: &[u8], format: SerdeFormat) -> io::Result<Self> {
        Self::read(&mut bytes, format)
    }
}

impl<C: CurveAffine> VerifyingKey<C> {
    pub fn bytes_length(&self) -> usize {
        8 + (self.fixed_commitments.len() * C::default().to_bytes().as_ref().len())
            + self.permutation.bytes_length()
            + self.selectors.len()
                * (self
                    .selectors
                    .first()
                    .map(|selector| selector.len() / 8 + 1)
                    .unwrap_or(0))
            + self.cs.bytes_length()
            + 32
    }

    /// Hashes a verification key into a transcript.
    pub fn hash_into<E: EncodedChallenge<C>, T: Transcript<C, E>>(
        &self,
        transcript: &mut T,
    ) -> io::Result<()> {
        transcript.common_scalar(self.transcript_repr)?;

        Ok(())
    }

    /// Returns commitments of fixed polynomials
    pub fn fixed_commitments(&self) -> &Vec<C> {
        &self.fixed_commitments
    }

    /// Returns `VerifyingKey` of permutation
    pub fn permutation(&self) -> &permutation::VerifyingKey<C> {
        &self.permutation
    }

    /// Returns `ConstraintSystem`
    pub fn cs(&self) -> &ConstraintSystem<C::Scalar> {
        &self.cs
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
    pub gates: Vec<IndexedExpressionPoly>,

    // Contains an integer for each advice column
    // identifying how many distinct queries it has
    // so far; should be same length as num_advice_columns.
    pub num_advice_queries: Vec<usize>,
    pub advice_queries: Vec<(Column<Advice>, Rotation)>,
    pub instance_queries: Vec<(Column<Instance>, Rotation)>,
    pub fixed_queries: Vec<(Column<Fixed>, Rotation)>,

    // Permutation argument for performing equality constraints
    pub permutation: permutation::Argument,

    // Vector of lookup arguments, where each corresponds to a sequence of
    // input expressions and a sequence of table expressions involved in the lookup.
    pub lookups: Vec<lookup::Argument<F>>,

    // Vector of shuffle arguments, where each corresponds to a sequence of
    // input expressions and a sequence of shuffle expressions involved in the shuffle.
    pub shuffles: Vec<shuffle::Argument<F>>,

    pub coeff_vals: Vec<F>,
}

impl<F: SerdePrimeField> ConstraintSystem<F> {
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        writer.write_u32(self.num_fixed_columns as u32)?;
        writer.write_u32(self.num_advice_columns as u32)?;
        writer.write_u32(self.num_instance_columns as u32)?;
        writer.write_u32(self.num_selectors as u32)?;
        writer.write_u32(self.num_challenges as u32)?;
        writer.write_u32(self.gates.len() as u32)?;
        writer.write_u32(self.lookups.len() as u32)?;
        writer.write_u32(self.shuffles.len() as u32)?;
        writer.write_u32(self.coeff_vals.len() as u32)?;

        for phase in &self.advice_column_phase {
            writer.write_u8(*phase)?;
        }

        for phase in &self.challenge_phase {
            writer.write_u8(*phase)?;
        }

        for n in &self.num_advice_queries {
            writer.write_u32(*n as u32)?;
        }

        for query in &self.advice_queries {
            writer.write_u32(query.0.index as u32)?;
            writer.write_u8(query.0.column_type.phase())?;
            writer.write_i32(query.1 .0)?;
        }

        for query in &self.instance_queries {
            writer.write_u32(query.0.index as u32)?;
            writer.write_i32(query.1 .0)?;
        }

        for query in &self.fixed_queries {
            writer.write_u32(query.0.index as u32)?;
            writer.write_i32(query.1 .0)?;
        }

        self.permutation.write(writer)?;

        for expr in &self.gates {
            expr.write(writer, format)?;
        }

        for lookup in &self.lookups {
            lookup.write(writer, format)?;
        }

        for shuffle in &self.shuffles {
            shuffle.write(writer, format)?;
        }

        for value in &self.coeff_vals {
            value.write(writer, format)?;
        }

        Ok(())
    }

    fn read<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self> {
        let num_fixed_columns = reader.read_u32()? as usize;
        let num_advice_columns = reader.read_u32()? as usize;
        let num_instance_columns = reader.read_u32()? as usize;
        let num_selectors = reader.read_u32()? as usize;
        let num_challenges = reader.read_u32()? as usize;
        let num_gates = reader.read_u32()? as usize;
        let num_lookups = reader.read_u32()? as usize;
        let num_shuffles = reader.read_u32()? as usize;
        let num_coeff_vals = reader.read_u32()? as usize;

        let mut advice_column_phase = Vec::new();
        for _ in 0..num_advice_columns {
            advice_column_phase.push(reader.read_u8()?);
        }

        let mut challenge_phase = Vec::new();
        for _ in 0..num_challenges {
            challenge_phase.push(reader.read_u8()?);
        }

        let mut num_advice_queries = Vec::new();
        for _ in 0..num_advice_columns {
            num_advice_queries.push(reader.read_u32()? as usize);
        }

        let total_num_advice_queries = num_advice_queries.iter().sum::<usize>();
        let mut advice_queries = Vec::new();
        for _ in 0..total_num_advice_queries {
            let index = reader.read_u32()? as usize;
            let phase = reader.read_u8()?;
            let column = Column::<Advice>::new(index, Advice::new(phase));
            let rotation = reader.read_i32()?;
            advice_queries.push((column, Rotation(rotation)));
        }

        let mut instance_queries = Vec::new();
        for _ in 0..num_instance_columns {
            let index = reader.read_u32()? as usize;
            let rotation = reader.read_i32()?;
            instance_queries.push((Column::<Instance>::new(index, Instance), Rotation(rotation)));
        }

        let mut fixed_queries = Vec::new();
        for _ in 0..num_fixed_columns {
            let index = reader.read_u32()? as usize;
            let rotation = reader.read_i32()?;
            fixed_queries.push((Column::<Fixed>::new(index, Fixed), Rotation(rotation)));
        }

        let permutation = permutation::Argument::read(reader)?;

        let mut gates = Vec::new();
        for _ in 0..num_gates {
            gates.push(IndexedExpressionPoly::read(reader, format)?);
        }

        let mut lookups = Vec::new();
        for _ in 0..num_lookups {
            lookups.push(lookup::Argument::read(reader, format)?);
        }

        let mut shuffles = Vec::new();
        for _ in 0..num_shuffles {
            shuffles.push(shuffle::Argument::read(reader, format)?);
        }

        let mut coeff_vals: Vec<F> = Vec::new();
        for _ in 0..num_coeff_vals {
            coeff_vals.push(F::read(reader, format)?);
        }

        Ok(Self {
            num_fixed_columns,
            num_advice_columns,
            num_instance_columns,
            num_selectors,
            num_challenges,

            advice_column_phase,
            challenge_phase,
            num_advice_queries,
            advice_queries,
            instance_queries,
            fixed_queries,
            permutation,
            gates,
            lookups,
            shuffles,
            coeff_vals,
        })
    }
}

impl<F: Field> ConstraintSystem<F> {
    fn bytes_length(&self) -> usize {
        24 + self.advice_column_phase.len() * 8
            + self.challenge_phase.len() * 8
            + self.num_advice_queries.len() * 8
            + self.advice_queries.len() * 6
            + self.instance_queries.len() * 5
            + self.fixed_queries.len() * 5
            + self.permutation.bytes_length()
            + self
                .gates
                .iter()
                .map(|gate| gate.bytes_length())
                .sum::<usize>()
            + self
                .lookups
                .iter()
                .map(|lookup| lookup.bytes_length())
                .sum::<usize>()
            + self
                .shuffles
                .iter()
                .map(|shuffle| shuffle.bytes_length())
                .sum::<usize>()
    }

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
            .copied()
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

#[derive(Clone, Debug)]
pub struct ExpressionPoly<F: Field>(SparsePolynomial<F, SparseTerm>);

#[derive(Clone)]
pub struct IndexedExpressionPoly(SparsePolynomial<u16, SparseTerm>);

impl core::fmt::Debug for IndexedExpressionPoly {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        for (coeff, term) in self.0.terms.iter().filter(|(c, _)| *c != 0) {
            write!(f, "\n{:?} {:?}", coeff, term)?;
        }
        Ok(())
    }
}

impl IndexedExpressionPoly {
    pub fn new(poly: SparsePolynomial<u16, SparseTerm>) -> Self {
        IndexedExpressionPoly(poly)
    }

    pub fn evaluate<F: Field>(
        &self,
        coeffs: &[F],
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
                let coeff_idx = term.0;
                let sparse_term = &term.1;
                let coeff = coeffs[coeff_idx as usize];
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

    pub fn write<W: io::Write>(&self, writer: &mut W, _: SerdeFormat) -> io::Result<()> {
        writer.write_u32(self.0.num_vars as u32)?;
        writer.write_u32(self.0.terms.len() as u32)?;
        for (coeff, term) in &self.0.terms {
            writer.write_u16(*coeff as u16)?;
            writer.write_u32(term.0.len() as u32)?;
            for (var, pow) in &term.0 {
                writer.write_u32(*var as u32)?;
                writer.write_u32(*pow as u32)?;
            }
        }
        Ok(())
    }

    pub fn read<R: io::Read>(reader: &mut R, _: SerdeFormat) -> io::Result<Self> {
        let num_vars = reader.read_u32()? as usize;
        let num_terms = reader.read_u32()? as usize;
        let mut terms = Vec::with_capacity(num_terms);
        for _ in 0..num_terms {
            let coeff = reader.read_u16()?;
            let mut term_vars = Vec::with_capacity(num_vars);
            let term_num_vars = reader.read_u32()? as usize;
            for _ in 0..term_num_vars {
                let var = reader.read_u32()? as usize;
                let pow = reader.read_u32()? as usize;
                term_vars.push((var, pow));
            }
            terms.push((coeff, SparseTerm(term_vars)));
        }
        Ok(IndexedExpressionPoly(SparsePolynomial::new(
            num_vars, terms,
        )))
    }

    pub fn bytes_length(&self) -> usize {
        8 + self
            .0
            .terms
            .iter()
            .map(|(_, term)| 6 + term.0.len() + 16)
            .sum::<usize>()
    }
}

impl<F: Field> From<SparsePolynomial<F, SparseTerm>> for ExpressionPoly<F> {
    fn from(poly: SparsePolynomial<F, SparseTerm>) -> Self {
        ExpressionPoly(poly)
    }
}

impl<F: Field> ExpressionPoly<F> {
    pub fn num_vars(&self) -> usize {
        self.0.num_vars
    }

    pub fn terms(&self) -> &Vec<(F, SparseTerm)> {
        &self.0.terms
    }

    pub fn degree(&self) -> usize {
        self.0.degree()
    }
}

#[inline]
fn eval<F: Field>(coeff: &F, terms: &[(usize, usize)], var_access: impl Fn(usize) -> F) -> F {
    let mut result = F::ONE;
    terms.iter().for_each(|term| {
        let var = &var_access(term.0);
        result *= var.pow_vartime([term.1 as u64, 0, 0, 0]);
    });
    *coeff * result
}
