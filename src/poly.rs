//! A sparse multivariate polynomial represented in coefficient form.
use ff::Field;
use num_traits::Zero;
//use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use core::ops::{Deref, Mul, MulAssign};
use core::{
    cmp::Ordering,
    fmt,
    ops::{Add, AddAssign, Neg, Sub, SubAssign},
};
use alloc::vec::Vec;

/// Stores a sparse multivariate polynomial in coefficient form.
#[derive(Clone)]
pub struct SparsePolynomial<F, T: Term> {
    /// The number of variables the polynomial supports

    pub num_vars: usize,
    /// List of each term along with its coefficient
    pub terms: Vec<(F, T)>,
}

impl<F: Field, T: Term> SparsePolynomial<F, T> {
    fn remove_zeros(&mut self) {
        self.terms.retain(|(c, _)| !bool::from(c.is_zero()));
    }
}

impl<F> SparsePolynomial<F, SparseTerm> {

    /// Returns the total degree of the polynomial
    ///
    /// # Examples
    /// ```
    /// use ark_poly::{
    ///     polynomial::multivariate::{SparsePolynomial, SparseTerm},
    ///     DenseMVPolynomial, Polynomial,
    /// };
    /// use ark_std::test_rng;
    /// use ark_test_curves::bls12_381::Fq;
    ///
    /// let rng = &mut test_rng();
    /// // Create a multivariate polynomial of degree 7
    /// let poly: SparsePolynomial<Fq, SparseTerm> = SparsePolynomial::rand(7, 2, rng);
    /// assert_eq!(poly.degree(), 7);
    /// ```
    pub fn degree(&self) -> usize {
        self.terms
            .iter()
            .map(|(_, term)| term.degree())
            .max()
            .unwrap_or(0)
    }


    pub fn evaluate<R>(&self, term_eval: impl Fn(&(F, SparseTerm)) -> R, term_add: impl Fn(R, R) -> R) -> R {
        let term_len = self.terms.len();
        let mut result = term_eval(&self.terms.get(0).unwrap());
        let mut i = 1;
        while i < term_len {
            let r = term_eval(&self.terms.get(i).unwrap());
            i = i + 1;
            result = term_add(result, r);
        };
        result
    }
}

impl<F: Field + Ord> SparsePolynomial<F, SparseTerm> {
    /// Returns the number of variables in `self`
    fn num_vars(&self) -> usize {
        self.num_vars
    }


    pub fn from_coefficients_vec(num_vars: usize, mut terms: Vec<(F, SparseTerm)>) -> Self {
        // Ensure that terms are in ascending order.
        terms.sort_by(|(_, t1), (_, t2)| t1.cmp(t2));
        // If any terms are duplicated, add them together
        let mut terms_dedup: Vec<(F, SparseTerm)> = Vec::new();
        for term in terms {
            if let Some(prev) = terms_dedup.last_mut() {
                if prev.1 == term.1 {
                    *prev = (prev.0 + term.0, prev.1.clone());
                    continue;
                }
            };
            // Assert correct number of indeterminates
            assert!(
                term.1.iter().all(|(var, _)| *var < num_vars),
                "Invalid number of indeterminates"
            );
            terms_dedup.push(term);
        }
        let mut result = Self {
            num_vars,
            terms: terms_dedup,
        };
        // Remove any terms with zero coefficients
        result.remove_zeros();
        result
    }

    // /// Returns the terms of a `self` as a list of tuples of the form `(coeff, Self::Term)`
    // fn terms(&self) -> &[(F, Self::Term)] {
    //     self.terms.as_slice()
    // }
}


impl<F: Field, T: Term> Add for SparsePolynomial<F, T> {
    type Output = SparsePolynomial<F, T>;

    fn add(self, other: SparsePolynomial<F, T>) -> Self {
        &self + &other
    }
}

impl<'a, 'b, F: Field, T: Term> Add<&'a SparsePolynomial<F, T>> for &'b SparsePolynomial<F, T> {
    type Output = SparsePolynomial<F, T>;

    fn add(self, other: &'a SparsePolynomial<F, T>) -> SparsePolynomial<F, T> {
        let mut result = Vec::new();
        let mut cur_iter = self.terms.iter().peekable();
        let mut other_iter = other.terms.iter().peekable();
        // Since both polynomials are sorted, iterate over them in ascending order,
        // combining any common terms
        loop {
            // Peek at iterators to decide which to take from
            let which = match (cur_iter.peek(), other_iter.peek()) {
                (Some(cur), Some(other)) => Some((cur.1).cmp(&other.1)),
                (Some(_), None) => Some(Ordering::Less),
                (None, Some(_)) => Some(Ordering::Greater),
                (None, None) => None,
            };
            // Push the smallest element to the `result` coefficient vec
            let smallest = match which {
                Some(Ordering::Less) => cur_iter.next().unwrap().clone(),
                Some(Ordering::Equal) => {
                    let other = other_iter.next().unwrap();
                    let cur = cur_iter.next().unwrap();
                    (cur.0 + other.0, cur.1.clone())
                }
                Some(Ordering::Greater) => other_iter.next().unwrap().clone(),
                None => break,
            };
            result.push(smallest);
        }
        // Remove any zero terms
        result.retain(|(c, _)| !bool::from(c.is_zero()));
        SparsePolynomial {
            num_vars: core::cmp::max(self.num_vars, other.num_vars),
            terms: result,
        }
    }
}

impl<'a, F: Field, T: Term> AddAssign<&'a SparsePolynomial<F, T>> for SparsePolynomial<F, T> {
    fn add_assign(&mut self, other: &'a SparsePolynomial<F, T>) {
        *self = &*self + other;
    }
}

#[allow(clippy::suspicious_op_assign_impl)]
impl<'a, F: Field, T: Term> AddAssign<(F, &'a SparsePolynomial<F, T>)> for SparsePolynomial<F, T> {
    fn add_assign(&mut self, (f, other): (F, &'a SparsePolynomial<F, T>)) {
        let other = Self {
            num_vars: other.num_vars,
            terms: other
                .terms
                .iter()
                .map(|(coeff, term)| (*coeff * f, term.clone()))
                .collect(),
        };
        // Note the call to `Add` will remove also any duplicates
        *self = &*self + &other;
    }
}

impl<F: Field, T: Term> Neg for SparsePolynomial<F, T> {
    type Output = SparsePolynomial<F, T>;

    #[inline]
    fn neg(mut self) -> SparsePolynomial<F, T> {
        for coeff in &mut self.terms {
            (coeff).0 = -coeff.0;
        }
        self
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<'a, 'b, F: Field, T: Term> Sub<&'a SparsePolynomial<F, T>> for &'b SparsePolynomial<F, T> {
    type Output = SparsePolynomial<F, T>;

    #[inline]
    fn sub(self, other: &'a SparsePolynomial<F, T>) -> SparsePolynomial<F, T> {
        let neg_other = other.clone().neg();
        self + &neg_other
    }
}

impl<'a, F: Field, T: Term> SubAssign<&'a SparsePolynomial<F, T>> for SparsePolynomial<F, T> {
    #[inline]
    fn sub_assign(&mut self, other: &'a SparsePolynomial<F, T>) {
        *self = &*self - other;
    }
}

impl<F: Field, T: Term> fmt::Debug for SparsePolynomial<F, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        for (coeff, term) in self.terms.iter().filter(|(c, _)| !bool::from(c.is_zero())) {
            if term.is_constant() {
                write!(f, "\n{:?}", coeff)?;
            } else {
                write!(f, "\n{:?} {:?}", coeff, term)?;
            }
        }
        Ok(())
    }
}

impl<F: Field, T: Term> Zero for SparsePolynomial<F, T> {
    /// Returns the zero polynomial.
    fn zero() -> Self {
        Self {
            num_vars: 0,
            terms: Vec::new(),
        }
    }

    /// Checks if the given polynomial is zero.
    fn is_zero(&self) -> bool {
        self.terms.is_empty() || self.terms.iter().all(|(c, _)| c.is_zero().into())
    }
}

impl<'a, 'b, F: Field + Ord> Mul<&'a SparsePolynomial<F, SparseTerm>>
    for &'b SparsePolynomial<F, SparseTerm>
{
    type Output = SparsePolynomial<F, SparseTerm>;

    /// Perform a naive n^2 multiplication of `self` by `other`.
    #[inline]
    fn mul(self, other: &'a SparsePolynomial<F, SparseTerm>) -> SparsePolynomial<F, SparseTerm> {
        if self.is_zero() || other.is_zero() {
            SparsePolynomial::zero()
        } else {
            let mut result_terms = Vec::new();
            for (cur_coeff, cur_term) in self.terms.iter() {
                for (other_coeff, other_term) in other.terms.iter() {
                    let mut term = cur_term.deref().to_vec();
                    term.extend(other_term.deref());
                    result_terms.push((*cur_coeff * *other_coeff, SparseTerm::new(term)));
                }
            }
            SparsePolynomial::from_coefficients_vec(self.num_vars, result_terms)
        }
    }
}

impl<'a, F: Field + Ord, T: Term> Mul<&'a F> for SparsePolynomial<F, T> {
    type Output = SparsePolynomial<F, T>;

    /// Perform a naive n^2 multiplication of `self` by `other`.
    #[inline]
    fn mul(mut self, other: &'a F) -> SparsePolynomial<F, T> {
        self *= other;
        self
    }
}

impl<'a, F: Field + Ord, T: Term> MulAssign<&'a F> for SparsePolynomial<F, T> {
    #[inline]
    fn mul_assign(&mut self, other: &'a F) {
        if self.is_zero() || bool::from(other.is_zero()) {
            *self = SparsePolynomial::zero();
        } else {
            self.terms.iter_mut().for_each(|(coeff, _)| *coeff *= other);
        }
    }
}


/// Describes the interface for a term (monomial) of a multivariate polynomial.
pub trait Term:
Clone
+ PartialOrd
+ Ord
+ PartialEq
+ Eq
//+ Hash
+ Default
+ fmt::Debug
// + Deref<Target = [(usize, usize)]>
+ Send
+ Sync
+
// + CanonicalSerialize
// + CanonicalDeserialize
{
    /// Create a new `Term` from a list of tuples of the form `(variable, power)`
    fn new(term: Vec<(usize, usize)>) -> Self;

    /// Returns the total degree of `self`. This is the sum of all variable
    /// powers in `self`
    fn degree(&self) -> usize;

    // /// Returns a list of variables in `self`
    // fn vars(&self) -> Vec<usize>;

    // /// Returns a list of the powers of each variable in `self`
    // fn powers(&self) -> Vec<usize>;

    /// Returns whether `self` is a constant
    fn is_constant(&self) -> bool;

    // /// Evaluates `self` at the point `p`.
    // fn evaluate<F: Field>(&self, p: &[F]) -> F;
}

/// Stores a term (monomial) in a multivariate polynomial.
/// Each element is of the form `(variable, power)`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct SparseTerm(pub(crate) Vec<(usize, usize)>);

impl SparseTerm {
    /// Sums the powers of any duplicated variables. Assumes `term` is sorted.
    fn combine(term: &[(usize, usize)]) -> Vec<(usize, usize)> {
        let mut term_dedup: Vec<(usize, usize)> = Vec::new();
        for (var, pow) in term {
            if let Some(prev) = term_dedup.last_mut() {
                if prev.0 == *var {
                    prev.1 += pow;
                    continue;
                }
            }
            term_dedup.push((*var, *pow));
        }
        term_dedup
    }
}

impl Term for SparseTerm {
    /// Create a new `Term` from a list of tuples of the form `(variable, power)`
    fn new(mut term: Vec<(usize, usize)>) -> Self {
        // Remove any terms with power 0
        term.retain(|(_, pow)| *pow != 0);
        // If there are more than one variables, make sure they are
        // in order and combine any duplicates
        if term.len() > 1 {
            term.sort_by(|(v1, _), (v2, _)| v1.cmp(v2));
            term = Self::combine(&term);
        }
        Self(term)
    }

    /// Returns the sum of all variable powers in `self`
    fn degree(&self) -> usize {
        self.0.iter().fold(0, |sum, acc| sum + acc.1)
    }

    // /// Returns a list of variables in `self`
    // fn vars(&self) -> Vec<usize> {
    //     self.iter().map(|(v, _)| *v).collect()
    // }

    // /// Returns a list of variable powers in `self`
    // fn powers(&self) -> Vec<usize> {
    //     self.iter().map(|(_, p)| *p).collect()
    // }

    /// Returns whether `self` is a constant
    fn is_constant(&self) -> bool {
        self.len() == 0 || self.degree() == 0
    }

    // /// Evaluates `self` at the given `point` in the field.
    // fn evaluate<F: Field>(&self, point: &[F]) -> F {
    //     self.iter()
    //         .map(|(var, power)| point[*var].pow([*power as u64]))
    //         .product()
    // }
}


impl Deref for SparseTerm {
    type Target = [(usize, usize)];

    fn deref(&self) -> &[(usize, usize)] {
        &self.0
    }
}

impl PartialOrd for SparseTerm {
    /// Sort by total degree. If total degree is equal then ordering
    /// is given by exponent weight in lower-numbered variables
    /// ie. `x_1 > x_2`, `x_1^2 > x_1 * x_2`, etc.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.degree() != other.degree() {
            Some(self.degree().cmp(&other.degree()))
        } else {
            // Iterate through all variables and return the corresponding ordering
            // if they differ in variable numbering or power
            for (cur, other) in self.iter().zip(other.iter()) {
                if other.0 == cur.0 {
                    if cur.1 != other.1 {
                        return Some((cur.1).cmp(&other.1));
                    }
                } else {
                    return Some((other.0).cmp(&cur.0));
                }
            }
            Some(Ordering::Equal)
        }
    }
}

impl Ord for SparseTerm {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}
