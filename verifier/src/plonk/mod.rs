use crate::io;
use core::fmt;

use crate::transcript::ChallengeScalar;

pub mod circuit;
pub mod lookup;
pub mod permutation;
pub(crate) mod vanishing;
pub(crate) mod vk;

pub use circuit::*;
pub use vk::*;

/// This is an error that could occur during proving or circuit synthesis.
// TODO: these errors need to be cleaned up
#[derive(Debug)]
pub enum Error {
    /// The provided instances do not match the circuit parameters.
    InvalidInstances,
    /// The constraint system is not satisfied.
    ConstraintSystemFailure,
    /// Out of bounds index passed to a backend
    BoundsFailure,
    /// Opening error
    Opening,
    /// Transcript error
    Transcript(crate::io::Error),
    /// Instance provided exceeds number of available rows
    InstanceTooLarge,
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        // The only place we can get io::Error from is the transcript.
        Error::Transcript(error)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidInstances => write!(f, "Provided instances do not match the circuit"),
            Error::ConstraintSystemFailure => write!(f, "The constraint system is not satisfied"),
            Error::BoundsFailure => write!(f, "An out-of-bounds index was passed to the backend"),
            Error::Opening => write!(f, "Multi-opening proof was invalid"),
            Error::Transcript(e) => write!(f, "Transcript error: {}", e),
            Error::InstanceTooLarge => write!(f, "Instance vectors are larger than the circuit"),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Theta;
pub type ChallengeTheta<F> = ChallengeScalar<F, Theta>;

#[derive(Clone, Copy, Debug)]
pub struct Beta;
pub type ChallengeBeta<F> = ChallengeScalar<F, Beta>;

#[derive(Clone, Copy, Debug)]
pub struct Gamma;
pub type ChallengeGamma<F> = ChallengeScalar<F, Gamma>;

#[derive(Clone, Copy, Debug)]
pub struct Y;
pub type ChallengeY<F> = ChallengeScalar<F, Y>;

#[derive(Clone, Copy, Debug)]
pub struct X;
pub type ChallengeX<F> = ChallengeScalar<F, X>;
