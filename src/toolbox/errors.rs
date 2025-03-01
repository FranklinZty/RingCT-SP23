//! Error module.

use ark_serialize::SerializationError;
use ark_std::string::String;
use displaydoc::Display;

/// A `enum` specifying the possible failure modes of the Transcript.
#[derive(Display, Debug)]
pub enum TranscriptError {
    /// Invalid Transcript: {0}
    InvalidTranscript(String),
    /// An error during (de)serialization: {0}
    SerializationError(SerializationError),
}

impl From<SerializationError> for TranscriptError {
    fn from(e: SerializationError) -> Self {
        Self::SerializationError(e)
    }
}

#[derive(Display, Debug)]
pub enum CommitmentErrors {
    /// Invalid Prover: {0}
    InvalidProver(String),
    /// Invalid Verifier: {0}
    InvalidVerifier(String),
    /// Invalid Proof: {0}
    InvalidProof(String),
    /// Invalid parameters: {0}
    InvalidParameters(String),
    /// An error during (de)serialization: {0}
    SerializationError(SerializationError),
}

impl From<SerializationError> for CommitmentErrors {
    fn from(e: SerializationError) -> Self {
        Self::SerializationError(e)
    }
}

#[derive(Display, Debug)]
pub enum SigmaErrors {
    /// Invalid Prover: {0}
    InvalidProver(String),
    /// Invalid Verifier: {0}
    InvalidVerifier(String),
    /// Invalid Proof: {0}
    InvalidProof(String),
    /// Invalid parameters: {0}
    InvalidParameters(String),
    /// Transcript error {0}
    TranscriptError(TranscriptError),
    /// Pedersen error {0}
    CommitmentErrors(CommitmentErrors),
    /// An error during (de)serialization: {0}
    SerializationError(SerializationError),
}

impl From<TranscriptError> for SigmaErrors {
    fn from(e: TranscriptError) -> Self {
        Self::TranscriptError(e)
    }
}

impl From<CommitmentErrors> for SigmaErrors {
    fn from(e: CommitmentErrors) -> Self {
        Self::CommitmentErrors(e)
    }
}

impl From<SerializationError> for SigmaErrors {
    fn from(e: SerializationError) -> Self {
        Self::SerializationError(e)
    }
}
