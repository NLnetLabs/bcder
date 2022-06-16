//! Error Handling.
//!
//! This is a private module. Its public content is being re-exported by the
//! parent module.

use std::{error, fmt};


//------------ Error ---------------------------------------------------------

/// A type representing an error that happened while decoding data.
///
/// Each [`Source`] defines its own error type that covers both errors
/// specific for the source as well as errors happening while interpreting
/// data.
///
/// For the latter case, i.e., the encoded data did not conform with the
/// specification, the method [`Error::malformed`] can be used to provide
/// additional information.
pub trait Error: Sized + error::Error {
    /// Returns an error signalling that decode wasn’t correctly encoded.
    fn malformed<T: fmt::Display + Send + Sync + 'static>(
        msg: T
    ) -> Self;

    /// Returns an error signalling that a certain encoding isn’t supported.
    ///
    /// This differs from `Error::malformed` in that the data is correctly
    /// encoded but the particular form of encoding isn’t supported.
    fn unimplemented<T: fmt::Display + Send + Sync + 'static>(
        msg: T
    ) -> Self;

    /// Converts the error into a different decoding error.
    fn convert_into<E: Error>(self) -> E;
}

