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
}


//------------ ContentError --------------------------------------------------

/// An error for a source where the content can be wrong.
///
/// This is an `Error` type for all sources where acquiring the raw data
/// cannot fail. All errors need to be able to convert from this type.
pub struct ContentError {
    kind: ErrorKind,
    msg: Box<dyn fmt::Display + Send + Sync>,
}

#[derive(Clone, Copy, Debug)]
enum ErrorKind {
    Malformed,
    Unimplemented,
}

impl Error for ContentError {
    fn malformed<T: fmt::Display + Send + Sync + 'static>(
        msg: T
    ) -> Self {
        ContentError {
            kind: ErrorKind::Malformed,
            msg: Box::new(msg)
        }
    }

    fn unimplemented<T: fmt::Display + Send + Sync + 'static>(
        msg: T
    ) -> Self {
        ContentError {
            kind: ErrorKind::Unimplemented,
            msg: Box::new(msg)
        }
    }
}

impl fmt::Debug for ContentError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("ContentError")
            .field("kind", &self.kind)
            .field("msg", &format_args!("{}", &self.msg))
            .finish()
    }
}

impl fmt::Display for ContentError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            ErrorKind::Malformed => write!(f, "malformed data")?,
            ErrorKind::Unimplemented => write!(f, "format not implemented")?,
        }
        write!(f, ": {}", self.msg)
    }
}

impl error::Error for ContentError { }

