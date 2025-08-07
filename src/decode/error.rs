//! Error Handling.
//!
//! This is a private module. Its public content is being re-exported by the
//! parent module.

use std::{error, fmt, io};
use crate::length::Length;


//------------ Error ---------------------------------------------------------

/// An error happened while decoding data.
///
/// This can either be a source error – which the type is generic over – or a
/// content error annotated with the position in the source where it happened.
#[derive(Debug)]
pub struct Error {
    err: io::Error,
    pos: Length,
}

impl Error {
    /// Creates a new decode error from an IO error and a position.
    //
    //  This is not named “new” since we may change the internal
    //  representation later and not use an io::Error.
    pub fn from_io(err: io::Error, pos: Length) -> Self {
        Self { err, pos }
    }

    pub fn content(
        err: impl Into<Box<dyn error::Error + Send + Sync>>,
        pos: Length,
    ) -> Self {
        Self {
            err: io::Error::new(io::ErrorKind::InvalidData, err),
            pos,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} (at position {})", self.err, self.pos)
    }
}

impl error::Error for Error { }

