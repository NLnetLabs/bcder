//! Error Handling.
//!
//! This is a private module. Its public content is being re-exported by the
//! parent module.

use std::fmt;


//------------ Error ---------------------------------------------------------

/// An error happened while decoding data.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    /// The data didn’t conform to the expected structure.
    Malformed,

    /// An encoding used by the data is not yet implemented by the crate.
    Unimplemented,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Malformed => write!(f, "malformed data"),
            Error::Unimplemented => write!(f, "format not implemented"),
        }
    }
}
