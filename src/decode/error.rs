//! Error Handling.
//!
//! This is a private module. Its public content is being re-exported by the
//! parent module.


//------------ Error ---------------------------------------------------------

/// An error happened while decoding data.
#[derive(Clone, Copy, Debug, Eq, Fail, PartialEq)]
pub enum Error {
    /// The data didn’t conform to the expected structure.
    #[fail(display="malformed data")]
    Malformed,

    /// An encoding used by the data is not yet implemented by the crate.
    #[fail(display="format not implemented")]
    Unimplemented,
}

