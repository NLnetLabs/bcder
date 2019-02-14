//! Error Handling.
//!
//! This is a private module. Its public content is being re-exported by the
//! parent module.


//------------ Error ---------------------------------------------------------

/// An error happened while decoding data.
#[derive(Clone, Copy, Debug, Display, Eq, PartialEq)]
pub enum Error {
    /// The data didn’t conform to the expected structure.
    #[display(fmt="malformed data")]
    Malformed,

    /// An encoding used by the data is not yet implemented by the crate.
    #[display(fmt="format not implemented")]
    Unimplemented,
}

