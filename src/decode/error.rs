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
pub trait Error: error::Error + From<ContentError> + Sized {
    /// Returns an error signalling that decode wasn’t correctly encoded.
    fn malformed(msg: impl Into<ErrorMessage>) -> Self;

    /// Returns an error signalling that a certain encoding isn’t supported.
    ///
    /// This differs from `Error::malformed` in that the data is correctly
    /// encoded but the particular form of encoding isn’t supported.
    fn unimplemented(msg: impl Into<ErrorMessage>) -> Self;
}


//------------ ErrorMessage --------------------------------------------------

/// An error message converted for use with the [`Error`] trait.
///
/// This type is intended as an intermediary to make it possible to pass all
/// kinds of types as error message without explicit conversion. Any type `T`
/// that should be used as an error message should implement
/// `From<T> for ErrorMessage`. Alternatively, you can call
/// [`ErrorMessage::from_boxed`] for any boxed trait object of the standard
/// `Display` trait.
pub struct ErrorMessage {
    /// The actual yet hidden message.
    inner: ErrorMessageKind,
}

/// The actual error message as a hidden enum.
enum ErrorMessageKind {
    /// The error message is a static str.
    Static(&'static str),

    /// The error message is a boxed trait object.
    Boxed(Box<dyn fmt::Display + Send + Sync + 'static>),
}

impl ErrorMessage {
    /// Creates an error message from a static str.
    pub fn from_static(msg: &'static str) -> Self {
        ErrorMessage {
            inner: ErrorMessageKind::Static(msg)
        }
    }

    /// Creates an error message from a boxed trait object.
    pub fn from_boxed(
        msg: Box<dyn fmt::Display + Send + Sync + 'static>
    ) -> Self {
        ErrorMessage {
            inner: ErrorMessageKind::Boxed(msg)
        }
    }
}

impl From<&'static str> for ErrorMessage {
    fn from(msg: &'static str) -> Self {
        Self::from_static(msg)
    }
}

impl From<String> for ErrorMessage {
    fn from(msg: String) -> Self {
        Self::from_boxed(Box::new(msg))
    }
}

impl<T: Error + Send + Sync + 'static> From<T> for ErrorMessage {
    fn from(err: T) -> Self {
        Self::from_boxed(Box::new(err))
    }
}

impl fmt::Display for ErrorMessage {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            ErrorMessageKind::Static(msg) => f.write_str(msg),
            ErrorMessageKind::Boxed(ref msg) => msg.fmt(f),
        }
    }
}


//------------ ContentError --------------------------------------------------

/// An error for a source where the content can be wrong.
///
/// This is an `Error` type for all sources where acquiring the raw data
/// cannot fail. All errors need to be able to convert from this type.
pub struct ContentError {
    kind: ErrorKind,
    msg: ErrorMessage,
}

#[derive(Clone, Copy, Debug)]
enum ErrorKind {
    Malformed,
    Unimplemented,
}

impl Error for ContentError {
    fn malformed(msg: impl Into<ErrorMessage>) -> Self {
        ContentError {
            kind: ErrorKind::Malformed,
            msg: msg.into(),
        }
    }

    fn unimplemented(msg: impl Into<ErrorMessage>) -> Self {
        ContentError {
            kind: ErrorKind::Unimplemented,
            msg: msg.into()
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

