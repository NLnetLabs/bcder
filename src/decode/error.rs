//! Error Handling.
//!
//! This is a private module. Its public content is being re-exported by the
//! parent module.

use std::{error, fmt};
use std::convert::Infallible;
use super::source::Pos;


//------------ ContentError --------------------------------------------------

/// An error happened while interpreting BER-encoded data.
pub struct ContentError {
    /// The error message.
    message: ErrorMessage,
}

impl ContentError {
    /// Creates a content error from a static str.
    pub fn from_static(msg: &'static str) -> Self {
        ContentError {
            message: ErrorMessage::Static(msg)
        }
    }

    /// Creates a content error from a boxed trait object.
    pub fn from_boxed(
        msg: Box<dyn fmt::Display + Send + Sync + 'static>
    ) -> Self {
        ContentError {
            message: ErrorMessage::Boxed(msg)
        }
    }
}

impl From<&'static str> for ContentError {
    fn from(msg: &'static str) -> Self {
        Self::from_static(msg)
    }
}

impl From<String> for ContentError {
    fn from(msg: String) -> Self {
        Self::from_boxed(Box::new(msg))
    }
}

impl From<DecodeError<Infallible>> for ContentError {
    fn from(err: DecodeError<Infallible>) -> Self {
        match err.inner {
            DecodeErrorKind::Source(_) => unreachable!(),
            DecodeErrorKind::Content { error, .. } => error,
        }
    }
}


impl fmt::Display for ContentError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.message.fmt(f)
    }
}

impl fmt::Debug for ContentError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("ContentError")
            .field(&self.message)
            .finish()
    }
}


//------------ ErrorMessage --------------------------------------------------

/// The actual error message as a hidden enum.
enum ErrorMessage {
    /// The error message is a static str.
    Static(&'static str),

    /// The error message is a boxed trait object.
    Boxed(Box<dyn fmt::Display + Send + Sync + 'static>),
}

impl fmt::Display for ErrorMessage {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorMessage::Static(msg) => f.write_str(msg),
            ErrorMessage::Boxed(ref msg) => msg.fmt(f),
        }
    }
}

impl fmt::Debug for ErrorMessage {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorMessage::Static(msg) => f.write_str(msg),
            ErrorMessage::Boxed(ref msg) => msg.fmt(f),
        }
    }
}


//------------ DecodeError ---------------------------------------------------

/// An error happened while decoding data.
///
/// This can either be a source error – which the type is generic over – or a
/// content error annotated with the position in the source where it happened.
#[derive(Debug)]
pub struct DecodeError<S> {
    inner: DecodeErrorKind<S>,
}

#[derive(Debug)]
enum DecodeErrorKind<S> {
    Source(S),
    Content {
        error: ContentError,
        pos: Pos,
    }
}

impl<S> DecodeError<S> {
    /// Creates a decode error from a content error and a position.
    pub fn content(error: impl Into<ContentError>, pos: Pos) -> Self {
        DecodeError {
            inner: DecodeErrorKind::Content { error: error.into(), pos },
        }
    }
}

impl DecodeError<Infallible> {
    /// Converts a decode error from an infallible source into another error.
    pub fn convert<S>(self) -> DecodeError<S> {
        match self.inner {
            DecodeErrorKind::Source(_) => unreachable!(),
            DecodeErrorKind::Content { error, pos } => {
                DecodeError::content(error, pos)
            }
        }
    }
}

impl<S> From<S> for DecodeError<S> {
    fn from(err: S) -> Self {
        DecodeError { inner: DecodeErrorKind::Source(err) }
    }
}

impl<S: fmt::Display> fmt::Display for DecodeError<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            DecodeErrorKind::Source(ref err) => err.fmt(f),
            DecodeErrorKind::Content { ref error, pos } => {
                write!(f, "{} (at position {})", error, pos)
            }
        }
    }
}

impl<S: fmt::Display + fmt::Debug> error::Error for DecodeError<S> { }

