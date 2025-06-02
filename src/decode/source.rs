//! Reading raw data.
//!
//! This module privates some items that are used internally only.

use std::{error, fmt, io};
use crate::length::Length;


//------------ Source --------------------------------------------------------

/// Enhances an `io::Read` for decoding.
///
/// This type wraps an IO reader and provides functionality used when decoding
/// data.
///
/// It implements both `io::Read` and `io::BufRead` if the underlying reader
/// implements them.
///
/// It keeps track of the amount of data read or consumed so we can enforce
/// the length limits of definite length values. The current read position is
/// available via the [`pos`][Self::pos] method.
///
/// Additionally, the source can track an error that happened during reading.
/// This error can be set via the [`set_err`][Self::set_err]. If set, any
/// subsequent read attempts will fail and return an error.
///
/// This functionality is used by the value decoder types which check whether
/// their content has been fully read in their destructors and need a way to
/// signal an error if they haven’t been exhausted.
pub struct Source<R> {
    /// The underlying reader.
    ///
    /// We are using this convoluted name to make it more likely that we
    /// use the `Self::reader` method to access it which considers the
    /// status.
    wrapped_reader: R,

    /// The status of the source.
    ///
    /// We don’t put the reader as the `Ok(_)` case here so that we can
    /// retrive it via `Self::into_reader` even the status has changed to an
    /// error.
    status: Result<(), SourceError>,

    /// The current read position.
    pos: Length,
}

impl<R> Source<R> {
    /// Creates a new source wrapping the given reader.
    ///
    /// Sets the initial position to zero.
    pub fn new(reader: R) -> Self {
        Self::with_pos(reader, Length::default())
    }

    /// Creates a new source with the given explicit start position.
    pub fn with_pos(reader: R, pos: Length) -> Self {
        Self {
            wrapped_reader: reader,
            status: Ok(()),
            pos,
        }
    }

    /// Checks the status of the source.
    ///
    /// Returns an error if the status was set to an error.
    pub fn check_status(&mut self) -> Result<(), io::Error> {
        if let Err(err) = self.status.as_mut() {
            return Err(err.create_io_error());
        }
        Ok(())
    }

    /// Changes the status to the given error.
    ///
    /// After calling this method, all attempts of reading will result in an
    /// error.
    pub fn set_err(&mut self, err: SourceError) {
        self.status = Err(err)
    }

    /// Return the current read position.
    pub fn pos(&self) -> Length {
        self.pos
    }

    /// Return the underlying reader.
    ///
    /// If the status has been changed to an error, returns an error.
    fn reader(&mut self) -> Result<&mut R, io::Error> {
        self.status.as_mut().map_err(|err| err.create_io_error())?;
        Ok(&mut self.wrapped_reader)
    }
}

impl<'a> Source<&'a [u8]> {
    /// Reads and returns the exact number of bytes requested.
    ///
    /// If at least `len` bytes are remaining in the reader, returns a slice
    /// of length `len` and progresses the reader by `len` bytes.
    ///
    /// Returns an error if less than `len` bytes are left.
    pub fn read_exact_borrowed(
        &mut self, len: usize
    ) -> Result<&'a [u8], io::Error> {
        let (head, tail) = self.wrapped_reader.split_at_checked(
            len
        ).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::UnexpectedEof, "unexpected end-of data"
            )
        })?;
        self.wrapped_reader = tail;
        self.pos += head.len();
        Ok(head)
    }
}

impl<R: io::Read> io::Read for Source<R> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, io::Error> {
        let read = self.reader()?.read(buf)?;
        self.pos += read;
        Ok(read)
    }
}

impl<R: io::BufRead> io::BufRead for Source<R> {
    fn fill_buf(&mut self) -> Result<&[u8], io::Error> {
        self.reader()?.fill_buf()
    }

    fn consume(&mut self, amt: usize) {
        if let Ok(reader) = self.reader() {
            reader.consume(amt);
            self.pos += amt;
        }
    }
}


//============ Helper Functions ==============================================


//------------ read_u8 -------------------------------------------------------

pub fn read_u8(reader: &mut impl io::Read) -> Result<u8, io::Error> {
    let mut res = [0u8];
    reader.read_exact(&mut res)?;
    Ok(res[0])
}


//============ Error Types ===================================================

//------------ SourceError ---------------------------------------------------

/// An error happened while processing the source.
///
/// This is only used internally when creating an IO error.
#[derive(Debug)]
pub enum SourceError {
    /// Invalidly encoded data was discovered while decoding.
    InvalidData(&'static str),

    /// A bug in an implementation was encountered.
    Bug(&'static str),

    /// An IO error happened.
    ///
    /// This is wrapped into an option because IO errors are not clone and
    /// we can only return it once. Any subsequent uses of the error will be
    /// converted into a placeholder.
    Io(Option<io::Error>),
}

impl SourceError {
    /// Converts the source error into an IO error.
    fn create_io_error(&mut self) -> io::Error {
        match self {
            Self::InvalidData(inner) => {
                io::Error::new(io::ErrorKind::InvalidData, *inner)
            }
            Self::Bug(inner) => {
                io::Error::other(*inner)
            }
            Self::Io(inner) => {
                match inner.take() {
                    Some(err) => err,
                    None => io::Error::other("earlier IO error"),
                }
            }
        }
    }
}

impl From<io::Error> for SourceError {
    fn from(src: io::Error) -> Self {
        Self::Io(Some(src))
    }
}

impl fmt::Display for SourceError {
    fn fmt(&self, _f: &mut fmt::Formatter) -> fmt::Result {
        todo!()
    }
}

impl error::Error for SourceError { }

