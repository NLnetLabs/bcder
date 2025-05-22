//! Targets for encoding.
//!
//! This is a private module. The relevant items are re-exported by the
//! parent.

use std::{error, io};
use std::convert::Infallible;


//------------ Target --------------------------------------------------------

/// A target for encoding.
///
/// This type provides a simplified version of `io::Write` that allows an
/// implementing type to define its own error type. The main purpose is to
/// be able to set the error to `Infallible`. This allows users to erase
/// the error case and avoid unnecessary `unwrap`s.
pub trait Target {
    /// The error type of the target.
    type Error: error::Error;

    /// Writes the data to the target.
    fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error>;
}

impl<T: Target> Target for &mut T {
    type Error = T::Error;

    fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        (*self).write_all(data)
    }
}

impl Target for Vec<u8> {
    type Error = Infallible;

    fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        self.extend_from_slice(data);
        Ok(())
    }
}


//------------ IoTarget ------------------------------------------------------

/// A wrapper around a `io::Write` type providing it as a target.
pub struct IoTarget<W>(W);

impl<W> IoTarget<W> {
    /// Creates a new target from an IO writer.
    pub fn new(writer: W) -> Self {
        Self(writer)
    }

    /// Converts the target back into its underlying writer.
    pub fn into_writer(self) -> W {
        self.0
    }
}

impl<W> From<W> for IoTarget<W> {
    fn from(src: W) -> Self {
        Self::new(src)
    }
}

impl<W: io::Write> Target for IoTarget<W> {
    type Error = io::Error;

    fn write_all(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        self.0.write_all(data)
    }
}

impl<W: io::Write> io::Write for IoTarget<W> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, io::Error> {
        self.0.write(buf)
    }

    fn flush(&mut self) -> Result<(), io::Error> {
        self.0.flush()
    }
}


//------------ IoTarget ------------------------------------------------------

/// Erases an error if it can’t happen.
pub fn infallible<T, E: Into<Infallible>>(res: Result<T, E>) -> T {
    match res {
        Ok(some) => some,
        Err(_) => unreachable!(),
    }
}

