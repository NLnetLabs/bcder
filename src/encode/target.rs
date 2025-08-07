//! Targets for encoding.
//!
//! This is a private module. The relevant items are re-exported by the
//! parent.

use std::{error, io};
use std::convert::Infallible;
use crate::ident::Tag;
use crate::length::Length;
use super::values::{total_len, write_header};


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


//------------ SplitTarget ---------------------------------------------------

/// A target wrapper that writes data split into equal length primitives.
///
/// The type takes some other target and writes data broken up into blocks of
/// a given size, except for the last segment which can be shorter. The
/// blocks are written as primitive values using a provided tag.
///
/// In order to know when the last segement is reached, the type needs to
/// know the overall length of the data. Because the type can’t produce its
/// own errors due to the structure of the [`Target`] trait, it will have to
/// quietly ignore any data written past this length. It will, however, panic
/// in debug mode.
///
/// Note that the type does only write a sequence of primitive values. You
/// will have to write the header and possibly end-of-value for the outer
/// constructed value yourself.
pub struct SplitTarget<'a, T> {
    /// The overall length of the data to be written.
    ///
    /// This is provided when creating a value of this type.
    len: Length,

    /// The length of the content of the segments.
    step: Length,

    /// The tag of the segments.
    tag: Tag,

    /// The target to write the data to.
    target: &'a mut T,

    /// The amount of content we have already written.
    written: Length,
}

impl<'a, T> SplitTarget<'a, T> {
    /// Creates a new split target.
    ///
    /// The returned target will wrap the provided `target`. It will never
    /// write more than `len` bytes of data. The data will be broken up
    /// into a sequence of primitive values using the given tag. Each value
    /// will contain `step` bytes except for the last one.
    pub fn new(
        len: Length, step: Length, tag: Tag, target: &'a mut T
    ) -> Self {
        Self {
            len, step, tag, target,
            written: Length::from_usize(0),
        }
    }
}

impl SplitTarget<'static, ()> {
    /// Returns the overall length of a split target.
    ///
    /// The function returns the overall encoded length of the sequence of
    /// primitive values resulting from spliting data of `len` bytes into
    /// segments of `step` bytes each.
    ///
    /// The returned value only includes the sequence of primitive values
    /// itself. It does not consider the additional length from the outer
    /// value.
    pub fn encoded_len(len: Length, step: Length, tag: Tag) -> Length {
        // The length of the full-size values.
        let full_len = (len / step) * total_len(tag, step);

        // The length of the final segment. We only need to consider it if it
        // isn’t zero.
        let tail_len = len % step;

        if tail_len != 0 {
            full_len + total_len(tag, tail_len)
        }
        else {
            full_len
        }
    }
}

impl<T: Target> Target for SplitTarget<'_, T> {
    type Error = T::Error;

    fn write_all(&mut self, mut data: &[u8]) -> Result<(), T::Error> {
        if self.written + data.len() > self.len {
            debug_assert!(false, "attempted to write past end of SplitTarget");
            return Ok(())
        }
        while !data.is_empty() {
            if self.written % self.step == 0 {
                write_header(
                    self.target, self.tag, false,
                    (self.len - self.written) % self.step
                )?;
            }
            let step = (
                self.step - self.written % self.step
            ).to_usize_saturating();
            if let Some((head, tail)) = data.split_at_checked(step) {
                self.target.write_all(head)?;
                self.written += head.len();
                data = tail;
            }
            else {
                self.target.write_all(data)?;
                self.written += data.len();
                data = b"";
            }
        }
        Ok(())
    }
}


//------------ infallible ----------------------------------------------------

/// Erases an error if it can’t happen.
pub fn infallible<T, E: Into<Infallible>>(res: Result<T, E>) -> T {
    match res {
        Ok(some) => some,
        Err(_) => unreachable!(),
    }
}

