//! Bytes String.
//!
//! This is an internal module. It’s public items are re-exported by the
//! parent.

use std::{ops, str};
use std::borrow::Borrow;
use bytes::Bytes;


//------------ BytesString ---------------------------------------------------

/// A string atop a bytes value.
///
/// This types wraps a `Bytes` value that contains a correctly encoded
/// string and provides a `str` interface to it.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BytesString(Bytes);

impl BytesString {
    /// Creates a new bytes string without checking the content.
    pub unsafe fn from_utf8_unchecked(bytes: Bytes) -> Self {
        BytesString(bytes)
    }

    /// Converts a bytes value into a bytes string.
    pub fn from_utf8(bytes: Bytes) -> Result<Self, str::Utf8Error> {
        let _ = str::from_utf8(&bytes)?;
        Ok(unsafe { Self::from_utf8_unchecked(bytes) })
    }

    /// Creates an empty bytes string.
    pub fn empty() -> Self {
        unsafe { Self::from_utf8_unchecked(Bytes::new()) }
    }

    /// Returns a reference to the underlying bytes value.
    pub fn as_bytes(&self) -> &Bytes {
        &self.0
    }

    /// Returns a reference to the string content.
    pub fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(self.as_slice()) }
    }

    /// Returns a reference to the raw byte slice.
    pub fn as_slice(&self) -> &[u8] {
        self.0.as_ref()
    }
}


//--- From

impl From<String> for BytesString {
    fn from(s: String) -> Self {
        unsafe { Self::from_utf8_unchecked(Bytes::from(s.into_bytes())) }
    }
}

impl<'a> From<&'a str> for BytesString {
    fn from(s: &'a str) -> Self {
        unsafe { Self::from_utf8_unchecked(Bytes::from(s.as_bytes())) }
    }
}


//--- Deref, AsRef and Borrow

impl ops::Deref for BytesString {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<Bytes> for BytesString {
    fn as_ref(&self) -> &Bytes {
        self.as_bytes()
    }
}

impl AsRef<str> for BytesString {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<[u8]> for BytesString {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl Borrow<Bytes> for BytesString {
    fn borrow(&self) -> &Bytes {
        self.as_bytes()
    }
}

impl Borrow<str> for BytesString {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl Borrow<[u8]> for BytesString {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

