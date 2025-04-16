//! The length octets.
//!
//! This is a private module. The [`Length`] definied herein is not
//! publicly exposed.

#![allow(dead_code)] // XXX REMOVE!!!

use std::io;
use std::marker::PhantomData;
use crate::mode::Mode;
use crate::decode::{DecodeError, Fragment, Source};



//------------ Length -------------------------------------------------------

/// The length octets of an encoded value.
///
/// A length value can either be definite, meaning it provides the actual
/// number of content octets in the value, or indefinite, in which case the
/// content is delimited by a special end-of-value marker.
///
/// # BER Encoding
///
/// The length can be encoded in one of two basic ways. Which one is used is
/// determined by the most significant bit of the first octet. If it is not
/// set, the length octets is one octet long and the remaining bits of this
/// first octet provide the definite length. Thus, if the first octet is
/// less than 128, it provides the definite length already.
///
/// If the most significant bit is set, the remaining bits of the first
/// octet specify the number of octets that follow to encode the actual
/// length. If they specify that there are zero more octets, i.e., the
/// value of the first octet is 128, the length is indefinite. Otherwise,
/// those following octets give the big-endian encoding of the definite
/// length of the content octets.
///
/// Under both CER and DER rules, a definite length must be encoded in the
/// minimum number of octets. Because of this, the type is generic over
/// the mode.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Length<M> {
    /// The length.
    ///
    /// If this is `None`, the length is indefinite. Otherwise it is definite
    /// with the given value.
    length: Option<Definite>,

    /// A marker for the mode.
    marker: PhantomData<M>,
}

impl<M> Length<M> {
    /// Creates a new length from the given optional length.
    ///
    /// If the length is `None`, creates an indefinite length value.
    fn new(length: Option<usize>) -> Self {
        Self { length: length.map(Definite), marker: PhantomData }
    }

    /// Returns the length if it is definite.
    pub fn definite(self) -> Option<usize> {
        self.length.map(|x| x.0)
    }

    /// Returns whether the length is definite and zero.
    pub fn is_zero(self) -> bool {
        self.definite() == Some(0)
    }

    /// Parses a length from a source in BER mode.
    pub fn take_from<S: Source>(
        source: &mut S
    ) -> Result<Self, DecodeError<S::Error>>
    where M: Mode {
        // This branch should be optimized away after monomorphisation.
        if M::IS_RESTRICTED {
            Self::take_from_restricted(source)
        }
        else {
            Self::take_from_relaxed(source)
        }
    }

    /// Parses a length from a source in BER mode.
    fn take_from_relaxed<S: Source>(
        source: &mut S
    ) -> Result<Self, DecodeError<S::Error>> {
        // Determine the length of the whole thing (which is one more than
        // what’s returned for multi).
        // Return early for trivial cases, don’t forget to consume the first
        // octet in this case.
        let len = match FirstOctet::peek(source)? {
            FirstOctet::Single(res) => {
                source.take_u8()?;
                return Ok(res)
            }
            FirstOctet::Multi(len) => len + 1,
        };

        // Find the first non-zero octet. This will be the index of the start
        // of our source slice.
        let start = (1..len).into_iter().find_map(|i| {
            match source.peek_nth(i) {
                Ok(value) if value != 0 => Some(Ok(i)),
                Ok(_) => None,
                Err(err) => Some(Err(err))
            }
        }).transpose()?;

        // If we have only zeros, the result is zero. We need to consume all
        // the zeros, though.
        let Some(start) = start else {
            source.request_exact(len)?.consume();
            return Ok(Self::new(Some(0)))
        };

        // Get the source slice.
        let pos = source.pos();
        let frag = source.request_exact(len)?;
        let Some(from) = frag.slice().get(start..) else {
            // This shouldn’t happen ...
            return Err(DecodeError::content("unexpected end of data", pos))
        };

        // Get the target slice.
        let mut res = 0usize.to_ne_bytes();
        let start = res.len().saturating_add(
            start
        ).saturating_sub(len);
        let Some(to) = res.as_mut_slice().get_mut(start..) else {
            // This means the length is too big for a usize.
            return Err(DecodeError::content("excessive length", pos))
        };

        // Now copy.
        debug_assert_eq!(from.len(), to.len());
        to.copy_from_slice(from);

        frag.consume();

        return Ok(Self::new(Some(usize::from_be_bytes(res))))
    }

    /// Parses a length from a source in CER/DER mode.
    fn take_from_restricted<S: Source>(
        source: &mut S
    ) -> Result<Self, DecodeError<S::Error>> {
        // The difference to the BER case is the second octet can’t be zero
        // and it can’t be less that 0x80 if it is the last octet as well.
        // In both cases, there is a shorter encoding.

        // Determine the length of the whole thing (which is one more than
        // what’s returned for multi).
        // Return early for trivial cases, don’t forget to consume the first
        // octet in this case.
        let len = match FirstOctet::peek(source)? {
            FirstOctet::Single(res) => {
                source.take_u8()?;
                return Ok(res)
            }
            FirstOctet::Multi(len) => len + 1,
        };

        // Now look at the second octet (i.e., index 1) to check for the
        // errors mentioned above.
        let second = source.peek_nth(1)?;
        if second == 0 || (second < 0x80 && len == 2) {
            return Err(source.content_err("illegal length in CER/DER"))
        }

        // Get the source slice.
        let pos = source.pos();
        let frag = source.request_exact(len)?;
        let Some(from) = frag.slice().get(1..) else {
            // This shouldn’t happen ...
            return Err(DecodeError::content("unexpected end of data", pos))
        };

        // Get the target slice.
        let mut res = 0usize.to_ne_bytes();
        let start = res.len().saturating_sub(len).saturating_add(1);
        let Some(to) = res.as_mut_slice().get_mut(start..) else {
            // This means the length is too big for a usize.
            return Err(DecodeError::content("excessive length", pos))
        };

        // Now copy.
        debug_assert_eq!(from.len(), to.len());
        to.copy_from_slice(from);

        frag.consume();

        return Ok(Self::new(Some(usize::from_be_bytes(res))))
    }

    /// Returns the length of the encoded representation of the value.
    pub fn encoded_len(self) -> usize {
        match self.length {
            Some(definite) => definite.encoded_len(),
            None => 1,
        }
    }

    /// Appends the encoded length to the end of `target`.
    pub fn append_encoded(self, target: &mut Vec<u8>) {
        match self.length {
            Some(definite) => definite.append_encoded(target),
            None => target.push(0x80),
        }
    }

    /// Writes the encoded length to the given writer.
    pub fn write_encoded<W: io::Write>(
        self, target: &mut W
    ) -> Result<(), io::Error> {
        match self.length {
            Some(definite) => definite.write_encoded(target),
            None => target.write_all(&[0x80]),
        }
    }
}


//------------ FirstOctet ---------------------------------------------------

/// The first octet of the encoded length.
enum FirstOctet<M> {
    /// The first octet is a length in and of itself.
    Single(Length<M>),

    /// The first octet indicates the number of octets to follow.
    Multi(usize),
}

impl<M> FirstOctet<M> {
    /// Look at the first octet and check what it means.
    fn peek<S: Source>(
        source: &mut S
    ) -> Result<Self, DecodeError<S::Error>> {
        match source.peek_nth(0)? {
            // Bit 7 clear: single.
            n if (n & 0x80) == 0 => {
                Ok(Self::Single(Length::new(Some(n as usize))))
            }

            // 0x80: indefinite.
            0x80 => Ok(Self::Single(Length::new(None))),

            // 0xFF: illegal.
            0xFF => return Err(source.content_err("illegal length octets")),

            // anything else: clear left bit, number of octets.
            n => Ok(Self::Multi((n & 0x7F) as usize))
        }
    }
}


//------------ Definite ------------------------------------------------------

/// A definite length.
///
/// This is a newtype of `usize` which allows us to do all the encoding
/// things on it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
struct Definite(usize);

impl Definite {
    const LEN: usize = 0usize.to_ne_bytes().len();

    fn encoded_len(self) -> usize {
        if self.0 > 0x7F {
            let idx = self.encoded_start_idx();
            debug_assert!(idx < Self::LEN);

            Self::LEN - idx + 1
        }
        else {
            1
        }
    }

    fn append_encoded(self, target: &mut Vec<u8>) {
        if self.0 > 0x7F {
            let idx = self.encoded_start_idx();
            debug_assert!(idx < Self::LEN);

            // LEN will never be greater than 126 bytes. Also, `idx` won’t be
            // greater than LEN, so the subtraction here is fine.
            target.push(((Self::LEN - idx) | 0x80) as u8);

            // Panic: idx can’t be bigger than LEN, so this can’t panic.
            #[allow(clippy::slicing_indexing)]
            target.extend_from_slice(
                &self.0.to_be_bytes()[idx..]
            )
        }
        else {
            target.push(self.0 as u8)
        }
    }

    fn write_encoded<W: io::Write>(
        self, target: &mut W
    ) -> Result<(), io::Error> {
        if self.0 > 0x7F {
            let idx = self.encoded_start_idx();
            debug_assert!(idx < Self::LEN);

            // LEN will never be greater than 126 bytes. Also, `idx` won’t be
            // greater than LEN, so the subtraction here is fine.
            target.write_all(&[((Self::LEN - idx) | 0x80) as u8])?;

            // Panic: idx can’t be bigger than LEN, so this can’t panic.
            #[allow(clippy::slicing_indexing)]
            target.write_all(
                &self.0.to_be_bytes()[idx..]
            )
        }
        else {
            target.write_all(&[self.0 as u8])
        }
    }

    /// Returns the index of the first non-zero octet of `len`.
    fn encoded_start_idx(self) -> usize {
        (self.0.leading_zeros().next_multiple_of(8) / 8) as usize
    }
}



//============ Tests =========================================================

#[cfg(test)]
mod test {
    use crate::decode::{ContentError, SliceSource};
    use crate::mode::{Ber, Der};
    use super::*;

    #[test]
    fn ber_take_from() {
        fn take_from<const N: usize>(
            src: &[u8; N]
        ) -> Result<Option<usize>, ContentError> {
            let mut src = SliceSource::new(src.as_ref());
            let res = Length::<Ber>::take_from(&mut src)?;
            if src.remaining().is_empty() {
                Ok(res.definite())
            }
            else {
                Err(ContentError::from_static("TRAILING DATA"))
            }
        }

        assert_eq!(take_from(b"\x00").unwrap(), Some(0x00));
        assert_eq!(take_from(b"\x12").unwrap(), Some(0x12));
        assert_eq!(take_from(b"\x7f").unwrap(), Some(0x7f));
        assert_eq!(take_from(b"\x80").unwrap(), None);
        assert_eq!(take_from(b"\x81\x00").unwrap(), Some(0));
        assert_eq!(take_from(b"\x81\xF0").unwrap(), Some(0xF0));
        assert_eq!(take_from(b"\x82\x00\x00").unwrap(), Some(0));
        assert_eq!(take_from(b"\x82\xF0\x0E").unwrap(), Some(0xF00E));
        assert_eq!(take_from(b"\x82\x00\x0E").unwrap(), Some(0x0E));
        assert!(take_from(b"\xFF").is_err());
    }

    #[test]
    fn der_take_from() {
        fn take_from<const N: usize>(
            src: &[u8; N]
        ) -> Result<Option<usize>, ContentError> {
            let mut src = SliceSource::new(src.as_ref());
            let res = Length::<Der>::take_from(&mut src)?;
            if src.remaining().is_empty() {
                Ok(res.definite())
            }
            else {
                Err(ContentError::from_static("TRAILING DATA"))
            }
        }

        assert_eq!(take_from(b"\x00").unwrap(), Some(0x00));
        assert_eq!(take_from(b"\x12").unwrap(), Some(0x12));
        assert_eq!(take_from(b"\x7f").unwrap(), Some(0x7f));
        assert_eq!(take_from(b"\x80").unwrap(), None);
        assert!(take_from(b"\x81\x00").is_err());
        assert!(take_from(b"\x81\x7f").is_err());
        assert_eq!(take_from(b"\x81\x80").unwrap(), Some(0x80));
        assert_eq!(take_from(b"\x81\xF0").unwrap(), Some(0xF0));
        assert!(take_from(b"\x82\x00\x00").is_err());
        assert_eq!(take_from(b"\x82\xF0\x0E").unwrap(), Some(0xF00E));
        assert!(take_from(b"\x82\x00\x0E").is_err());
        assert!(take_from(b"\xFF").is_err());
    }

    #[test]
    fn encode() {
        fn step<const N: usize>(l: Option<usize>, res: &[u8; N]) {
            let l = Length::<Ber>::new(l);
            let mut vec = Vec::new();
            l.append_encoded(&mut vec);
            assert_eq!(
                vec.as_slice(), res.as_ref(),
                "append failed for {l:?}: {vec:?}"
            );

            let mut vec = Vec::new();
            l.write_encoded(&mut vec).unwrap();
            assert_eq!(
                vec.as_slice(), res.as_ref(),
                "write failed for {l:?}: {vec:?}"
            );
        }

        step(None, b"\x80");
        step(Some(0), b"\x00");
        step(Some(0x12), b"\x12");
        step(Some(0x7f), b"\x7f");
        step(Some(0x80), b"\x81\x80");
        step(Some(0xdead), b"\x82\xde\xad");
    }
}

