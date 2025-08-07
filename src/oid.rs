//! ASN.1 Object Identifiers.
//!
//! This module contains the [`Oid`] type that implements object identifiers,
//! a construct used by ANS.1 to uniquely identify all sorts of things. The
//! type is also re-exported at the top-level.

use std::{error, fmt, io, mem};
use std::str::FromStr;
use std::sync::Arc;
use crate::decode;
use crate::decode::{Constructed, Primitive};
use crate::encode::{PrimitiveContent, Target};
use crate::ident::Tag;
use crate::length::Length;
use crate::mode::Mode;


//------------ Oid -----------------------------------------------------------

/// An object identifier.
///
/// Object identifiers are globally unique, hierarchical values that are used
/// to identify objects or their type. When written, they are presented as a
/// sequence of integers separated by dots such as ‘1.3.6.1.5.5.7.1’ or with
/// the integers separated by white space and enclosed in curly braces such
/// as ‘{ 1 3 6 1 5 5 7 1 }’. Individual integers or sequences of integers
/// can also be given names which then are used instead of the integers.
/// 
/// Values of this type keep a single object identifier in its BER encoding
/// as an unsized byte slice. To get an owned version, the type can be wrapped
/// in a `Box<Oid>` or `Arc<Oid>`.
///
/// The only use for object identifiers currently is to compare them to
/// predefined values. For this purpose, you typically define your known
/// object identifiers in a `oid` submodule as constants of
/// `&Oid` by using `Oid::make`. Unfortunately, you need to provide it with
/// a byte slice of the encoded identifier since we can’t do the necessary
/// manipulations in a const function and there currently is no proc macro.
///
/// Instead, the crate ships with a `mkoid` binary which accepts object
/// identifiers in ‘dot integer’ notation and produces the byte slice for
/// their encoded value. You can install this binary via `cargo install ber`.
#[derive(Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct Oid([u8]);

impl Oid {
    /// Creates an object identifier from a byte slice without checking.
    ///
    /// # Safety
    ///
    /// The called must ensure that `slice` contains a correctly encoded
    /// OID.
    pub const unsafe fn from_slice_unchecked(slice: &[u8]) -> &Self {
        unsafe { mem::transmute(slice) }
    }
    ///
    /// Creates a boxed identifier from a boxed slice without checking.
    ///
    /// # Safety
    ///
    /// The called must ensure that `src` contains a correctly encoded
    /// object identifier.
    pub unsafe fn from_box_unchecked(src: Box<[u8]>) -> Box<Self> {
        unsafe { mem::transmute(src) }
    }

    /// Creates an object identifier from a byte slice.
    pub fn from_slice(slice: &[u8]) -> Result<&Self, InvalidOid> {
        Self::check_slice(slice)?;
        Ok(unsafe { Self::from_slice_unchecked(slice) })
    }

    /// Creates a boxed object identifier from a boxed slice.
    pub fn from_box(src: Box<[u8]>) -> Result<Box<Self>, InvalidOid> {
        Self::check_slice(src.as_ref())?;
        Ok(unsafe { Self::from_box_unchecked(src) })
    }

    /// Creates an object identifier from a slice or panics.
    ///
    /// This function is intended to create constants and fail at compile
    /// time if the slice is invalid.
    ///
    /// # Panics
    ///
    /// The function panics if `slice` does not contain a correctly encoded
    /// object identifier.
    pub const fn make(slice: &[u8]) -> &Self {
        if Self::check_slice(slice).is_err() {
            panic!("invalid object identifier")
        }
        unsafe { Self::from_slice_unchecked(slice) }
    }

    /// Checks that the content contains a validly encoded OID.
    ///
    /// # Caveats
    ///
    /// This currently doesn’t check that the sub-identifiers are encoded in
    /// the smallest amount of octets.
    const fn check_slice(mut slice: &[u8]) -> Result<(), InvalidOid> {
        // There always has to be a first sub-identifier, i.e., content
        // must not be empty. We grab the last byte while we are checking for
        // empty.
        let last = match slice.last() {
            Some(last) => *last,
            None => {
                return Err(InvalidOid(()))
            }
        };

        // The last byte must have bit 8 cleared to indicate the end of a
        // subidentifier.
        if last & 0x80 != 0 {
            return Err(InvalidOid(()))
        }

        // The first octet of a subidentifier must not be 0x80. I.e., if
        // there is an 0x80, the octet before that must have bit 8 set.
        // Because of the const fn, we can’t do this the easy way.
        let mut prev = 0; // Pretend we had an end-of-subidentifier before.
        while let Some((&first, tail)) = slice.split_first() {
            if first == 0x80 && prev & 0x80 == 0 {
                return Err(InvalidOid(()))
            }
            prev = first;
            slice = tail;
        }

        Ok(())
    }

    /// Returns a reference to the underlying byte slice.
    pub fn as_slice(&self) -> &[u8] {
        &self.0
    }

    /// Returns an iterator to the components of this object identifiers.
    pub fn iter(&self) -> Iter<'_> {
        Iter::new(self.as_slice())
    }
}

/// # Decoding
impl Oid {
    /// Skips over the next value if it is an object identifier.
    ///
    /// Returns an error if `cons` has reached its end, if the next value
    /// is not a primitive value with `Tag::OID`, or if it does not contain
    /// a correctly encoded object identifer, irregardless of its actual
    /// value.
    pub fn skip_in<M: Mode, R: io::BufRead>(
        cons: &mut Constructed<M, R>
    ) -> Result<(), decode::Error> {
        Self::skip_primitive(cons.next_primitive_with(Tag::OID)?)
    }

    /// Skips over an optional next value if it is an object identifier.
    ///
    /// Returns `Ok(None)` if the `cons` has reached its end.
    ///
    /// Returns an error if the next value is not a primitive value with
    /// `Tag::OID`, or if it does not contain a correctly encoded object
    /// identifer, irregardless of its actual value.
    pub fn skip_opt_in<M: Mode, R: io::BufRead>(
        cons: &mut Constructed<M, R>
    ) -> Result<Option<()>, decode::Error> {
        let Some(prim) = cons.next_opt_primitive_with(Tag::OID)? else {
            return Ok(None)
        };
        Ok(Some(Self::skip_primitive(prim)?))
    }

    /// Decodes the next value as an object identifier.
    ///
    /// Returns an error if `const` has reached its end, if the next value
    /// is not a primitive value with `Tag::OID`, or if it does not contain
    /// a correctly encoded object identifer.
    pub fn take_from<M: Mode, R: io::BufRead>(
        cons: &mut Constructed<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        Self::from_primitive(cons.next_primitive_with(Tag::OID)?)
    }

    /// Decodes the next value as an object identifier, borrowing the content.
    ///
    /// Returns an error if `cons` has reached its end, if the next value
    /// is not a primitive value with `Tag::OID`, or if it does not contain
    /// a correctly encoded object identifer.
    pub fn take_from_borrowed<'s, M: Mode>(
        cons: &mut Constructed<M, &'s [u8]>
    ) -> Result<&'s Self, decode::Error> {
        Self::from_primitive_borrowed(cons.next_primitive_with(Tag::OID)?)
    }

    /// Decodes an optional next value if it is an object identifier.
    ///
    /// Returns `Ok(None)` if `const` has reached its end.
    ///
    /// Returns an error if the next value is not a primitive value with
    /// `Tag::OID`, or if it does not contain a correctly encoded object
    /// identifer.
    pub fn take_opt_from<M: Mode, R: io::BufRead>(
        cons: &mut Constructed<M, R>
    ) -> Result<Option<Box<Self>>, decode::Error> {
        let Some(prim) = cons.next_opt_primitive_with(Tag::OID)? else {
            return Ok(None)
        };
        Ok(Some(Self::from_primitive(prim)?))
    }

    /// Decodes an optional next value as object identifier, borrowing content.
    ///
    /// Returns `Ok(None)` if `const` has reached its end.
    ///
    /// Returns an error if the next value is not a primitive value with
    /// `Tag::OID`, or if it does not contain a correctly encoded object
    /// identifer.
    pub fn take_opt_from_borrowed<'s, M: Mode>(
        cons: &mut Constructed<M, &'s [u8]>
    ) -> Result<Option<&'s Self>, decode::Error> {
        let Some(prim) = cons.next_opt_primitive_with(Tag::OID)? else {
            return Ok(None)
        };
        Ok(Some(Self::from_primitive_borrowed(prim)?))
    }

    /// Skips over the next value if it is equal to `self`.
    ///
    /// Returns an error if `cons` has reached its end, if the next value
    /// is not a primitive value with `Tag::OID`, or if it does not contain
    /// a correctly encoded object identifer, or if the object identifier is
    /// not equal to `self`.
    pub fn skip_if<M: Mode, R: io::BufRead>(
        &self, cons: &mut Constructed<M, R>
    ) -> Result<(), decode::Error> {
        self.expect_primitive(cons.next_primitive_with(Tag::OID)?)
    }


    /// Skips over an optional next value if it is equal to `self`.
    ///
    /// Returns `Ok(None)` if `cons` has reached its end.
    ///
    /// Returns an error if the next value is not a primitive value with
    /// `Tag::OID`, or if it does not contain a correctly encoded object
    /// identifer, or if the object identifier is not equal to `self`.
    pub fn skip_opt_if<M: Mode, R: io::BufRead>(
        &self, cons: &mut Constructed<M, R>
    ) -> Result<Option<()>, decode::Error> {
        let Some(prim) = cons.next_opt_primitive_with(Tag::OID)? else {
            return Ok(None)
        };
        Ok(Some(self.expect_primitive(prim)?))
    }

    /// Constructs an object identifier from the content of a primitive value.
    pub fn from_primitive<M, R: io::BufRead>(
        mut prim: Primitive<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        Self::from_box(prim.read_all_into_box()?).map_err(|err| {
            prim.err_at_start(err)
        })
    }

    /// Constructs an object identifier from the content of a primitive value.
    pub fn from_primitive_borrowed<'s, M>(
        mut prim: Primitive<M, &'s [u8]>
    ) -> Result<&'s Self, decode::Error> {
        Self::from_slice(prim.read_all_borrowed()?).map_err(|err| {
            prim.err_at_start(err)
        })
    }

    /// Skips over an object identifier contained in a primitive value.
    ///
    /// Skips the content as long as it is a correctly encoded object
    /// identifier, no matter what identifier it actually is.
    pub fn skip_primitive<M, R: io::BufRead>(
        mut prim: Primitive<M, R>
    ) -> Result<(), decode::Error> {
        let start = prim.start();
        // Can’t be empty.
        if prim.remaining().is_zero() {
            return Err(decode::Error::content(InvalidOid(()), start))
        }
        let mut prev = 0;
        loop {
            let mut buf = prim.fill_buf()?;
            if buf.is_empty() {
                // We have reached the end. Check that the last octet has
                // bit 8 cleared.
                if prev & 0x80 == 0 {
                    return Ok(())
                }
                else {
                    return Err(decode::Error::content(InvalidOid(()), start))
                }
            }

            let len = buf.len();

            // 0x80 can’t follow an octet with bit 8 unset.
            while let Some((&first, tail)) = buf.split_first() {
                if first == 0x80 && prev & 0x80 == 0 {
                    return Err(decode::Error::content(
                        InvalidOid(()), start
                    ))
                }
                prev = first;
                buf = tail;
            }

            prim.consume(len);
        }
    }

    /// Skips over an idenifier in a primitive if it is equal.
    ///
    /// If the primitive contains a different identifier, returns an error.
    pub fn expect_primitive<M, R: io::BufRead>(
        &self,
        mut prim: Primitive<M, R>
    ) -> Result<(), decode::Error> {
        // We don’t check for a valid OID here but just compare it to our
        // own slice.
        let start = prim.start();
        let mut slice = self.as_slice();
        while !slice.is_empty() {
            let buf = prim.fill_buf()?;
            if buf.is_empty() {
                return Err(decode::Error::content(
                    "unexpected object identifier", start
                ))
            }
            match slice.strip_prefix(buf) {
                Some(tail) => {
                    if tail.is_empty() {
                        break
                    }
                    else {
                        slice = tail;
                    }
                }
                None => {
                    return Err(decode::Error::content(
                        "unexpected object identifier", start
                    ))
                }
            }
        }
        if !prim.remaining().is_zero() {
            Err(decode::Error::content("unexpected object identifier", start))
        }
        else {
            Ok(())
        }
    }
}


//--- FromStr

impl FromStr for Box<Oid> {
    type Err = ParseOidError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn from_str(s: &str) -> Result<u32, ParseOidError> {
            u32::from_str(s).map_err(|_| {
                ParseOidError("only integer components allowed")
            })
        }

        let mut components = s.split('.');
        let (first, second) = match (components.next(), components.next()) {
            (Some(first), Some(second)) => (first, second),
            _ => {
                return Err(ParseOidError(
                    "at least two components required"
                ));
            }
        };

        let first = from_str(first)?;
        if first > 2 {
            return Err(ParseOidError(
                "first component can only be 0, 1, or 2."
            ))
        }

        let second = from_str(second)?;
        if first < 2 && second >= 40 {
            return Err(ParseOidError(
                "second component for 0. and 1. must be less than 40"
            ));
        }

        let mut res = vec![40 * first + second];
        for item in components {
            res.push(from_str(item)?);
        }

        let mut bytes = vec![];
        for item in res {
            // 1111 1111  1111 1111  1111 1111  1111 1111
            // EEEE DDDD  DDDC CCCC  CCBB BBBB  BAAA AAAA
            if item > 0x0FFF_FFFF {
                bytes.push(((item >> 28) | 0x80) as u8);
            }
            if item > 0x001F_FFFF {
                bytes.push((((item >> 21) & 0x7F) | 0x80) as u8);
            }
            if item > 0x0000_3FFF {
                bytes.push((((item >> 14) & 0x7F) | 0x80) as u8)
            }
            if item > 0x0000_007F {
                bytes.push((((item >> 7) & 0x7F) | 0x80) as u8);
            }
            bytes.push((item & 0x7F) as u8);
        }

        Ok(unsafe { Oid::from_box_unchecked(bytes.into()) })
    }
}


//--- AsRef

impl AsRef<Oid> for Oid {
    fn as_ref(&self) -> &Oid {
        self
    }
}

impl AsRef<[u8]> for Oid {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}


//--- PartialEq

impl<'a> PartialEq<&'a Oid> for Box<Oid> {
    fn eq(&self, other: &&'a Oid) -> bool {
        self.as_ref().eq(other)
    }
}


//--- PrimitiveContent

impl<M> PrimitiveContent<M> for &'_ Oid {
    const TAG: Tag = Tag::OID;

    fn encoded_len(self) -> Length {
        self.as_slice().len().into()
    }

    fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(self.as_slice())
    }
}

impl<M> PrimitiveContent<M> for &'_ Box<Oid> {
    const TAG: Tag = Tag::OID;

    fn encoded_len(self) -> Length {
        self.as_slice().len().into()
    }

    fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(self.as_slice())
    }
}

impl<M> PrimitiveContent<M> for &'_ Arc<Oid> {
    const TAG: Tag = Tag::OID;

    fn encoded_len(self) -> Length {
        self.as_slice().len().into()
    }

    fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(self.as_slice())
    }
}


//--- Display and Debug

impl fmt::Display for Oid {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut components = self.iter();
        match components.next() {
            Some(component) => component.fmt(f)?,
            None => { return Ok(()) }
        }
        components.try_for_each(|item| write!(f, ".{item}"))
    }
}

impl fmt::Debug for Oid {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("Oid(")?;
        let mut components = self.iter();
        match components.next() {
            Some(component) => component.fmt_debug(f)?,
            None => return f.write_str(")"),
        }
        components.try_for_each(|item| write!(f, ".{item}"))?;
        f.write_str(")")
    }
}


//------------ Component -----------------------------------------------------

/// A component of an object identifier.
///
/// Although these components are integers, they are encoded in a slightly
/// inconvenient way. Because of this we don’t convert them to native integers
/// but rather keep them as references to the underlying octets.
///
/// This type allows comparison and formatting, which hopefully is all you’ll
/// need. If you insist, the method `to_u32` allows you to try to convert a
/// component to a native integer.
#[derive(Clone, Copy)]
pub struct Component<'a> {
    /// The position of the component in the object identifier.
    position: Position,

    /// The octets of the subidentifier.
    ///
    /// These octets translate to an integer value. The most significant bit
    /// of each octet indicates whether there are more octets to follow (and
    /// can thus be ignored in this context), the lower seven bits are then
    /// shifted accordingly to make up an unsigned integer in big endian
    /// notation. Since this isn’t bounded in any way, we can’t just simply
    /// turn these into, say, `u32`s although, realistically, it is unlikely
    /// there is anything bigger than that.
    slice: &'a [u8],
}

/// The position of the component in the object identifier.
///
/// As the first two components of the object identifier are encoded in the
/// first subidentifier of the encoded value, we have three different cases.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Position {
    /// This is the first component of the identifier.
    ///
    /// This is 0 if the integer value of the subidentifier is 0..39,
    /// 1 for 40..79, and 2 for anything else.
    First,

    /// This is the second component of the identifier.
    ///
    /// This is the integer value of the subidentifier module 40 if the value
    /// is below 80 and otherwise the value minus 80.
    Second,

    /// This is any later component of the identifier.
    ///
    /// This is identical to the integer value of the subidentifier.
    Other,
}

impl<'a> Component<'a> {
    /// Creates a new component.
    fn new(position: Position, slice: &'a [u8]) -> Self {
        Component { position, slice }
    }

    /// Attempts to convert the component to `u32`.
    ///
    /// Since the component’s value can be larger than the maximum value of
    /// a `u32`, this may fail in which case the method will return `None`.
    pub fn to_u32(self) -> Option<u32> {
        // This can be at most five octets with at most four bits in the
        // topmost octet.
        //
        // Safety: self.slice is definitely not empty when indexing.
        #[allow(clippy::indexing_slicing)]
        if self.slice.len() > 5
            || (self.slice.len() == 4 && self.slice[0] & 0x70 != 0)
        {
            return None
        }
        let mut res = 0;
        for &ch in self.slice {
            res = (res << 7) | u32::from(ch & 0x7F);
        }
        match self.position {
            Position::First => {
                if res < 40 {
                    Some(0)
                }
                else if res < 80{
                    Some(1)
                }
                else {
                    Some(2)
                }
            }
            Position::Second => {
                if res < 80 {
                    Some(res % 40)
                }
                else {
                    Some(res - 80)
                }
            }
            Position::Other => Some(res)
        }
    }

    /// Formats the component for use in `Oid`’s `Debug` impl.
    fn fmt_debug(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.to_u32() {
            Some(val) => write!(f, "{val}"),
            None => write!(f, "{:?}", self.slice),
        }
    }
}


//--- PartialEq and Eq

impl PartialEq for Component<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.position == other.position && self.slice == other.slice
    }
}

impl Eq for Component<'_> { }


//--- Display

impl fmt::Display for Component<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // XXX This can’t deal correctly with overly large components.
        //     Since this is a really rare (if not non-existant) case,
        //     I can’t be bothered to figure out how to convert a seven
        //     bit integer into decimal.
        match self.to_u32() {
            Some(val) => val.fmt(f),
            None => f.write_str("(very large component)"),
        }
    }
}


//------------ Iter ----------------------------------------------------------

/// An iterator over the sub-identifiers in an object identifier.
pub struct Iter<'a> {
    /// The remainder of the object identifier’s encoded octets.
    slice: &'a [u8],

    /// The position of the next component.
    position: Position,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    fn new(slice: &'a [u8]) -> Self {
        Iter {
            slice,
            position: Position::First
        }
    }

    fn advance_position(&mut self) -> Position {
        let res = self.position;
        self.position = match res {
            Position::First => Position::Second,
            _ => Position::Other
        };
        res
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = Component<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.slice.is_empty() {
            return None
        }
        for i in 0..self.slice.len() {
            // Safety: i is always a valid index.
            #[allow(clippy::indexing_slicing)]
            if self.slice[i] & 0x80 == 0 {
                let (res, tail) = self.slice.split_at(i + 1);
                if self.position != Position::First {
                    self.slice = tail;
                }
                return Some(Component::new(self.advance_position(), res));
            }
        }
        // If we arrive here, the last component didn’t end with the last
        // octet having the most-significant bit cleared. Since we only allow
        // `Oid` to contain a correctly encoded value, this can’t happen. So,
        // we are having undefined behaviour here and can do whatever we want.
        // Which is:
        None
    }
}


//============ ErrorTyps =====================================================

//------------ InvalidOid ----------------------------------------------------

/// A byte slice contained an invalidly encoded OID.
#[derive(Clone, Debug)]
pub struct InvalidOid(());

impl fmt::Display for InvalidOid {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("invalid OID")
    }
}

impl error::Error for InvalidOid { }


//------------ ParseOidError -------------------------------------------------

/// A string couldn’t be parsed as an object identifier.
#[derive(Clone, Debug)]
pub struct ParseOidError(&'static str);

impl fmt::Display for ParseOidError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.0)
    }
}

impl error::Error for ParseOidError { }


//============ Tests ========================================================

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn display() {
        assert_eq!(
            "2.5.29.19",
            format!("{}", Oid::from_slice(&[85, 29, 19]).unwrap()).as_str()
        );
    }

    #[test]
    fn take_and_skip_primitive() {
        fn check(slice: &[u8], is_ok: bool) {
            let take = Primitive::decode_slice_ber(
                slice, |prim| Oid::from_primitive(prim)
            );
            assert_eq!(take.is_ok(), is_ok);
            if let Ok(oid) = take {
                assert_eq!(oid.0.as_ref(), slice);
            }
            let res = Primitive::decode_slice_ber(
                slice, |prim| Oid::skip_primitive(prim)
            );
            if is_ok {
                res.unwrap()
            }
            else {
                assert!(res.is_err())
            }
        }

        check(b"", false);
        check(b"\x81\x34", true);
        check(b"\x81\x34\x03", true);
        check(b"\x81\x34\x83\x03", true);
        check(b"\x81\x34\x83\x83\x03\x03", true);
        check(b"\x81\x34\x83", false);
    }
}


