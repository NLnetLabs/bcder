//! ASN.1 Object Identifiers.
//!
//! This module contains the [`Oid`] type that implements object identifiers,
//! a construct used by ANS.1 to uniquely identify all sorts of things. The
//! type is also re-exported at the top-level.
//!
//! [`Oid`]: struct.Oid.html

use std::{fmt, hash, io, str::FromStr};
use bytes::Bytes;
use crate::encode;
use crate::decode::{Constructed, DecodeError, Primitive, Source};
use crate::mode::Mode;
use crate::tag::Tag;


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
/// Values of this type keep a single object identifier in its BER encoding,
/// i.e., in some form of byte sequence. Because different representations
/// may be useful, the type is actually generic over something that can
/// become a reference to a bytes slice. Parsing is only defined for `Bytes`
/// values, though.
///
/// The only use for object identifiers currently is to compare them to
/// predefined values. For this purpose, you typically define your known
/// object identifiers in a `oid` submodule as constants of
/// `Oid<&'static [u8]>` – or its type alias `ConstOid`. This is also the
/// reason why the wrapped value is `pub` for now. This will change once
/// `const fn` is stable.
///
/// Unfortunately, there is currently no proc macro to generate the object
/// identifier constants in the code. Instead, the crate ships with a
/// `mkoid` binary which accepts object identifiers in ‘dot integer’ notation
/// and produces the `u8` array for their encoded value. You can install
/// this binary via `cargo install ber`.
#[derive(Clone, Debug)]
pub struct Oid<T: AsRef<[u8]> = Bytes>(pub T);

/// A type alias for `Oid<&'static [u8]>.
///
/// This is useful when defining object identifier constants.
pub type ConstOid = Oid<&'static [u8]>;


/// # Decoding and Encoding
///
impl Oid<Bytes> {
    /// Skips over an object identifier value.
    ///
    /// If the source has reached its end, if the next value does not have
    /// the `Tag::OID`, or if it is not a primitive value containing a
    /// correctly encoded OID, returns a malformed error.
    pub fn skip_in<S: Source>(
        cons: &mut Constructed<S>
    ) -> Result<(), DecodeError<S::Error>> {
        cons.take_primitive_if(Tag::OID, Self::skip_primitive)
    }

    /// Skips over an optional object identifier value.
    ///
    /// If the source has reached its end of if the next value does not have
    /// the `Tag::OID`, returns `Ok(None)`. If the next value has the right
    /// tag but is not a primitive value containing a correctly encoded OID,
    /// returns a malformed error.
    pub fn skip_opt_in<S: Source>(
        cons: &mut Constructed<S>
    ) -> Result<Option<()>, DecodeError<S::Error>> {
        cons.take_opt_primitive_if(Tag::OID, Self::skip_primitive)
    }

    /// Takes an object identifier value from the source.
    ///
    /// If the source has reached its end, if the next value does not have
    /// the `Tag::OID`, or if it is not a primitive value, returns a malformed
    /// error.
    pub fn take_from<S: Source>(
        constructed: &mut Constructed<S>
    ) -> Result<Self, DecodeError<S::Error>> {
        constructed.take_primitive_if(Tag::OID, Self::from_primitive)
    }

    /// Takes an optional object identifier value from the source.
    ///
    /// If the source has reached its end of if the next value does not have
    /// the `Tag::OID`, returns `Ok(None)`. If the next value has the right
    /// tag but is not a primitive value, returns a malformed error.
    pub fn take_opt_from<S: Source>(
        constructed: &mut Constructed<S>
    ) -> Result<Option<Self>, DecodeError<S::Error>> {
        constructed.take_opt_primitive_if(Tag::OID, Self::from_primitive)
    }

    /// Skips an object identifier in the content of a primitive value.
    pub fn skip_primitive<S: Source>(
        prim: &mut Primitive<S>
    ) -> Result<(), DecodeError<S::Error>> {
        prim.with_slice_all(Self::check_content)
    }

    /// Constructs an object identifier from the content of a primitive value.
    pub fn from_primitive<S: Source>(
        prim: &mut Primitive<S>
    ) -> Result<Self, DecodeError<S::Error>> {
        let content = prim.take_all()?;
        Self::check_content(content.as_ref()).map_err(|err| {
            prim.content_err(err)
        })?;
        Ok(Oid(content))
    }

    /// Checks that the content contains a validly encoded OID.
    ///
    /// # Caveats
    ///
    /// This currently doesn’t check that the sub-identifiers are encoded in
    /// the smallest amount of octets.
    fn check_content(content: &[u8]) -> Result<(), &'static str> {
        // There always has to be a first sub-identifier, i.e., content
        // must not be empty. We grab the last byte while we are checking for
        // empty.
        let last = match content.last() {
            Some(last) => *last,
            None => {
                return Err("empty object identifier")
            }
        };

        // The last byte must have bit 8 cleared to indicate the end of a
        // subidentifier.
        if last & 0x80 != 0 {
            return Err("illegal object identifier")
        }

        Ok(())
    }
}

impl<T: AsRef<[u8]>> Oid<T> {
    /// Skip over an object identifier if it matches `self`.
    pub fn skip_if<S: Source>(
        &self, constructed: &mut Constructed<S>,
    ) -> Result<(), DecodeError<S::Error>> {
        constructed.take_primitive_if(Tag::OID, |prim| {
            prim.with_slice_all(|content| {
                // We are assuming that self contains a properly encoded OID,
                // so we don’t really need to check if prim does, too, if we
                // compare for equality.
                if content != self.0.as_ref() {
                    Err("object identifier mismatch")
                }
                else {
                    Ok(())
                }
            })
        })
    }
}

/// # Access to Sub-identifiers
///
impl<T: AsRef<[u8]>> Oid<T> {
    /// Returns an iterator to the components of this object identifiers.
    ///
    /// # Panics
    ///
    /// The returned identifier will eventually panic if `self` does not
    /// contain a correctly encoded object identifier.
    pub fn iter(&self) -> Iter {
        Iter::new(self.0.as_ref())
    }
}


//--- AsRef

impl<T: AsRef<[u8]>> AsRef<[u8]> for Oid<T> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}


//--- PartialEq and Eq

impl<T: AsRef<[u8]>, U: AsRef<[u8]>> PartialEq<Oid<U>> for Oid<T> {
    fn eq(&self, other: &Oid<U>) -> bool {
        self.0.as_ref() == other.0.as_ref()
    }
}

impl<T: AsRef<[u8]>> Eq for Oid<T> { }


//--- Hash

impl<T: AsRef<[u8]>> hash::Hash for Oid<T> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.0.as_ref().hash(state)
    }
}


//--- Display

impl<T: AsRef<[u8]>> fmt::Display for Oid<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut components = self.iter();
        match components.next() {
            Some(component) => component.fmt(f)?,
            None => { return Ok(()) }
        }
        components.try_for_each(|item| write!(f, ".{}", item))
    }
}


//--- encode::PrimitiveContent

impl<T: AsRef<[u8]>> encode::PrimitiveContent for Oid<T> {
    const TAG: Tag = Tag::OID;

    fn encoded_len(&self, _: Mode) -> usize {
        self.0.as_ref().len()
    }

    fn write_encoded<W: io::Write>(
        &self,
        _: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        target.write_all(self.0.as_ref())
    }
}


//--- FromStr

impl<T: AsRef<[u8]> + From<Vec<u8>>> FromStr for Oid<T> {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn from_str(s: &str) -> Result<u32, &'static str> {
            u32::from_str(s).map_err(|_| "only integer components allowed")
        }

        let mut components = s.split('.');
        let (first, second) = match (components.next(), components.next()) {
            (Some(first), Some(second)) => (first, second),
            _ => { return Err("at least two components required"); }
        };

        let first = from_str(first)?;
        if first > 2 {
            return Err("first component can only be 0, 1, or 2.")
        }

        let second = from_str(second)?;
        if first < 2 && second >= 40 {
            return Err("second component for 0. and 1. must be less than 40");
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

        Ok(Oid(bytes.into()))
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
#[derive(Clone, Copy, Debug)]
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
        if self.slice.len() > 5
            || (self.slice.len() == 4 && self.slice[0] & 0x70 != 0)
        {
            return None
        }
        let mut res = 0;
        for &ch in self.slice {
            res = res << 7 | u32::from(ch & 0x7F);
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
}


//--- PartialEq and Eq

impl<'a> PartialEq for Component<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.position == other.position && self.slice == other.slice
    }
}

impl<'a> Eq for Component<'a> { }


//--- Display

impl<'a> fmt::Display for Component<'a> {
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
            if self.slice[i] & 0x80 == 0 {
                let (res, tail) = self.slice.split_at(i + 1);
                if self.position != Position::First {
                    self.slice = tail;
                }
                return Some(Component::new(self.advance_position(), res));
            }
        }
        panic!("illegal object identifier (last octet has bit 8 set)");
    }
}


//============ Tests ========================================================

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn display() {
        assert_eq!(
            "2.5.29.19",
            format!("{}", Oid(&[85, 29, 19])).as_str()
        );
    }

    #[test]
    fn take_and_skip_primitive() {
        fn check(slice: &[u8], is_ok: bool) {
            let take = Primitive::decode_slice(
                slice, Mode::Der, |prim| Oid::from_primitive(prim)
            );
            assert_eq!(take.is_ok(), is_ok);
            if let Ok(oid) = take {
                assert_eq!(oid.0.as_ref(), slice);
            }
            assert_eq!(
                Primitive::decode_slice(
                    slice, Mode::Der, |prim| Oid::skip_primitive(prim)
                ).is_ok(),
                is_ok
            );
        }

        check(b"", false);
        check(b"\x81\x34", true);
        check(b"\x81\x34\x03", true);
        check(b"\x81\x34\x83\x03", true);
        check(b"\x81\x34\x83\x83\x03\x03", true);
        check(b"\x81\x34\x83", false);
    }
}
