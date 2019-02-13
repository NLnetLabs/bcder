//! ASN.1 Object Identifiers.
//!
//! This module contains the [`Oid`] type that implements object identifiers,
//! a construct used by ANS.1 to uniquely identify all sorts of things. The
//! type is also re-exported at the top-level.
//!
//! [`Oid`]: struct.Oid.html

use std::{fmt, hash, io};
use bytes::Bytes;
use super::{decode, encode};
use super::decode::Source;
use super::mode::Mode;
use super::tag::Tag;


//------------ Oid -----------------------------------------------------------

/// An object identifer.
///
/// Object identifiers are globally unique, hierarchical values that are used
/// to identify objects or their type. When written, they are presented as a
/// sequence of integers separated by dots such as ‘1.3.6.1.5.5.7.1’ or with
/// the integers separated by white space and enclosed in curly braces such
/// as ‘{ 1 3 6 1 5 5 7 1 }’. Individual integers or sequences of integers
/// can also be given names which then are used instead of the integers.
/// 
/// Values of this type keep a single object identifer in its BER encoding,
/// i.e., in some form of byte sequence. Because different representations
/// may be useful, the type is actually generic over something that can
/// become a reference to a bytes slice. Parsing is only defined for `Bytes`
/// values, though.
///
/// The only use for object identifiers currently is to compare them to
/// predefined values. For this purpose, you typically define your known
/// object identifiers in a `oid` submodule as contants of
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
pub struct Oid<T: AsRef<[u8]>=Bytes>(pub T);

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
    /// the `Tag::OID`, or if it is not a primitive value, returns a malformed
    /// error.
    pub fn skip_in<S: decode::Source>(
        cons: &mut decode::Constructed<S>
    ) -> Result<(), S::Err> {
        cons.take_primitive_if(Tag::OID, |prim| prim.skip_all())
    }

    /// Skips over an optional object identifier value.
    ///
    /// If the source has reached its end of if the next value does not have
    /// the `Tag::OID`, returns `Ok(None)`. If the next value has the right
    /// tag but is not a primitive value, returns a malformed error.
    pub fn skip_opt_in<S: decode::Source>(
        cons: &mut decode::Constructed<S>
    ) -> Result<Option<()>, S::Err> {
        cons.take_opt_primitive_if(Tag::OID, |prim| prim.skip_all())
    }

    /// Takes an object identifier value from the source.
    ///
    /// If the source has reached its end, if the next value does not have
    /// the `Tag::OID`, or if it is not a primitive value, returns a malformed
    /// error.
    pub fn take_from<S: decode::Source>(
        constructed: &mut decode::Constructed<S>
    ) -> Result<Self, S::Err> {
        constructed.take_primitive_if(Tag::OID, |content| {
            content.take_all().map(Oid)
        })
    }

    /// Takes an optional object identifier value from the source.
    ///
    /// If the source has reached its end of if the next value does not have
    /// the `Tag::OID`, returns `Ok(None)`. If the next value has the right
    /// tag but is not a primitive value, returns a malformed error.
    pub fn take_opt_from<S: decode::Source>(
        constructed: &mut decode::Constructed<S>
    ) -> Result<Option<Self>, S::Err> {
        constructed.take_opt_primitive_if(Tag::OID, |content| {
            content.take_all().map(Oid)
        })
    }
}

impl<T: AsRef<[u8]>> Oid<T> {
    /// Skip over an object identifier if it matches `self`.
    pub fn skip_if<S: decode::Source>(
        &self,
        constructed: &mut decode::Constructed<S>
    ) -> Result<(), S::Err> {
        constructed.take_primitive_if(Tag::OID, |content| {
            let len = content.remaining();
            content.request(len)?;
            if &content.slice()[..len] == self.0.as_ref() {
                content.skip_all()?;
                Ok(())
            }
            else {
                xerr!(Err(decode::Error::Malformed.into()))
            }
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
        // XXX This can’t deal correctly with overly large components.
        //     Since this is a really rare (if not non-existant) case,
        //     I can’t be bothered to figure out how to convert a seven
        //     bit integer into decimal.
        let mut components = self.iter();
        // There’s at least one and it is always an valid u32.
        write!(f, "{}", components.next().unwrap().to_u32().unwrap())?;
        for component in components {
            if let Some(val) = component.to_u32() {
                write!(f, ".{}", val)?;
            }
            else {
                write!(f, ".(not implemented)")?;
            }
        }
        Ok(())
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
    /// The position of the component in the object identifer.
    position: Position,

    /// The octets of the subidentifer.
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
/// As the first two components of the object identifer are encoded in the
/// first subidentifier of the encoded value, we have three different cases.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Position {
    /// This is the first component of the identifier.
    ///
    /// This is 0 if the integer value of the subidentifer is 0..39,
    /// 1 for 40..79, and 2 for anything else.
    First,

    /// This is the second component of the identifier.
    ///
    /// This is the integer value of the subidentifer module 40 if the value
    /// is below 80 and otherwise the value minus 80.
    Second,

    /// This is any later component of the identifier.
    ///
    /// This is identical to the integer value of the subidentifier.
    Other,
}

impl<'a> Component<'a> {
    /// Creates a new component.
    fn new(slice: &'a [u8], position: Position) -> Self {
        Component { slice, position }
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
                let (res, tail) = self.slice.split_at(i);
                self.slice = tail;
                return Some(Component::new(res, self.advance_position()));
            }
        }
        panic!("illegal object identifier (last octet has bit 8 set)");
    }
}

