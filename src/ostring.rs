//! A BER-encoded OCTET STRING.
//!
//! This is an internal module. It’s public types are re-exported by the
//! parent.
//!
//! XXX This currently panics when trying to encode an octet string in
//!     CER mode. An implementation of that is TODO.

use std::{cmp, hash, io, mem};
use bytes::{BytesMut, Bytes};
use super::captured::Captured;
use super::{decode, encode};
use super::mode::Mode;
use super::length::Length;
use super::tag::Tag;


//------------ OctetString ---------------------------------------------------

/// An OCTET STRING value.
///
/// An octet string is a sequence of octets, i.e., a glorified `[u8]`. Basic
/// Encoding Rules, however, allow this sequence to be broken up into chunks
/// that are encoded separatedly to allow for very large octet strings and
/// cases where one doesn’t yet know the length of the string.
///
/// In order to avoid unnecessary allocations, this type wraps the raw content
/// octets of a BER encoded octet string. As a consequence, assembling the
/// complete string may actually be costly and should only be done if really
/// necessary. As an alternative, there is an iterator over the parts via the
/// `iter` method or the `IntoIterator` trait as well as an iterator over the
/// individual octets via the `octets` method.
/// 
/// Octet strings are sometimes used to store BER encoded data. The
/// `OctetStringSource` type, accessible via the `to_source` method, provides
/// an implementation of the `Source` trait to run a decoder on.
///
/// # BER Encoding
///
/// Octet strings are either encoded as a primitive or a constructed value.
/// In the primitive form, the content octets are the string’s octets. In a
/// constructed form, the content is a sequence of encoded octets strings
/// which in turn may be primitive or constructed. In this case, the string’s
/// octets are the concatenation of all the content octets of the primitive
/// forms in the order as encountered.
///
/// In CER, the string must use the primitive form if it is less than 1000
/// octets long and the constructed form otherwise. The constructed form must
/// consists of a sequence of primitive values each exactly with a 1000
/// octets of content except for the last one.
///
/// In DER, only the primitive form is allowed.
#[derive(Clone, Debug)]
pub struct OctetString(Inner<Bytes, Captured>);

#[derive(Clone, Debug)]
enum Inner<P, C> {
    Primitive(P),
    Constructed(C),
}

/// # Parsing of BER Encoded Octet Strings
///
impl OctetString {
    /// Takes a single octet string value from constructed value content.
    ///
    /// If there is no next value, if the next value does not have the tag
    /// `Tag::OCTET_STRING`, or if it doesn’t contain a correctly encoded
    /// octet string, a malformed error is returned.
    pub fn take_from<S: decode::Source>(
        cons: &mut decode::Constructed<S>
    ) -> Result<Self, S::Err> {
        cons.take_value_if(Tag::OCTET_STRING, Self::take_content_from)
    }

    /// Takes an octet string value from content.
    pub fn take_content_from<S: decode::Source>(
        content: &mut decode::Content<S>
    ) -> Result<Self, S::Err> {
        match *content {
            decode::Content::Primitive(ref mut inner) => {
                if inner.mode() == Mode::Cer && inner.remaining() > 1000 {
                    xerr!(return Err(decode::Error::Malformed.into()))
                }
                Ok(OctetString(Inner::Primitive(inner.take_all()?)))
            }
            decode::Content::Constructed(ref mut inner) => {
                match inner.mode() {
                    Mode::Ber => Self::take_constructed_ber(inner),
                    Mode::Cer => Self::take_constructed_cer(inner),
                    Mode::Der => {
                        xerr!(Err(decode::Error::Malformed.into()))
                    }
                }
            }
        }
    }

    /// Parses a constructed BER encoded octet string.
    ///
    /// It consists octet string values either primitive or constructed.
    fn take_constructed_ber<S: decode::Source>(
        constructed: &mut decode::Constructed<S>
    ) -> Result<Self, S::Err> {
        constructed.capture(|constructed| skip_nested(constructed))
            .map(|captured| OctetString(Inner::Constructed(captured)))
    }

    /// Parses a constructed CER encoded octet string.
    ///
    /// The constructed form contains a sequence of primitive OCTET STRING
    /// values each except for the last one exactly 1000 octets long.
    fn take_constructed_cer<S: decode::Source>(
        constructed: &mut decode::Constructed<S>
    ) -> Result<Self, S::Err> {
        let mut short = false;
        constructed.capture(|con| {
            while let Some(()) = con.take_opt_primitive_if(Tag::OCTET_STRING,
                                                           |primitive| {
                if primitive.remaining() > 1000 {
                    xerr!(return Err(decode::Error::Malformed.into()));
                }
                if primitive.remaining() < 1000 {
                    if short {
                        xerr!(return Err(decode::Error::Malformed.into()));
                    }
                    short = true
                }
                primitive.skip_all()
            })? { }
            Ok(())
        }).map(|captured| OctetString(Inner::Constructed(captured)))
    }

    pub fn encode_as<'a>(&'a self, tag: Tag) -> impl encode::Values + 'a {
        OctetStringEncoder::new(self, tag)
    }

    pub fn encode<'a>(&'a self) -> impl encode::Values + 'a {
        self.encode_as(Tag::OCTET_STRING)
    }

    /// Encodes any Values structure into an OctetString.
    pub fn encode_into_der<V: encode::Values>(v: V) -> impl encode::Values {
        WrappingOctetStringEncoder(v)
    }
}


/// # Content Access
///
impl OctetString {
    /// Creates an octet string from a Bytes value.
    pub fn new(bytes: Bytes) -> Self {
        OctetString(Inner::Primitive(bytes))
    }

    /// Returns an iterator over the parts of the octet string.
    ///
    /// The iterator will produce `&[u8]` which, when appended produce the
    /// complete content of the octet string.
    pub fn iter(&self) -> OctetStringIter {
        match self.0 {
            Inner::Primitive(ref inner) => {
                OctetStringIter(Inner::Primitive(inner.as_ref()))
            }
            Inner::Constructed(ref inner) => {
                OctetStringIter(Inner::Constructed(inner.as_ref()))
            }
        }
    }

    /// Returns an iterator over the individual octets of the string.
    pub fn octets(&self) -> OctetStringOctets {
        OctetStringOctets::new(self.iter())
    }

    /// Returns a reference to the complete content if possible.
    ///
    /// The method will return a bytes slice of the content if the octet
    /// string was encoded as a single primitive value or `None` otherwise.
    ///
    /// This is guaranteed to return some slice if the value was produced by
    /// decoding in DER mode.
    pub fn as_slice(&self) -> Option<&[u8]> {
        match self.0 {
            Inner::Primitive(ref inner) => Some(inner.as_ref()),
            Inner::Constructed(_) => None
        }
    }

    /// Produces a bytes value with the string’s content.
    ///
    /// If the octet string was encoded as a single primitive value, the
    /// method will simply clone the contnent. Otherwise it will produce
    /// an entirely new bytes value from the concatenated content of all
    /// the primitive values.
    pub fn to_bytes(&self) -> Bytes {
        if let Inner::Primitive(ref inner) = self.0 {
            return inner.clone()
        }
        let mut res = BytesMut::new();
        self.iter().for_each(|x| res.extend_from_slice(x));
        res.freeze()
    }

    /// Returns the length of the content.
    ///
    /// This is _not_ the length of the encoded value but of the actual
    /// octet string.
    pub fn len(&self) -> usize {
        if let Inner::Primitive(ref inner) = self.0 {
            return inner.len()
        }
        self.iter().fold(0, |len, x| len + x.len())
    }

    /// Creates a source that can be used to decode the string’s content.
    ///
    /// The returned value contains a clone of the string (which, because of
    /// the use of `Bytes` is rather cheap) that implements the `Source`
    /// trait and thus can be used to decode the string’s content.
    pub fn to_source(&self) -> OctetStringSource {
        OctetStringSource::new(self)
    }
}


//--- PartialEq and Eq

impl PartialEq for OctetString {
    fn eq(&self, other: &OctetString) -> bool {
        if let (Some(l), Some(r)) = (self.as_slice(), other.as_slice()) {
            return l == r
        }
        let mut sit = self.iter();
        let mut oit = other.iter();
        let (mut ssl, mut osl) = match (sit.next(), oit.next()) {
            (Some(ssl), Some(osl)) => (ssl, osl),
            (None, None) => return true,
            _ => return false,
        };
        loop {
            if ssl.is_empty() {
                ssl = sit.next().unwrap_or(b"");
            }
            if osl.is_empty() {
                osl = oit.next().unwrap_or(b"");
            }
            match (ssl.is_empty(), osl.is_empty()) {
                (true, true) => return true,
                (false, false) => { },
                _ => return false,
            }
            let len = cmp::min(ssl.len(), osl.len());
            if ssl[..len] != osl[..len] {
                return false
            }
            ssl = &ssl[len..];
            osl = &osl[len..];
        }
    }
}

impl<T: AsRef<[u8]>> PartialEq<T> for OctetString {
    fn eq(&self, other: &T) -> bool {
        let mut other = other.as_ref();

        if let Some(slice) = self.as_slice() {
            return slice == other
        }

        for part in self.iter() {
            if part.len() > other.len() {
                return false
            }
            if part.len() == other.len() {
                return part == other
            }
            if part != &other[..part.len()] {
                return false
            }
            other = &other[part.len()..]
        }
        return false
    }
}

impl Eq for OctetString { }


//--- PartialOrd and Ord

impl PartialOrd for OctetString {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: AsRef<[u8]>> PartialOrd<T> for OctetString {
    fn partial_cmp(&self, other: &T) -> Option<cmp::Ordering> {
        let mut other = other.as_ref();

        if let Some(slice ) = self.as_slice() {
            return slice.partial_cmp(other)
        }

        for part in self.iter() {
            if part.len() >= other.len() {
                return Some(part.cmp(other))
            }
            match part.cmp(&other[..part.len()]) {
                cmp::Ordering::Equal => { }
                other => return Some(other)
            }
            other = &other[part.len()..]
        }
        return Some(cmp::Ordering::Less)
    }
}

impl Ord for OctetString {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        if let (Some(l), Some(r)) = (self.as_slice(), other.as_slice()) {
            return l.cmp(&r)
        }

        let mut siter = self.iter();
        let mut oiter = other.iter();
        let mut spart = b"".as_ref();
        let mut opart = b"".as_ref();

        loop {
            if spart.is_empty() {
                spart = siter.next().unwrap_or(b"");
            }
            if opart.is_empty() {
                opart = oiter.next().unwrap_or(b"");
            }
            match (spart.is_empty(), opart.is_empty()) {
                (true, true) => return cmp::Ordering::Equal,
                (true, false) => return cmp::Ordering::Less,
                (false, true) => return cmp::Ordering::Greater,
                (false, false) => { },
            }
            let len = cmp::min(spart.len(), opart.len());
            match spart[..len].cmp(&opart[..len]) {
                cmp::Ordering::Equal => { }
                other => return other
            }
            spart = &spart[len..];
            opart = &opart[len..];
        }
    }
}


//--- Hash

impl hash::Hash for OctetString {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        for part in self.iter() {
            part.hash(state)
        }
    }
}


//--- IntoIterator

impl<'a> IntoIterator for &'a OctetString {
    type Item = &'a [u8];
    type IntoIter = OctetStringIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}


//------------ OctetStringSource ---------------------------------------------

/// A source atop an octet string.
///
/// You can get a value of this type by calling `OctetString::source`.
//
//  Assuming we have a correctly encoded octet string, its content is a
//  sequence of value headers (i.e., tag and length octets) and actual string
//  content. There’s three types of headers we could encounter: primitive
//  octet strings, constructed octet strings, and end-of-values. The first
//  one is followed by as many octets of actual content as given in the
//  length octets. The second one is followed by more values recursively and
//  the third one is by nothing. So, only the primitive values actually
//  contain content and, because however they are nested, they appear in
//  order, we can ignore all the rest.
pub struct OctetStringSource {
    /// The content of primitive value we currently work on.
    current: Bytes,

    /// The remainder of the value after the value in `current`.
    remainder: Bytes,
}

impl OctetStringSource {
    fn new(from: &OctetString) -> Self {
        match from.0 {
            Inner::Primitive(ref inner) => {
                OctetStringSource {
                    current: inner.clone(),
                    remainder: Bytes::new(),
                }
            }
            Inner::Constructed(ref inner) => {
                OctetStringSource {
                    current: Bytes::new(),
                    remainder: inner.clone().into_bytes()
                }
            }
        }
    }
                
    fn next_primitive(&mut self) -> Option<Bytes> {
        while !self.remainder.is_empty() {
            let (tag, cons) = Tag::take_from(&mut self.remainder).unwrap();
            let length = Length::take_from(
                &mut self.remainder, Mode::Ber
            ).unwrap();
            match tag {
                Tag::OCTET_STRING => {
                    if cons {
                        continue
                    }
                    let length = match length {
                        Length::Definite(len) => len,
                        _ => unreachable!()
                    };
                    return Some(self.remainder.split_to(length))
                }
                Tag::END_OF_VALUE => continue,
                _ => unreachable!()
            }
        }
        None
    }
}

impl decode::Source for OctetStringSource {
    type Err = decode::Error;

    fn request(&mut self, len: usize) -> Result<usize, decode::Error> {
        if self.current.len() < len && !self.remainder.is_empty() {
            // Make a new current that is at least `len` long.
            let mut current = BytesMut::from(self.current.clone());
            while current.len() < len {
                if let Some(bytes) = self.next_primitive() {
                    current.extend_from_slice(bytes.as_ref())
                }
                else {
                    break
                }
            }
            self.current = current.freeze()
        }
        Ok(self.current.len())
    }

    fn advance(&mut self, mut len: usize) -> Result<(), decode::Error> {
        while len > self.current.len() {
            len -= self.current.len();
            self.current = match self.next_primitive() {
                Some(value) => value,
                None => {
                    xerr!(return Err(decode::Error::Malformed))
                }
            }
        }
        self.current.advance(len);
        Ok(())
    }

    fn slice(&self) -> &[u8] {
        self.current.as_ref()
    }

    fn bytes(&self, start: usize, end: usize) -> Bytes {
        self.current.slice(start, end)
    }
}


//------------ OctetStringIter -----------------------------------------------

/// An iterator over the segments of an octet string.
///
/// You can get a value of this type by calling `OctetString::iter` or relying
/// on the `IntoIterator` impl for a `&OctetString`.
#[derive(Clone, Debug)]
pub struct OctetStringIter<'a>(Inner<&'a [u8], &'a [u8]>);

impl<'a> Iterator for OctetStringIter<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<Self::Item> {
        match self.0 {
            Inner::Primitive(ref mut inner) => {
                if inner.is_empty() {
                    None
                }
                else {
                    Some(mem::replace(inner, &b""[..]))
                }
            }
            Inner::Constructed(ref mut inner) => {
                while !inner.is_empty() {
                    let (tag, cons) = Tag::take_from(inner).unwrap();
                    let length = Length::take_from(inner, Mode::Ber).unwrap();
                    match tag {
                        Tag::OCTET_STRING => {
                            if cons {
                                continue
                            }
                            let length = match length {
                                Length::Definite(len) => len,
                                _ => unreachable!()
                            };
                            let res = &inner[..length];
                            *inner = &inner[length..];
                            return Some(res)
                        }
                        Tag::END_OF_VALUE => continue,
                        _ => unreachable!()
                    }
                }
                None
            }
        }
    }
}


//------------ OctetStringOctets ---------------------------------------------

/// An iterator over the octets in an octet string.
///
/// You can get a value of this type by calling `OctetString::octets`.
pub struct OctetStringOctets<'a> {
    cur: &'a [u8],
    iter: OctetStringIter<'a>,
}

impl<'a> OctetStringOctets<'a> {
    fn new(iter: OctetStringIter<'a>) -> Self {
        OctetStringOctets {
            cur: b"",
            iter: iter
        }
    }
}

impl<'a> Iterator for OctetStringOctets<'a> {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        if self.cur.is_empty() {
            let next = match self.iter.next() {
                Some(some) => some,
                None => return None,
            };
            self.cur = next;
        }
        let res = self.cur[0];
        self.cur = &self.cur[1..];
        Some(res)
    }
}

//------------ WrappingOctetStringEncoder ------------------------------------

/// Allows wrapping of any `impl encode::Values` inside a DER encoded
/// OctetString. This is particularly intended for use with X509 Extensions,
/// which wrap the value the particular extension DER structure as octets
/// within an OctetString.
pub struct WrappingOctetStringEncoder<V: encode::Values>(V);


//--- encode::Values

impl<V: encode::Values> encode::Values for WrappingOctetStringEncoder<V> {

    fn encoded_len(&self, mode: Mode) -> usize {
        if mode == Mode::Cer {
            unimplemented!()
        }

        encode::total_encoded_len(
            Tag::OCTET_STRING,
            self.0.encoded_len(Mode::Der)
        )
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        if mode == Mode::Cer {
            unimplemented!()
        }

        encode::write_header(
            target,
            Tag::OCTET_STRING,
            false,
            self.0.encoded_len(Mode::Der))?;

        self.0.write_encoded(Mode::Der, target)
    }
}


//------------ OctetStringEncoder --------------------------------------------

#[derive(Clone, Debug)]
pub struct OctetStringEncoder<'a> {
    value: &'a OctetString,
    tag: Tag,
}

impl<'a> OctetStringEncoder<'a> {
    fn new(value: &'a OctetString, tag: Tag) -> Self {
        OctetStringEncoder { value, tag }
    }
}


//--- encode::Values

impl<'a> encode::Values for OctetStringEncoder<'a> {
    fn encoded_len(&self, mode: Mode) -> usize {
        match mode {
            Mode::Ber => {
                let len = match self.value.0 {
                    Inner::Primitive(ref bytes) => bytes.len(),
                    Inner::Constructed(ref captured) => captured.len(),
                };
                self.tag.encoded_len()
                + Length::Definite(len).encoded_len()
                + len
            }
            Mode::Cer => {
                unimplemented!()
            }
            Mode::Der => {
                let len = self.value.len();
                self.tag.encoded_len()
                + Length::Definite(len).encoded_len()
                + len
            }
        }
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        match mode {
            Mode::Ber => {
                match self.value.0 {
                    Inner::Primitive(ref bytes) => {
                        self.tag.write_encoded(false, target)?;
                        Length::Definite(bytes.len()).write_encoded(target)?;
                        target.write_all(bytes.as_ref())
                    }
                    Inner::Constructed(ref captured) => {
                        self.tag.write_encoded(true, target)?;
                        Length::Definite(captured.len()).write_encoded(target)?;
                        target.write_all(captured.as_slice())
                    }
                }
            }
            Mode::Cer => {
                unimplemented!()
            }
            Mode::Der => {
                self.tag.write_encoded(false, target)?;
                Length::Definite(self.value.len()).write_encoded(target)?;
                for slice in self.value.iter() {
                    target.write_all(slice)?;
                }
                Ok(())
            }
        }
    }
}


//------------ Helper Functions ----------------------------------------------

fn skip_nested<S>(con: &mut decode::Constructed<S>) -> Result<(), S::Err>
where S: decode::Source {
    while let Some(()) = con.take_opt_value_if(Tag::OCTET_STRING, |content| {
        match content {
            decode::Content::Constructed(ref mut inner) => {
                skip_nested(inner)?
            }
            decode::Content::Primitive(ref mut inner) => {
                inner.skip_all()?
            }
        }
        Ok(())
    })? { }
    Ok(())
}


//------------ Tests ---------------------------------------------------------

#[cfg(test)]
pub mod tests {

    use super::*;
    use encode::{Values, PrimitiveContent};

    #[test]
    fn should_wrap_content_in_octetstring() {
        let mut v = Vec::new();
        let enc = OctetString::encode_into_der(true.value());
        enc.write_encoded(Mode::Der, &mut v).unwrap();

        // 4, 3          OctetString with content length 3
        //    1, 1, 255    Boolean, length 1, Value true
        assert_eq!(vec![4, 3, 1, 1, 255], v);

        let l = enc.encoded_len(Mode::Der);
        assert_eq!(l, v.len());
    }
}



