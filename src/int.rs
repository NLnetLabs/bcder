//! Unbounded integers.
//
//  Reviewer note:
//
//     {IntegerArray,UnsignedArray}::from_primitive_ref do crazy slice
//     wrangling need to be thoroughly reviewed.

use std::{cmp, error, fmt, hash, io, mem};
use std::sync::Arc;
use crate::decode;
use crate::{Mode, Tag};
use crate::decode::{Constructed, FromPrimitive, Primitive};
use crate::encode::{PrimitiveContent, Target};
use crate::length::Length;


//------------ Integer -------------------------------------------------------

/// A BER encoded integer.
///
/// As integers are variable length in BER, this type is a wrapper atop a
/// byte slice. This makes the type unsigned and needing to be kept behind
/// some pointer, typically a `Box<_>` or an `Arc<_>`.
///
/// A value of this type represents a signed integer. If a value is defined
/// as an unsigned integer, i.e., as `INTEGER (0..MAX)`, you should use the
/// sibling type [`Unsigned`] instead.
///
/// # BER Encoding
///
/// In BER, an INTEGER is encoded as a primitive value with the content octets
/// providing a shortest possible variable-length, big-endian, two’s
/// complement byte sequence of that integer. Thus, the most-significant bit
/// of the first octet serves as the sign bit.
#[derive(Debug)]
#[repr(transparent)]
pub struct Integer([u8]);

impl Integer {
    /// Checks that a byte slice contains a correctly encoded integer.
    ///
    /// Because integers need to be encoded in the shortest possible form,
    /// the leftmost nine bits (so, the first octet and the most
    /// significant bit of the second octet) must not all be zero or all be
    /// one. Also, the slice must not be empty.
    fn check_slice(slice: &[u8]) -> Result<(), InvalidInteger> {
        match (slice.first(), slice.get(1).map(|x| x & 0x80 != 0)) {
            (Some(0), Some(false)) => Err(InvalidInteger(())),
            (Some(0xFF), Some(true)) => Err(InvalidInteger(())),
            (None, _) => Err(InvalidInteger(())),
            _ => Ok(())
        }
    }

    /// Creates an integer from a byte slice without checking the encoding.
    ///
    /// # Safety
    ///
    /// The caller needs to ensure that the byte slice contains a correctly
    /// encoded integer.
    pub unsafe fn from_slice_unchecked(slice: &[u8]) -> &Self {
        unsafe { mem::transmute(slice) }
    }

    /// Creates an integer from a boxed slice without checking the encoding.
    ///
    /// # Safety
    ///
    /// The caller needs to ensure that the byte slice contains a correctly
    /// encoded integer.
    pub unsafe fn from_box_unchecked(src: Box<[u8]>) -> Box<Self> {
        unsafe { mem::transmute(src) }
    }

    /// Creates an integer from a byte slice.
    pub fn from_slice(slice: &[u8]) -> Result<&Self, InvalidInteger> {
        Self::check_slice(slice)?;
        Ok(unsafe { Self::from_slice_unchecked(slice) })
    }

    /// Creates a boxed integer from a boxed slice.
    pub fn from_box(src: Box<[u8]>) -> Result<Box<Self>, InvalidInteger> {
        Self::check_slice(src.as_ref())?;
        Ok(unsafe { Self::from_box_unchecked(src) })
    }

    /// Returns a bytes slice with the raw content.
    pub fn as_slice(&self) -> &[u8] {
        self.0.as_ref()
    }

    /// Returns whether the number is zero.
    pub fn is_zero(&self) -> bool {
        matches!(
            (self.0.first().copied(), self.0.get(1).copied()),
            (Some(0), None)
        )
    }

    /// Returns whether the integer is positive.
    ///
    /// Also returns `false` if the number is zero.
    pub fn is_positive(&self) -> bool {
        let Some(first) = self.0.first().copied() else {
            return false
        };
        if first == 0 && self.0.get(1).is_none() {
            return false
        }
        first & 0x80 == 0x00
    }

    /// Returns whether the integer is negative.
    ///
    /// Also returns `false` if the number is zero.
    pub fn is_negative(&self) -> bool {
        self.0.first().copied().unwrap_or(0) & 0x80 == 0x80
    }
}

/// # Decoding
impl Integer {
    /// Decodes the next value as a signed integer value.
    ///
    /// This requires the next value in `cons` to be a primitive value with
    /// tag `INTEGER` that contains a correctly encoded integer.
    pub fn take_from<M: Mode, R: io::BufRead>(
        cons: &mut Constructed<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        Self::from_primitive(
            cons.next_primitive_with(Tag::INTEGER)?
        )
    }

    /// Decodes the next value as a signed integer, borrowing the content.
    ///
    /// This requires the next value in `cons` to be a primitive value with
    /// tag `INTEGER` that contains a correctly encoded integer.
    pub fn take_from_borrowed<'s, M: Mode>(
        cons: &mut Constructed<M, &'s [u8]>
    ) -> Result<&'s Self, decode::Error> {
        Self::from_primitive_borrowed(
            cons.next_primitive_with(Tag::INTEGER)?
        )
    }

    /// Creates an integer from the content of a primitive value.
    pub fn from_primitive<M, R: io::BufRead>(
        mut prim: Primitive<M, R>,
    ) -> Result<Box<Self>, decode::Error> {
        let len = usize::try_from(prim.remaining()).map_err(|_| {
            prim.err_at_start(OverflowError(()))
        })?;
        Self::from_box(prim.read_exact_into_box(len)?).map_err(|err| {
            prim.err_at_start(err)
        })
    }

    /// Creates an borrowed integer from the content of a primitive value.
    pub fn from_primitive_borrowed<'s, M>(
        mut prim: Primitive<M, &'s [u8]>
    ) -> Result<&'s Self, decode::Error> {
        let len = usize::try_from(prim.remaining()).map_err(|_| {
            prim.err_at_start(OverflowError(()))
        })?;
        Self::from_slice(prim.read_exact_borrowed(len)?).map_err(|err| {
            prim.err_at_start(err)
        })
    }
}


//--- From

impl<'a, const N: usize> From<&'a IntegerArray<N>> for &'a Integer {
    fn from(src: &'a IntegerArray<N>) -> Self {
        unsafe { Integer::from_slice_unchecked(src.as_encoded_slice()) }
    }
}

impl<'a> From<&'a Integer> for Box<Integer> {
    fn from(src: &'a Integer) -> Self {
        let res = Box::<[u8]>::from(&src.0);
        unsafe { Integer::from_box_unchecked(res) }
    }
}

impl<const N: usize> From<IntegerArray<N>> for Box<Integer> {
    fn from(src: IntegerArray<N>) -> Self {
        let res = Box::<[u8]>::from(src.as_encoded_slice());
        unsafe { Integer::from_box_unchecked(res) }
    }
}

impl<'a> From<&'a Integer> for Arc<Integer> {
    fn from(src: &'a Integer) -> Self {
        Box::<Integer>::from(src).into()
    }
}

impl<const N: usize> From<IntegerArray<N>> for Arc<Integer> {
    fn from(src: IntegerArray<N>) -> Self {
        Box::<Integer>::from(src).into()
    }
}


//--- AsRef

impl AsRef<[u8]> for Integer {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}


//--- PartialEq and Eq

impl PartialEq for Integer {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl PartialEq<Unsigned> for Integer {
    fn eq(&self, other: &Unsigned) -> bool {
        self.0.eq(&other.0)
    }
}

impl Eq for Integer { }


//--- PartialOrd and Ord

impl PartialOrd for Integer {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<Unsigned> for Integer {
    fn partial_cmp(&self, other: &Unsigned) -> Option<cmp::Ordering> {
        Some(self.cmp(other.as_integer()))
    }
}

impl Ord for Integer {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match (self.is_positive(), other.is_positive()) {
            (true, true) => { // i.e., both > 0
                match self.0.len().cmp(&other.0.len()) {
                    cmp::Ordering::Equal => {
                        for (l, r) in self.0.iter().zip(other.0.iter()) {
                            match l.cmp(r) {
                                cmp::Ordering::Equal => { }
                                cmp => return cmp
                            }
                        }
                        cmp::Ordering::Equal
                    }
                    cmp => cmp
                }
            }
            (false, false) => { // i.e., both <= 0
                match self.0.len().cmp(&other.0.len()) {
                    cmp::Ordering::Equal => {
                        for (l, r) in self.0.iter().zip(other.0.iter()) {
                            match l.cmp(r) {
                                cmp::Ordering::Equal => { }
                                cmp => return cmp.reverse()
                            }
                        }
                        cmp::Ordering::Equal
                    }
                    cmp => cmp.reverse()
                }
            }
            (false, true) => cmp::Ordering::Less,
            (true, false) => cmp::Ordering::Greater,
        }
    }
}


//--- Hash

impl hash::Hash for Integer {
    fn hash<H: hash::Hasher>(&self, h: &mut H) {
        self.0.hash(h)
    }
}


//--- PrimitiveContent

impl<M> PrimitiveContent<M> for &'_ Integer {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(self) -> Length {
        self.as_slice().len().into()
    }

    fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(self.as_slice())
    }
}

impl<M> PrimitiveContent<M> for &'_ Box<Integer> {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(self) -> Length {
        self.as_slice().len().into()
    }

    fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(self.as_slice())
    }
}

impl<M> PrimitiveContent<M> for &'_ Arc<Integer> {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(self) -> Length {
        self.as_slice().len().into()
    }

    fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(self.as_slice())
    }
}


//------------ IntegerArray --------------------------------------------------

/// A BER encoded integer backed by a byte array.
///
/// This is a fixed length version of the variable-sized [`Integer`] type,
/// essentially a big-ending signed integer of length `N`. The content is
/// right-aligned within the byte array so as to represent a big-endian
/// signed integer of size `N`.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct IntegerArray<const N: usize>([u8; N]);

impl<const N: usize> IntegerArray<N> {
    /// Creates a new value from a byte array.
    pub fn from_array(array: [u8; N]) -> Self {
        Self(array)
    }

    /// Returns the underlying byte array.
    pub fn to_array(self) -> [u8; N] {
        self.0
    }

    /// Returns a bytes slice with the raw octets.
    ///
    /// The slice will contain the full content, i.e., it will be of length
    /// `N`.
    pub fn as_slice(&self) -> &[u8] {
        self.0.as_ref()
    }

    /// Returns a bytes slice with the encoded value.
    ///
    /// This value skips leading “filler” octets and thus may return a slice
    /// shorter than `N`.
    pub fn as_encoded_slice(&self) -> &[u8] {
        let mut slice = self.as_slice();
        if self.0[0] & 0x80 != 0 {
            while let Some((&first, tail)) = slice.split_first() {
                if first != 0xFF {
                    return slice
                }
                slice = tail; 
            }
            b"\xFF"
        }
        else {
            while let Some((&first, tail)) = slice.split_first() {
                if first != 0x00 {
                    return slice
                }
                slice = tail; 
            }
            b"\x00"
        }
    }
}

/// # Decoding
impl<const N: usize> IntegerArray<N> {
    /// Decodes the next value as a integer.
    ///
    /// This requires the next value in `cons` to be a primitive value with
    /// tag `INTEGER` that contains a correctly encoded integer fitting into
    /// `N` bytes.
    pub fn take_from<M: Mode, R: io::BufRead>(
        cons: &mut Constructed<M, R>
    ) -> Result<Self, decode::Error> {
        Self::from_primitive(
            cons.next_primitive_with(Tag::INTEGER)?
        )
    }

    /// Creates an integer from the content of a primitive value.
    pub fn from_primitive<M, R: io::BufRead>(
        mut prim: Primitive<M, R>,
    ) -> Result<Self, decode::Error> {
        Self::from_primitive_ref(&mut prim)
    }

    /// Creates an integer from content of a primitive value (legacy version).
    ///
    /// This function is identical to [`from_primitive`][Self::from_primitive]
    /// but takes a mut ref of the primitive. It exists solely for
    /// compatibility with existing code and will be removed.
    pub(super) fn from_primitive_ref<M, R: io::BufRead>(
        prim: &mut Primitive<M, R>,
    ) -> Result<Self, decode::Error> {
        let start = usize::try_from(prim.remaining()).ok().and_then(|len| {
            N.checked_sub(len)
        }).ok_or_else(|| prim.err_at_start(OverflowError(())))?;
        if start == N {
            return Err(prim.err_at_start(InvalidInteger(())))
        }

        let mut res = [0u8; N];

        // Safety: start is determined by subtracting from N
        let (head, tail) = res.as_mut_slice().split_at_mut(start);
        prim.read_exact(tail)?;
        Integer::check_slice(tail).map_err(|err| {
            prim.err_at_start(err)
        })?;

        // If the sign bit in tail was set, we need to
        // fill the head with 0xFF so the two’s complement works out. Because
        // we start with all zeros, we don’t need to do this for a positive
        // number.
        if tail.first().copied().unwrap_or(0) & 0x80 != 0 {
            head.fill(0xFF)
        }
        Ok(Self(res))
    }
}


//--- Default

impl<const N: usize> Default for IntegerArray<N> {
    fn default() -> Self {
        Self([0u8; N])
    }
}


//--- PrimitiveContent

impl<const N: usize, M> PrimitiveContent<M> for IntegerArray<N> {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(self) -> Length {
        self.as_encoded_slice().len().into()
    }

    fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(self.as_encoded_slice())
    }
}


//------------ Signed Built-in Integers --------------------------------------

macro_rules! signed_builtin {
    ( $int:ident ) => {
        signed_builtin!{$int, { mem::size_of::<$int>() }}
    };

    ( $int:ident, $len:expr ) => {
        impl From<IntegerArray<$len>> for $int {
            fn from(src: IntegerArray<$len>) -> Self {
                Self::from_be_bytes(src.0)
            }
        }

        impl From<$int> for IntegerArray<$len> {
            fn from(src: $int) -> Self {
                Self::from_array(src.to_be_bytes())
            }
        }

        impl From<$int> for Box<Integer> {
            fn from(src: $int) -> Self {
                IntegerArray::from(src).into()
            }
        }

        impl<M> FromPrimitive<M> for $int {
            const TAG: Tag = Tag::INTEGER;

            fn from_primitive<R: io::BufRead>(
                prim: Primitive<M, R>
            ) -> Result<Self, decode::Error> {
                Ok(IntegerArray::from_primitive(prim)?.into())
            }
        }

        impl<M> PrimitiveContent<M> for $int {
            const TAG: Tag = Tag::INTEGER;

            fn encoded_len(self) -> Length {
                PrimitiveContent::<M>::encoded_len(
                    IntegerArray::from(self)
                )
            }

            fn write_encoded<T: Target>(
                self, target: &mut T
            ) -> Result<(), T::Error> {
                PrimitiveContent::<M>::write_encoded(
                    IntegerArray::from(self), target
                )
            }
        }
    };
}

signed_builtin!(i8);
signed_builtin!(i16);
signed_builtin!(i32);
signed_builtin!(i64);
signed_builtin!(i128);


//------------ Unsigned ------------------------------------------------------

/// A BER encoded unsigned integer.
///
/// As integers are variable length in BER, this type is a wrapper atop a
/// byte slice. This makes the type unsigned and needing to be kept behind
/// some pointer, typically a `Box<_>` or an `Arc<_>`.
///
/// A value of this type represents an unsigned integer, usually defined
/// as `INTEGER (0..MAX)` in ASN.1. If you need a integer without any
/// restrictions, you can use `Integer`.
///
/// # BER Encoding
///
/// In BER, an INTEGER is encoded as a primitive value with the content octets
/// providing a shortest possible variable-length, big-endian, two’s
/// complement byte sequence of that integer. Thus, the most-significant bit
/// of the first octet serves as the sign bit and, for an unsigned integer,
/// has to be unset. This means that unsigned integers that have their most
/// significant bit set need to be padded with a zero byte.
#[derive(Debug)]
pub struct Unsigned([u8]);

impl Unsigned {
    /// Checks that a byte slice contains a correctly encoded integer.
    ///
    /// Checks that the slice is not empty. Checks that the most significant
    /// bit is not set. Checks that if the first octet is zero, the most
    /// significant bit of a possible second octet is set.
    fn check_slice(slice: &[u8]) -> Result<(), InvalidInteger> {
        match (slice.first(), slice.get(1).map(|x| x & 0x80 != 0)) {
            (Some(val), _) if val & 0x80 == 0 => Err(InvalidInteger(())),
            (Some(0), Some(false)) => Err(InvalidInteger(())),
            (None, _) => Err(InvalidInteger(())),
            _ => Ok(())
        }
    }

    /// Creates an unsigned from a byte slice without checking the encoding.
    ///
    /// # Safety
    ///
    /// The caller needs to ensure that the byte slice contains a correctly
    /// encoded unsigned integer.
    pub unsafe fn from_slice_unchecked(slice: &[u8]) -> &Self {
        unsafe { mem::transmute(slice) }
    }

    /// Creates an unsigned from a boxed slice without checking the encoding.
    ///
    /// # Safety
    ///
    /// The caller needs to ensure that the byte slice contains a correctly
    /// encoded integer.
    pub unsafe fn from_box_unchecked(src: Box<[u8]>) -> Box<Self> {
        unsafe { mem::transmute(src) }
    }

    /// Creates an unsigned integer from a byte slice.
    pub fn from_slice(slice: &[u8]) -> Result<&Self, InvalidInteger> {
        Self::check_slice(slice)?;
        Ok(unsafe { Self::from_slice_unchecked(slice) })
    }

    /// Creates a boxed unsigned from a boxed slice.
    pub fn from_box(src: Box<[u8]>) -> Result<Box<Self>, InvalidInteger> {
        Self::check_slice(src.as_ref())?;
        Ok(unsafe { Self::from_box_unchecked(src) })
    }

    /// Returns a bytes slice with the raw content.
    pub fn as_slice(&self) -> &[u8] {
        self.0.as_ref()
    }

    /// Converts the unsigned to a signed integer.
    pub fn as_integer(&self) -> &Integer {
        unsafe { Integer::from_slice_unchecked(self.as_slice()) }
    }

    /// Returns whether the number is zero.
    pub fn is_zero(&self) -> bool {
        matches!(
            (self.0.first().copied(), self.0.get(1).copied()),
            (Some(0), None)
        )
    }
}


/// # Decoding
impl Unsigned {
    /// Decodes the next value as an unsigned integer.
    ///
    /// This requires the next value in `cons` to be a primitive value with
    /// tag `INTEGER` that contains a correctly encoded unsigned integer.
    pub fn take_from<M: Mode, R: io::BufRead>(
        cons: &mut Constructed<M, R>
    ) -> Result<Box<Self>, decode::Error> {
        Self::from_primitive(
            cons.next_primitive_with(Tag::INTEGER)?
        )
    }

    /// Decodes the next value as an unsigned integer, borrowing the content.
    ///
    /// This requires the next value in `cons` to be a primitive value with
    /// tag `INTEGER` that contains a correctly encoded unsigned integer.
    pub fn take_from_borrowed<'s, M: Mode>(
        cons: &mut Constructed<M, &'s [u8]>
    ) -> Result<&'s Self, decode::Error> {
        Self::from_primitive_borrowed(
            cons.next_primitive_with(Tag::INTEGER)?
        )
    }

    /// Creates an integer from the content of a primitive value.
    pub fn from_primitive<M, R: io::BufRead>(
        mut prim: Primitive<M, R>,
    ) -> Result<Box<Self>, decode::Error> {
        let len = usize::try_from(prim.remaining()).map_err(|_| {
            prim.err_at_start(OverflowError(()))
        })?;
        Self::from_box(prim.read_exact_into_box(len)?).map_err(|err| {
            prim.err_at_start(err)
        })
    }

    /// Creates an integer from the content of a primitive value.
    pub fn from_primitive_borrowed<'s, M>(
        mut prim: Primitive<M, &'s [u8]>,
    ) -> Result<&'s Self, decode::Error> {
        let len = usize::try_from(prim.remaining()).map_err(|_| {
            prim.err_at_start(OverflowError(()))
        })?;
        Self::from_slice(prim.read_exact_borrowed(len)?).map_err(|err| {
            prim.err_at_start(err)
        })
    }
}


//--- AsRef

impl AsRef<Integer> for Unsigned {
    fn as_ref(&self) -> &Integer {
        self.as_integer()
    }
}

impl AsRef<[u8]> for Unsigned {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}


//--- PartialEq and Eq

impl PartialEq for Unsigned {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl PartialEq<Integer> for Unsigned {
    fn eq(&self, other: &Integer) -> bool {
        self.0.eq(&other.0)
    }
}

impl Eq for Unsigned { }


//--- PartialOrd and Ord

impl PartialOrd for Unsigned {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<Integer> for Unsigned {
    fn partial_cmp(&self, other: &Integer) -> Option<cmp::Ordering> {
        Some(self.as_integer().cmp(other))
    }
}

impl Ord for Unsigned {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_integer().cmp(other.as_integer())
    }
}


//--- Hash

impl hash::Hash for Unsigned {
    fn hash<H: hash::Hasher>(&self, h: &mut H) {
        self.0.hash(h)
    }
}


//--- PrimitiveContent

impl<M> PrimitiveContent<M> for &'_ Unsigned {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(self) -> Length {
        self.as_slice().len().into()
    }

    fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(self.as_slice())
    }
}

impl<M> PrimitiveContent<M> for &'_ Box<Unsigned> {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(self) -> Length {
        self.as_slice().len().into()
    }

    fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(self.as_slice())
    }
}

impl<M> PrimitiveContent<M> for &'_ Arc<Unsigned> {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(self) -> Length {
        self.as_slice().len().into()
    }

    fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(self.as_slice())
    }
}


//------------ UnsignedArray -------------------------------------------------

/// A BER encoded unsigned integer backed by a byte array.
///
/// This is a fixed length version of the variable-sized [`Unsigned`] type,
/// essentially a big-ending unsigned integer of length `N`. The content is
/// right-aligned within the byte array so as to represent a big-endian
/// signed integer of size `N`. It does not contain the possibly necessary
/// padding zero but uses the full bit space of the `N` bytes and adds the
/// zero if necessary when encoding the value.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct UnsignedArray<const N: usize>([u8; N]);

impl<const N: usize> UnsignedArray<N> {
    /// Creates a new value from a byte array.
    //
    //  Make sure all values are created through this function which checks
    //  that N > 0 at compile time.
    pub fn from_array(array: [u8; N]) -> Self {
        let () = const { assert!(N > 0) };
        Self(array)
    }

    /// Returns the underlying byte array.
    pub fn to_array(self) -> [u8; N] {
        self.0
    }

    /// Returns a bytes slice with the raw octets.
    ///
    /// The slice will contain the full content, i.e., it will be of length
    /// `N`.
    pub fn as_slice(&self) -> &[u8] {
        self.0.as_ref()
    }

    /// Returns a bytes slice with the encoded value.
    ///
    /// The first component of the returned value is whether a zero value
    /// needs to be added before the second component.
    pub fn as_encoded_slice(&self) -> (bool, &[u8]) {
        let mut slice = self.as_slice();
        while let Some((&first, tail)) = slice.split_first() {
            if first != 0x00 {
                return (first & 0x80 != 0, slice)
            }
            slice = tail; 
        }
        (false, b"\x00")
    }
}

/// # Decoding
impl<const N: usize> UnsignedArray<N> {
    /// Decodes the next value as an unsigned integer.
    ///
    /// This requires the next value in `cons` to be a primitive value with
    /// tag `INTEGER` that contains a correctly encoded unsigned integer that
    /// fits into `N` bytes.
    pub fn take_from<M: Mode, R: io::BufRead>(
        cons: &mut Constructed<M, R>
    ) -> Result<Self, decode::Error> {
        Self::from_primitive(
            cons.next_primitive_with(Tag::INTEGER)?
        )
    }

    /// Creates an integer from the content of a primitive value.
    pub fn from_primitive<M, R: io::BufRead>(
        mut prim: Primitive<M, R>,
    ) -> Result<Self, decode::Error> {
        Self::from_primitive_ref(&mut prim)
    }

    /// Creates an integer from content of a primitive value (legacy version).
    ///
    /// This function is identical to [`from_primitive`][Self::from_primitive]
    /// but takes a mut ref of the primitive. It exists solely for
    /// compatibility with existing code and will be removed.
    pub(super) fn from_primitive_ref<M, R: io::BufRead>(
        prim: &mut Primitive<M, R>,
    ) -> Result<Self, decode::Error> {
        // Read the first octet to see if it is zero and needs to be skipped.
        let first = prim.read_u8()?;

        // First musn’t have bit 8 set to be unsigned
        if first & 0x80 != 0 {
            return Err(prim.err_at_start(OverflowError(())));
        }

        // If that was it, return.
        if prim.remaining().is_zero() {
            let mut res = [0u8; N];
            // Safety: N is always > 0
            #[allow(clippy::indexing_slicing)] {
                res[N - 1] = first;
            }
            return Ok(Self::from_array(res))
        }

        // Now determine the start position of what’s left in our byte array.
        let start = usize::try_from(prim.remaining()).ok().and_then(|len| {
            N.checked_sub(len)
        }).ok_or_else(|| prim.err_at_start(OverflowError(())))?;
        if start == N {
            return Err(prim.err_at_start(OverflowError(())))
        }

        // If the first byte wasn’t a padding 0, we need to have space for it.
        if first != 0 && start == 0 {
            return Err(prim.err_at_start(OverflowError(())))
        }

        // Read the rest.
        let mut res = [0u8; N];
        let (_, tail) = res.as_mut_slice().split_at_mut(start);
        prim.read_exact(tail)?;

        // If first was zero, the first octet of the tail must have the most
        // significant bit set. Otherwise, we need to set it as the last
        // octet of head.
        if first == 0 {
            // Safety: tail can’t be empty since start is smaller than N.
            #[allow(clippy::indexing_slicing)]
            if tail[0] & 0x80 == 0 {
                return Err(prim.err_at_start(InvalidInteger(())));
            }
        }
        else {
            // Safety: start can’t be zero if first != 0.
            #[allow(clippy::indexing_slicing)] {
                res[start - 1] = first
            }
        }

        Ok(Self::from_array(res))
    }
}


//--- Default

impl<const N: usize> Default for UnsignedArray<N> {
    fn default() -> Self {
        Self::from_array([0u8; N])
    }
}

//--- PrimitiveContent

impl<const N: usize, M> PrimitiveContent<M> for UnsignedArray<N> {
    const TAG: Tag = Tag::INTEGER;

    fn encoded_len(self) -> Length {
        match self.as_encoded_slice() {
            (true, slice) => (slice.len() as u64 + 1).into(),
            (false, slice) => slice.len().into(),
        }
    }

    fn write_encoded<T: Target>(
        self, target: &mut T
    ) -> Result<(), T::Error> {
        let (zero, slice) = self.as_encoded_slice();
        if zero {
            target.write_all(&[0])?;
        }
        target.write_all(slice)
    }
}


//------------ Unsigned Built-in Integers ------------------------------------

macro_rules! unsigned_builtin {
    ( $int:ident ) => {
        unsigned_builtin!{$int, { mem::size_of::<$int>() }}
    };

    ( $int:ident, $len:expr ) => {
        impl From<UnsignedArray<$len>> for $int {
            fn from(src: UnsignedArray<$len>) -> Self {
                Self::from_be_bytes(src.0)
            }
        }

        impl From<$int> for UnsignedArray<$len> {
            fn from(src: $int) -> Self {
                Self::from_array(src.to_be_bytes())
            }
        }

        impl<M> FromPrimitive<M> for $int {
            const TAG: Tag = Tag::INTEGER;

            fn from_primitive<R: io::BufRead>(
                prim: Primitive<M, R>
            ) -> Result<Self, decode::Error> {
                Ok(UnsignedArray::from_primitive(prim)?.into())
            }
        }

        impl<M> PrimitiveContent<M> for $int {
            const TAG: Tag = Tag::INTEGER;

            fn encoded_len(self) -> Length {
                PrimitiveContent::<M>::encoded_len(
                    UnsignedArray::from(self)
                )
            }

            fn write_encoded<T: Target>(
                self, target: &mut T
            ) -> Result<(), T::Error> {
                PrimitiveContent::<M>::write_encoded(
                    UnsignedArray::from(self), target
                )
            }
        }
    };
}

unsigned_builtin!(u8);
unsigned_builtin!(u16);
unsigned_builtin!(u32);
unsigned_builtin!(u64);
unsigned_builtin!(u128);


//============ Error Types ===================================================

//------------ InvalidInteger ------------------------------------------------

/// A octets slice does not contain a validly encoded integer.
#[derive(Clone, Copy, Debug)]
pub struct InvalidInteger(());

impl fmt::Display for InvalidInteger {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "invalid integer")
    }
}

impl error::Error for InvalidInteger { }


//------------ OverflowError -------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub struct OverflowError(());

impl fmt::Display for OverflowError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "integer out of range")
    }
}

impl error::Error for OverflowError { }


//============ Tests =========================================================

// XXX There should be more tests here. Especially for the Ord impl.

#[cfg(test)]
mod test {
    use std::{cmp, fmt};
    use crate::decode::Primitive;
    use crate::encode::PrimitiveContent;
    use crate::mode::Ber;
    use super::*;

    fn cycle<T>(value: T, encoded: &[u8])
    where
        T: FromPrimitive<Ber> + PrimitiveContent<Ber>
            + fmt::Debug + cmp::PartialEq,
    {
        eprintln!("Cycling {value:?} through {encoded:?}");
        let decoded = match Primitive::decode_slice_ber(
            encoded, |prim| T::from_primitive(prim)
        ) {
            Ok(decoded) => decoded,
            Err(err) => {
                panic!("failed decoding {encoded:?} as {value:?}: {err}");
            }
        };
        if decoded != value {
            panic!(
                "failed decoding {encoded:?} as {value:?}: got {decoded:?}"
            );
        }
        let written = value.encode_to_vec();
        if written.as_slice() != encoded {
            panic!(
                "failed encoding {value:?} as {encoded:?}: got {written:?}"
            );
        }
    }

    fn fail_decode<T>(encoded: &[u8])
    where T: FromPrimitive<Ber> + fmt::Debug + cmp::PartialEq,
    {
        if let Ok(some) = Primitive::decode_slice_ber(
            encoded, |prim| T::from_primitive(prim)
        ) {
            panic!("successfully decoded {encoded:?} as {some:?}");
        }
    }

    #[test]
    fn decode_signed_builtins() {
        cycle(0i8, b"\x00");
        cycle(66i8, b"\x42");
        cycle(127i8, b"\x7F");
        cycle(-1i8, b"\xFF");
        cycle(-62i8, b"\xC2");
        cycle(-128i8, b"\x80");
        fail_decode::<i8>(b"\x00\x00");
        fail_decode::<i8>(b"\x00\x12");
        fail_decode::<i8>(b"\x12\x34");
        fail_decode::<i8>(b"\xFF\x00");
        fail_decode::<i8>(b"\xFF\x80");
        fail_decode::<i8>(b"\xFF\xFF");

        cycle(0i16, b"\x00");
        cycle(66i16, b"\x42");
        cycle(17142i16, b"\x42\xF6");
        cycle(32_767i16, b"\x7F\xFF");
        cycle(-1i16, b"\xFF");
        cycle(-62i16, b"\xC2");
        cycle(-15837i16, b"\xC2\x23");
        cycle(-32_768i16, b"\x80\x00");
        fail_decode::<i16>(b"\x00\x00");
        fail_decode::<i16>(b"\x00\x12");
        fail_decode::<i16>(b"\xFF\x80");
        fail_decode::<i16>(b"\xFF\xFF");
        fail_decode::<i8>(b"\x12\x34\x56");
    }

    #[test]
    fn decode_unsigned_builtins() {
        cycle(0u8, b"\x00");
        cycle(0x42u8, b"\x42");
        cycle(0x7fu8, b"\x7f");
        cycle(0x80u8, b"\x00\x80");
        cycle(0xC4u8, b"\x00\xC4");
        cycle(0xFFu8, b"\x00\xFF");
        fail_decode::<u8>(b"\xC4");
        fail_decode::<u8>(b"\xFF");
        fail_decode::<i8>(b"\x00\x00");
        fail_decode::<i8>(b"\x00\x12");
        fail_decode::<i8>(b"\x12\x34");
        fail_decode::<i8>(b"\xFF\x00");
        fail_decode::<i8>(b"\xFF\x80");
        fail_decode::<i8>(b"\xFF\xFF");

        cycle(0u16, b"\x00");
        cycle(0x42u16, b"\x42");
        cycle(0x7fu16, b"\x7f");
        cycle(0x80u16, b"\x00\x80");
        cycle(0xC4u16, b"\x00\xC4");
        cycle(0xFFu16, b"\x00\xFF");
        cycle(0x1234u16, b"\x12\x34");
        cycle(0x7fffu16, b"\x7f\xff");
        cycle(0x8000u16, b"\x00\x80\x00");
        fail_decode::<u16>(b"\x00\x00");
        fail_decode::<u16>(b"\x00\x12");
        fail_decode::<u16>(b"\xFF\x80");
        fail_decode::<u16>(b"\xFF\xFF");
        fail_decode::<u8>(b"\x12\x34\x56");
    }
}

