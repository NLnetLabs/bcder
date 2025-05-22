//! PrimitiveContent and related types.
//!
//! This is an internal module. The relevant items are re-exported by the
//! parent.

use std::marker::PhantomData;
use crate::ident::Tag;
use crate::length::Length;
use super::target::{Target, infallible};
use super::values::{Values, total_len, write_header};


//------------ primitive -----------------------------------------------------

/// Encodes the give slice as a primitive value with the given tag.
pub fn primitive<'s, M: 's>(tag: Tag, data: &'s [u8]) -> impl Values<M> + 's {
    data.encode_as(tag)
}

//------------ PrimitiveContent ----------------------------------------------

/// A type that is encoded as a primitive value.
///
/// This trait should be implemented for types that use primitive encoding.
/// It defines, how the content octets of a single primitive value containing
/// a value of the type are to be created. As a consequence, these types
/// gain the [`encode`] and [`encode_as`] methods from their implementation
/// of this trait.
///
/// Note that the trait requires implementing types to be `Copy` to
/// avoid unnecessary lifetime parameters on the encoder type. For types that
/// aren’t `Copy`, `PrimitiveContent` should be implemented on a reference to
/// the type instead.
///
/// [`encode`]: #tymethod.encode
/// [`encode_as`]: #tymethod.encode_as
pub trait PrimitiveContent<M>: Copy {
    /// The natural tag of an encoded value of this type.
    const TAG: Tag;

    /// Returns the length of the encoded content of this type.
    fn encoded_len(self) -> Length;

    /// Writes the encoded content to a target.
    fn write_encoded<T: Target>(
        self,
        target: &mut T
    ) -> Result<(), T::Error>;


    //--- Provided methods

    /// Returns a value encoder for this content using the natural tag.
    ///
    /// This is identical to `self.encode_as(Self::TAG)`
    fn encode(self) -> Primitive<M, Self> {
        self.encode_as(Self::TAG)
    }

    /// Returns a value encoder for this content using the given tag.
    ///
    /// The returned value is a content encoder that produces a single
    /// primitive BER encoded value. The tag for this value is explicitely
    /// given via the `tag` argument.
    fn encode_as(self, tag: Tag) -> Primitive<M, Self> {
        Primitive::new(tag, self)
    }

    /// Writes the encoded content into a new vec.
    ///
    /// This is mostly just useful for testing.
    fn encode_to_vec(self) -> Vec<u8> {
        let mut res = Vec::new();
        infallible(self.write_encoded(&mut res));
        res
    }
}

//--- impl for built-in types
//
// See crate::int for the impls for the built-in integer types.


impl<M> PrimitiveContent<M> for () {
    const TAG: Tag = Tag::NULL;

    fn encoded_len(self) -> Length {
        Length::ZERO
    }

    fn write_encoded<T: Target>(
        self,
        _: &mut T
    ) -> Result<(), T::Error> {
        Ok(())
    }
}

impl<M> PrimitiveContent<M> for bool {
    const TAG: Tag = Tag::BOOLEAN;

    fn encoded_len(self) -> Length {
        Length::from_u64(1)
    }

    fn write_encoded<T: Target>(
        self,
        target: &mut T
    ) -> Result<(), T::Error> {
        if self {
            target.write_all(&[0xff])
        }
        else {
            target.write_all(&[0])
        }
    }
}

impl<M> PrimitiveContent<M> for &'_ [u8] {
    const TAG: Tag = Tag::OCTET_STRING;

    fn encoded_len(self) -> Length {
        self.len().into()
    }

    fn write_encoded<T: Target>(
        self,
        target: &mut T
    ) -> Result<(), T::Error> {
        target.write_all(self)
    }
}




//------------ Primitive -----------------------------------------------------

/// A value encoder for primitively encoded types.
///
/// This type is returned by [`PrimitiveContent::encode`] and
/// [`PrimitiveContent::encode_as`].
///
/// [`PrimitiveContent::encode`]: trait.PrimitiveContent.html#tymethod_encode
/// [`PrimitiveContent::encode_as`]: trait.PrimitiveContent.html#tymethod_encode_as
pub struct Primitive<M, P> {
    /// The tag of the value
    tag: Tag,

    /// The primitive content.
    prim: P,

    /// A marker for the mode.
    marker: PhantomData<M>,
}

impl<M, P> Primitive<M, P> {
    fn new(tag: Tag, prim: P) -> Self {
        Self { tag, prim, marker: PhantomData }
    }
}

impl<M, P: PrimitiveContent<M>> Values<M> for Primitive<M, P> {
    fn encoded_len(&self) -> Length {
        total_len(self.tag, self.prim.encoded_len())
    }

    fn write_encoded<T: Target>(
        &self,
        target: &mut T
    ) -> Result<(), T::Error> {
        write_header(target, self.tag, false, self.prim.encoded_len())?;
        self.prim.write_encoded(target)
    }
}

