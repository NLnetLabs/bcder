//! Everything related to the `Values` trait.
//!
//! This is an internal module. The relevant items are re-exported by the
//! parent.

use std::marker::PhantomData;
use crate::ident::{Ident, Tag};
use crate::length::{Length, LengthOctets};
use crate::mode::{BerCer, Mode};
use super::target::{Target, infallible};


//------------ Values --------------------------------------------------------

/// A type that is a value encoder.
///
/// Value encoders know how to encode themselves into a
/// sequence of BER encoded values. While you can impl this trait for your
/// type manually, in practice it is often easier to define a method called
/// `encode` and let it return some dedicated value encoder type constructed
/// from the types provided by this module.
///
/// A type implementing this trait should encodes itself into one or more
/// BER values. That is, the type becomes the content or part of the content
/// of a constructed value.
pub trait Values<M> {
    /// Returns the length of the encoded values for the given mode.
    fn encoded_len(&self) -> Length;

    /// Encodes the values in the given mode and writes them to `target`.
    fn write_encoded<T: Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error>;


    //--- Provided methods

    /// Converts the encoder into one with an explicit tag.
    ///
    /// For an explicite tag, the value is wrapped in a constructed value with
    /// the given tag.
    fn explicit(self, tag: Tag) -> Constructed<Self>
    where Self: Sized {
        Constructed::new(tag, self)
    }

    fn to_vec(&self) -> Vec<u8> {
        let mut target = Vec::new();
        infallible(self.write_encoded(&mut target));
        target
    }
}


//--- Blanket impls

impl<M, V: Values<M>> Values<M> for &'_ V {
    fn encoded_len(&self) -> Length {
        (*self).encoded_len()
    }

    fn write_encoded<T: Target>(
        &self,
        target: &mut T
    ) -> Result<(), T::Error> {
        (*self).write_encoded(target)
    }
}


//--- Impls for Tuples

/// Macro for implementing `Values` for tuples.
///
/// This macro implements `Values` for all tuples up to a certain degree.
/// It needs to be invoked as below. All the `Tx`s are the type parameters
/// of the elements the tuple, the numbers are the tuple element numbers.
/// The number need to be provided backwards ending in 0.
///
/// The `tuple` bit of the macro does the actual impl and invokes itself with
/// one less tuple element. The `write` bit below is to implement
/// `write_encoded` backwards (i.e., starting with the smallest number).
macro_rules! tupl_impl {
    // Termination: empty lists, do nothing.
    ( tuple > ) => { };

    // Impl values for the complete lists, then recurse to the lists without
    // their heads.
    ( tuple $t:ident $( $ttail:ident )* > $i:tt $( $itail:tt )* ) => {
        impl<M, $t: Values<M>, $( $ttail: Values<M> ),*> Values<M>
                for ($t, $( $ttail ),*) {
            fn encoded_len(&self) -> Length {
                self.$i.encoded_len()
                $(
                    + self.$itail.encoded_len()
                )*
            }

            fn write_encoded<T: Target>(
                &self,
                target: &mut T
            ) -> Result<(), T::Error> {
                tupl_impl!( write self, target, $i $( $itail )* );
                Ok(())
            }
        }

        tupl_impl!(
             tuple $($ttail)* > $($itail)*
        );
    };

    // Termination: empty lists, do nothing.
    ( write $self:expr, $target:expr, ) => { };

    // Write all elements of tuple $self in mode $mode to $target in order.
    ( write $self:expr, $target:expr, $i:tt $($itail:tt)*) => {
        tupl_impl!( write $self, $target, $($itail)* );
        $self.$i.write_encoded($target)?
    }
}

// The standard library implements things for tuples up to twelve elements,
// so we do the same.
tupl_impl!(
    tuple T11 T10 T9 T8 T7 T6 T5 T4 T3 T2 T1 T0 > 11 10 9 8 7 6 5 4 3 2 1 0
);


//--- Impl for Option

/// Encoding of an optional value.
///
/// This implementation encodes `None` as nothing, i.e., as an OPTIONAL
/// in ASN.1 parlance.
impl<M, V: Values<M>> Values<M> for Option<V> {
    fn encoded_len(&self) -> Length {
        match self {
            Some(v) => v.encoded_len(),
            None => Length::ZERO,
        }
    }

    fn write_encoded<T: Target>(
        &self,
        target: &mut T
    ) -> Result<(), T::Error> {
        match self {
            Some(v) => v.write_encoded(target),
            None => Ok(())
        }
    }
}


//--- Impl for slice and Vec

impl<M, V: Values<M>> Values<M> for [V] {
    fn encoded_len(&self) -> Length {
        self.iter().fold(Length::ZERO, |len, v| len + v.encoded_len())
    }

    fn write_encoded<T: Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        self.iter().try_for_each(|v| v.write_encoded(target))
    }
}

impl<M, V: Values<M>> Values<M> for Vec<V> {
    fn encoded_len(&self) -> Length {
        self.as_slice().encoded_len()
    }

    fn write_encoded<T: Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        self.as_slice().write_encoded(target)
    }
}


//------------ Constructed ---------------------------------------------------

/// A value encoder for a single constructed value.
///
/// The encoder uses the definite length form for BER and DER and the
/// indefinite length form for CER.
pub struct Constructed<V> {
    /// The tag of the value.
    tag: Tag,

    /// A value encoder for the content of the value.
    inner: V,
}

impl<V> Constructed<V> {
    /// Creates a new constructed value encoder from a tag and content.
    ///
    /// The returned value will encode as a single constructed value with
    /// the given tag and whatever `inner` encodeds to as its content.
    pub fn new(tag: Tag, inner: V) -> Self {
        Constructed { tag, inner }
    }
}

impl<M: Mode, V: Values<M>> Values<M> for Constructed<V> {
    fn encoded_len(&self) -> Length {
        if M::IS_CER {
            total_indefinite_len(self.tag, self.inner.encoded_len())
        }
        else {
            total_len(self.tag, self.inner.encoded_len())
        }
    }

    fn write_encoded<T: Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        if M::IS_CER {
            write_indefinite_header(target, self.tag)?;
            self.inner.write_encoded(target)?;
            write_end_of_contents(target)
        }
        else {
            write_header(target, self.tag, true, self.inner.encoded_len())?;
            self.inner.write_encoded(target)
        }
    }
}


//------------ IndefiniteConstructed -----------------------------------------

/// A value encoder for a indefinite length form constructed value.
///
/// This type can only be used when encoding in BER or CER modes.
pub struct IndefiniteConstructed<V> {
    /// The tag octets of the value.
    tag: Tag,

    /// A value encoder for the content of the value.
    inner: V,
}

impl<V> IndefiniteConstructed<V> {
    /// Creates a new value encoder from a tag and content.
    ///
    /// The returned value will encode as a single indefinite length form
    /// constructed value with the given tag and whatever `inner` encodeds
    /// to as its content.
    pub fn new(tag: Tag, inner: V) -> Self {
        Self { tag, inner }
    }
}

impl<M: BerCer, V: Values<M>> Values<M> for IndefiniteConstructed<V> {
    fn encoded_len(&self) -> Length {
        total_indefinite_len(self.tag, self.inner.encoded_len())
    }

    fn write_encoded<T: Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        write_indefinite_header(target, self.tag)?;
        self.inner.write_encoded(target)?;
        write_end_of_contents(target)
    }
}


//------------ Choice2 -------------------------------------------------------

/// A value encoder for a two-variant enum.
///
/// Instead of implementing `Values` for an enum manually, you can just
/// define a method `encode` that returns a value of this type.
pub enum Choice2<L, R> {
    /// The first choice.
    One(L),

    /// The second choice.
    Two(R)
}

impl<M, L: Values<M>, R: Values<M>> Values<M> for Choice2<L, R> {
    fn encoded_len(&self) -> Length {
        match self {
            Choice2::One(inner) => inner.encoded_len(),
            Choice2::Two(inner) => inner.encoded_len(),
        }
    }

    fn write_encoded<T: Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        match self {
            Choice2::One(inner) => inner.write_encoded(target),
            Choice2::Two(inner) => inner.write_encoded(target),
        }
    }
}


//------------ Choice3 -------------------------------------------------------

/// A value encoder for a three-variant enum.
///
/// Instead of implementing `Values` for an enum manually, you can just
/// define a method `encode` that returns a value of this type.
pub enum Choice3<L, C, R> {
    /// The first choice.
    One(L),

    /// The second choice.
    Two(C),

    /// The third choice.
    Three(R)
}

impl<M, L, C, R> Values<M> for Choice3<L, C, R>
where L: Values<M>, C: Values<M>, R: Values<M> {
    fn encoded_len(&self) -> Length {
        match self {
            Choice3::One(inner) => inner.encoded_len(),
            Choice3::Two(inner) => inner.encoded_len(),
            Choice3::Three(inner) => inner.encoded_len(),
        }
    }

    fn write_encoded<T: Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        match self {
            Choice3::One(inner) => inner.write_encoded(target),
            Choice3::Two(inner) => inner.write_encoded(target),
            Choice3::Three(inner) => inner.write_encoded(target),
        }
    }
}


//--------------- Iter -------------------------------------------------------

/// A wrapper for an iterator of values.
///
/// The type wraps something that impl `IntoIterator`. It needs to be
/// `Clone`, because we need to be able to restart iterating at the beginning.
///
/// The wrapper is needed because a blanket impl on any iterator type is
/// currently not possible.
pub struct Iter<I>(pub I);

impl<I> Iter<I> {
    /// Creates a new iterator encoder atop `iter`.
    pub fn new(iter: I) -> Self {
        Iter(iter)
    }
}

/// Wraps an iterator over value encoders into a value encoder.
pub fn iter<I>(iter: I) -> Iter<I> {
    Iter::new(iter)
}


//--- IntoIterator

impl<I: IntoIterator> IntoIterator for Iter<I> {
    type Item = <I as IntoIterator>::Item;
    type IntoIter = <I as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<I: Clone + IntoIterator> IntoIterator for &'_ Iter<I> {
    type Item = <I as IntoIterator>::Item;
    type IntoIter = <I as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.clone().into_iter()
    }
}


//--- Values

impl<M, I> Values<M> for Iter<I>
where
    I: Clone + IntoIterator,
    <I as IntoIterator>::Item: Values<M>
{
    fn encoded_len(&self) -> Length {
        self.into_iter().fold(
            Length::ZERO,
            |len, item| len + item.encoded_len()
        )
    }

    fn write_encoded<T: Target>(
        &self, target: &mut T
    ) -> Result<(), T::Error> {
        self.into_iter().try_for_each(|item| item.write_encoded(target))
    }
}


//------------ EncodeSlice ---------------------------------------------------

/// A wrapper for a slice of encodable values.
///
/// A value of this type will take something that can provide a reference to
/// a slice of some value and a closure that converts the values of the slice
/// into something encodable.
//
//  We need the extra type arguments here already or else they are
//  unconstrained in the Values impl.
pub struct EncodeSlice<S, F, U, V>
where
    S: AsRef<[U]>,
    F: Fn(&U) -> V
{
    /// The slice value.
    slice: S,

    /// The converter function.
    op: F,

    /// A markers for extra type arguments.
    marker: PhantomData<(U, V)>,
}

impl<S, F, U, V> EncodeSlice<S, F, U, V>
where
    S: AsRef<[U]>,
    F: Fn(&U) -> V
{
    /// Creates a new wrapper for a given value and closure.
    pub fn new(slice: S, op: F) -> Self {
        Self { slice, op, marker: PhantomData, }
    }
}

/// Creates an encodable wrapper around a slice.
///
/// The function takes a value of a type that can be converted into a slice of
/// some type and a function that converts references to slice elements into
/// some encoder.
pub fn encode_slice<S, F, U, V>(slice: S, op: F) -> EncodeSlice<S, F, U, V>
where
    S: AsRef<[U]>,
    F: Fn(&U) -> V
{
    EncodeSlice::new(slice, op)
}


//--- Values

impl<M, S, F, U, V> Values<M> for EncodeSlice<S, F, U, V>
where
    S: AsRef<[U]>,
    F: Fn(&U) -> V,
    V: Values<M>
{
    fn encoded_len(&self) -> Length {
        self.slice.as_ref().iter().fold(Length::ZERO, |len, v| {
            len + (self.op)(v).encoded_len()
        })
    }

    fn write_encoded<T: Target>(
        &self,
        target: &mut T
    ) -> Result<(), T::Error> {
        self.slice.as_ref().iter().try_for_each(|v|
            (self.op)(v).write_encoded(target)
        )
    }
}


//------------ Nothing -------------------------------------------------------

/// An encoder for nothing.
///
/// Unsurprisingly, this encodes as zero octets of content. It can be useful
/// for writing an encoder for an enum where some of the variants shouldn’t
/// result in content at all.
pub struct Nothing;

impl<M> Values<M> for Nothing {
    fn encoded_len(&self) -> Length {
        Length::ZERO
    }

    fn write_encoded<T: Target>(
        &self, _target: &mut T
    ) -> Result<(), T::Error> {
        Ok(())
    }
}


//============ Standard Functions ============================================

/// Returns a value encoder for a SEQUENCE containing `inner`.
pub fn sequence<M: Mode, V: Values<M>>(inner: V) -> impl Values<M> {
    Constructed::new(Tag::SEQUENCE, inner)
}

/// Returns a value encoder for a SEQUENCE with the given tag.
///
/// This is identical to `Constructed::new(tag, inner)`. It merely provides a
/// more memorable name.
pub fn sequence_as<M: Mode, V: Values<M>>(
    tag: Tag, inner: V
) -> impl Values<M> {
    Constructed::new(tag, inner)
}

/// Returns a value encoder for a SET containing `inner`.
pub fn set<M: Mode, V: Values<M>>(inner: V) -> impl Values<M> {
    Constructed::new(Tag::SET, inner)
}

/// Returns a value encoder for a SET with the given tag.
///
/// This is identical to `Constructed::new(tag, inner)`. It merely provides a
/// more memorable name.
pub fn set_as<M: Mode, V: Values<M>>(tag: Tag, inner: V) -> impl Values<M> {
    Constructed::new(tag, inner)
}

/// Returns the length for a structure based on the tag and content length.
///
/// This is necessary because the length octets have a different length
/// depending on the content length.
pub fn total_len(tag: Tag, content_l: Length) -> Length {
    Ident::from_tag(tag, false).encoded_len()
        + LengthOctets::new(Some(content_l)).encoded_len()
        + content_l
}

/// Returns the length of a indefinite-form constructed.
///
/// This includes the end-of-contents octets.
pub fn total_indefinite_len(tag: Tag, content_l: Length) -> Length {
    Ident::from_tag(tag, false).encoded_len()
        + LengthOctets::new(None).encoded_len()
        + content_l
        + 2 // End-of-contents is two bytes.
}

/// Writes the header for a value.
///
/// The header in the sense of this function is the identifier octets and the
/// length octets.
pub fn write_header<T: Target>(
    target: &mut T,
    tag: Tag,
    constructed: bool,
    content_length: Length, 
) -> Result<(), T::Error> {
    Ident::from_tag(tag, constructed).write_encoded(target)?;
    LengthOctets::new(Some(content_length)).write_encoded(target)?;
    Ok(())
}

/// Writes the header for an indefinite-length constructed.
pub fn write_indefinite_header<T: Target>(
    target: &mut T,
    tag: Tag,
) -> Result<(), T::Error> {
    Ident::from_tag(tag, true).write_encoded(target)?;
    LengthOctets::new(None).write_encoded(target)?;
    Ok(())
}

/// Writes the end-of-contents octets.
pub fn write_end_of_contents<T: Target>(
    target: &mut T,
) -> Result<(), T::Error> {
    target.write_all(b"\0\0")
}

