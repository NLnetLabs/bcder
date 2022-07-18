//! Everything related to the `Values` trait.
//!
//! This is an internal module. Its public types are re-exported by the
//! parent.

use std::io;
use std::marker::PhantomData;
use crate::captured::Captured;
use crate::length::Length;
use crate::mode::Mode;
use crate::tag::Tag;


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
pub trait Values {
    /// Returns the length of the encoded values for the given mode.
    fn encoded_len(&self, mode: Mode) -> usize;

    /// Encodes the values in the given mode and writes them to `target`.
    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error>;


    //--- Provided methods

    /// Converts the encoder into one with an explicit tag.
    fn explicit(self, tag: Tag) -> Constructed<Self>
    where Self: Sized {
        Constructed::new(tag, self)
    }

    /// Captures the encoded values in the given mode.
    fn to_captured(&self, mode: Mode) -> Captured {
        let mut target = Vec::new();
        self.write_encoded(mode, &mut target).unwrap();
        Captured::new(target.into(), mode, Default::default())
    }
}


//--- Blanket impls

impl<'a, T: Values> Values for &'a T {
    fn encoded_len(&self, mode: Mode) -> usize {
        (*self).encoded_len(mode)
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        (*self).write_encoded(mode, target)
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
        impl<$t: Values, $( $ttail: Values ),*> Values
                for ($t, $( $ttail ),*) {
            fn encoded_len(&self, mode: Mode) -> usize {
                self.$i.encoded_len(mode)
                $(
                    + self.$itail.encoded_len(mode)
                )*
            }

            fn write_encoded<W: io::Write>(
                &self,
                mode: Mode,
                target: &mut W
            ) -> Result<(), io::Error> {
                tupl_impl!( write self, mode, target, $i $( $itail )* );
                Ok(())
            }
        }

        tupl_impl!(
             tuple $($ttail)* > $($itail)*
        );
    };

    // Termination: empty lists, do nothing.
    ( write $self:expr, $mode:expr, $target:expr, ) => { };

    // Write all elements of tuple $self in mode $mode to $target in order.
    ( write $self:expr, $mode:expr, $target:expr, $i:tt $($itail:tt)*) => {
        tupl_impl!( write $self, $mode, $target, $($itail)* );
        $self.$i.write_encoded($mode, $target)?
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
impl<V: Values> Values for Option<V> {
    fn encoded_len(&self, mode: Mode) -> usize {
        match self {
            Some(v) => v.encoded_len(mode),
            None => 0
        }
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        match self {
            Some(v) => v.write_encoded(mode, target),
            None => Ok(())
        }
    }
}


//--- Impl for slice and Vec

impl<V: Values> Values for [V] {
    fn encoded_len(&self, mode: Mode) -> usize {
        self.iter().map(|v| v.encoded_len(mode)).sum()
    }

    fn write_encoded<W: io::Write>(&self, mode: Mode, target: &mut W)
        -> Result<(), io::Error>
    {
        for i in self {
            i.write_encoded(mode, target)?;
        };
        Ok(())
    }
}

impl<V: Values> Values for Vec<V> {
    fn encoded_len(&self, mode: Mode) -> usize {
        self.iter().map(|v| v.encoded_len(mode)).sum()
    }

    fn write_encoded<W: io::Write>(&self, mode: Mode, target: &mut W)
        -> Result<(), io::Error>
    {
        for i in self {
            i.write_encoded(mode, target)?;
        };
        Ok(())
    }
}


//------------ Constructed ---------------------------------------------------

/// A value encoder for a single constructed value.
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

impl<V: Values> Values for Constructed<V> {
    fn encoded_len(&self, mode: Mode) -> usize {
        let len = self.inner.encoded_len(mode);
        let len = len + match mode {
            Mode::Ber | Mode::Der => {
                Length::Definite(len).encoded_len()
            }
            Mode::Cer => {
                Length::Indefinite.encoded_len()
                + EndOfValue.encoded_len(mode)
            }
        };
        self.tag.encoded_len() + len
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        self.tag.write_encoded(true, target)?;
        match mode {
            Mode::Ber | Mode::Der => {
                Length::Definite(self.inner.encoded_len(mode))
                    .write_encoded(target)?;
                self.inner.write_encoded(mode, target)
            }
            Mode::Cer => {
                Length::Indefinite.write_encoded(target)?;
                self.inner.write_encoded(mode, target)?;
                EndOfValue.write_encoded(mode, target)
            }
        }
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

impl<L: Values, R: Values> Values for Choice2<L, R> {
    fn encoded_len(&self, mode: Mode) -> usize {
        match *self {
            Choice2::One(ref inner) => inner.encoded_len(mode),
            Choice2::Two(ref inner) => inner.encoded_len(mode),
        }
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        match *self {
            Choice2::One(ref inner) => inner.write_encoded(mode, target),
            Choice2::Two(ref inner) => inner.write_encoded(mode, target),
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

impl<L: Values, C: Values, R: Values> Values for Choice3<L, C, R> {
    fn encoded_len(&self, mode: Mode) -> usize {
        match *self {
            Choice3::One(ref inner) => inner.encoded_len(mode),
            Choice3::Two(ref inner) => inner.encoded_len(mode),
            Choice3::Three(ref inner) => inner.encoded_len(mode),
        }
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        match *self {
            Choice3::One(ref inner) => inner.write_encoded(mode, target),
            Choice3::Two(ref inner) => inner.write_encoded(mode, target),
            Choice3::Three(ref inner) => inner.write_encoded(mode, target),
        }
    }
}


//--------------- Iter -------------------------------------------------------

/// A wrapper for an iterator of values.
///
/// The wrapper is needed because a blanket impl on any iterator type is
/// currently not possible.
///
/// Note that `T` needs to be clone because we need to be able to restart
/// iterating at the beginning.
pub struct Iter<T>(pub T);

impl<T> Iter<T> {
    /// Creates a new iterator encoder atop `iter`.
    pub fn new(iter: T) -> Self {
        Iter(iter)
    }
}

/// Wraps an iterator over value encoders into a value encoder.
pub fn iter<T>(iter: T) -> Iter<T> {
    Iter::new(iter)
}


//--- IntoIterator

impl<T: IntoIterator> IntoIterator for Iter<T> {
    type Item = <T as IntoIterator>::Item;
    type IntoIter = <T as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T: Clone + IntoIterator> IntoIterator for &'a Iter<T> {
    type Item = <T as IntoIterator>::Item;
    type IntoIter = <T as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.clone().into_iter()
    }
}


//--- Values

impl<T> Values for Iter<T>
where T: Clone + IntoIterator, <T as IntoIterator>::Item: Values {
    fn encoded_len(&self, mode: Mode) -> usize {
        self.into_iter().map(|item| item.encoded_len(mode)).sum()
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        self.into_iter().try_for_each(|item| item.write_encoded(mode, target))
    }
}


//------------ Slice ---------------------------------------------------------

/// A wrapper for a slice of encodable values.
///
/// A value of this type will take something that can provide a reference to
/// a slice of some value and a closure that converts the values of the slice
/// into something encodable.
pub struct Slice<T, F, U, V>
where T: AsRef<[U]>, F: Fn(&U) -> V {
    /// The slice value.
    value: T,

    /// The converter function.
    f: F,

    /// A markers for extra type arguments.
    marker: PhantomData<(U, V)>,
}

impl<T, F, U, V> Slice<T, F, U, V>
where T: AsRef<[U]>, F: Fn(&U) -> V {
    /// Creates a new wrapper for a given value and closure.
    pub fn new(value: T, f: F) -> Self {
        Slice { value, f, marker: PhantomData }
    }
}

/// Creates an encodable wrapper around a slice.
///
/// The function takes a value of a type that can be converted into a slice of
/// some type and a function that converts references to slice elements into
/// some encoder.
pub fn slice<T, F, U, V>(value: T, f: F) -> Slice<T, F, U, V>
where T: AsRef<[U]>, F: Fn(&U) -> V {
    Slice::new(value, f)
}


//--- Values

impl<T, F, U, V> Values for Slice<T, F, U, V>
where T: AsRef<[U]>, F: Fn(&U) -> V, V: Values {
    fn encoded_len(&self, mode: Mode) -> usize {
        self.value.as_ref().iter().map(|v| (self.f)(v).encoded_len(mode)).sum()
    }

    fn write_encoded<W: io::Write>(
        &self,
        mode: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        self.value.as_ref().iter().try_for_each(|v|
            (self.f)(v).write_encoded(mode, target)
        )
    }
}


//------------ Nothing -------------------------------------------------------

/// A encoder for nothing.
///
/// Unsurprisingly, this encodes as zero octets of content. It can be useful
/// for writing an encoder for an enum where some of the variants shouldn’t
/// result in content at all.
pub struct Nothing;

impl Values for Nothing {
    fn encoded_len(&self, _mode: Mode) -> usize {
        0
    }

    fn write_encoded<W: io::Write>(
        &self,
        _mode: Mode,
        _target: &mut W
    ) -> Result<(), io::Error> {
        Ok(())
    }
}


//============ Standard Functions ============================================

/// Returns a value encoder for a SEQUENCE containing `inner`.
pub fn sequence<V: Values>(inner: V) -> impl Values {
    Constructed::new(Tag::SEQUENCE, inner)
}

/// Returns a value encoder for a SEQUENCE with the given tag.
///
/// This is identical to `Constructed::new(tag, inner)`. It merely provides a
/// more memorial name.
pub fn sequence_as<V: Values>(tag: Tag, inner: V) -> impl Values {
    Constructed::new(tag, inner)
}

/// Returns a value encoder for a SET containing `inner`.
pub fn set<V: Values>(inner: V) -> impl Values {
    Constructed::new(Tag::SET, inner)
}

/// Returns a value encoder for a SET with the given tag.
///
/// This is identical to `Constructed::new(tag, inner)`. It merely provides a
/// more memorial name.
pub fn set_as<V: Values>(tag: Tag, inner: V) -> impl Values {
    Constructed::new(tag, inner)
}

/// Returns the length for a structure based on the tag and content length.
///
/// This is necessary because the length octets have a different length
/// depending on the content length.
pub fn total_encoded_len(tag: Tag, content_l: usize) -> usize {
    tag.encoded_len() + Length::Definite(content_l).encoded_len() + content_l
}

/// Writes the header for a value.
///
/// The header in the sense of this function is the identifier octets and the
/// length octets.
pub fn write_header<W: io::Write>(
    target: &mut W,
    tag: Tag,
    constructed: bool,
    content_length: usize
) -> Result<(), io::Error> {
    tag.write_encoded(constructed, target)?;
    Length::Definite(content_length).write_encoded(target)?;
    Ok(())
}


//============ Helper Types ==================================================

//------------ EndOfValue ----------------------------------------------------

/// A value encoder for the end of value marker.
struct EndOfValue;

impl Values for EndOfValue {
    fn encoded_len(&self, _: Mode) -> usize {
        2
    }

    fn write_encoded<W: io::Write>(
        &self,
        _: Mode,
        target: &mut W
    ) -> Result<(), io::Error> {
        let buf = [0, 0];
        target.write_all(&buf)
    }
}


//============ Tests =========================================================

#[cfg(test)]
mod test {
    use super::*;
    use crate::encode::PrimitiveContent;

    #[test]
    fn encode_2_tuple() {
        let mut res = Vec::new();
        (0.encode(), 1.encode()).write_encoded(Mode::Der, &mut res).unwrap();
        assert_eq!(res, b"\x02\x01\0\x02\x01\x01");
    }

    #[test]
    fn encode_4_tuple() {
        let mut res = Vec::new();
        (0.encode(), 1.encode(), 2.encode(), 3.encode())
            .write_encoded(Mode::Der, &mut res).unwrap();
        assert_eq!(res, b"\x02\x01\0\x02\x01\x01\x02\x01\x02\x02\x01\x03");
    }
}
