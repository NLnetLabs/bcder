//! Encoding data in BER.
//!
//! This modules provides means to encode data in BER.
//!
//! Encoding is done using helper types called _encoders_ that represent the
//! structure of the BER encoding. These types implement the trait
//! [`Values`]. A type that can be encoded as BER typically provides a method
//! named `encode` that produces a value of its encoder type representing the
//! value’s encoding.  If necessary, they can also provide a method
//! `encode_as` that does the same thing but allows the caller to provide an
//! tag to use for encoding as is necessary for implicit tagging.
//!
//! The [`Values`] type can then be used to simply write the encoding to
//! anything that implements the standard library’s `io::Write` trait.
//!
//! The trait [`PrimitiveContent`] helps with producing encoders for types
//! that use the primitive encoding. Through this trait the types can declare
//! how their content is encoded and receive an automatic encoder type based
//! on that.
//!
//! The module also provides a number of helper types that make it easier
//! to implement encoders in various situations.
//!
//! For a more detailed introduction to writing the `encode` methods of
//! types, see the [encode section of the guide].
//!
//! [`Values`]: trait.Values.html
//! [`PrimitiveContent`]: trait.PrimitiveContent.html
//! [encode section of the guide]: ../guide/encode/index.html

pub use self::primitive::{PrimitiveContent, Primitive, primitive};
pub use self::values::{
    Choice2, Choice3, Constructed, EncodeSlice, IndefiniteConstructed, Iter,
    Nothing, Values, encode_slice, iter, sequence, sequence_as, set, set_as,
    total_len, total_indefinite_len, write_end_of_contents, write_header,
    write_indefinite_header,
};
pub use self::target::{IoTarget, SplitTarget, Target, infallible};

pub mod raw;

mod primitive;
mod target;
mod values;

