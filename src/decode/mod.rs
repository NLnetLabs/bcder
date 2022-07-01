//! Parsing BER-encoded data.
//!
//! This modules provides the means to parse BER-encoded data.
//!
//! The basic idea is that for each type a function exists that knows how
//! to decode one value of that type. For constructed types, this function
//! in turn relies on similar functions provided for its constituent types.
//! For a detailed introduction to how to write these functions, please
//! refer to the [decode section of the guide][crate::guide::decode].
//!
//! The two most important types of this module are [`Primitive`] and
//! [`Constructed`], representing the content octets of a value in primitive
//! and constructed encoding, respectively. Each provides a number of methods
//! allowing to parse the content.
//!
//! You will never create a value of either type. Rather, you get handed a
//! reference to one as an argument to a closure or function argument to be
//! provided to these methods. 
//!
//! The enum [`Content`] is used for cases where a value can be either
//! primitive or constructed such as most string types.
//!
//! The data for decoding is provided by any type that implements the
//! [`Source`] trait – or can be converted into such a type via the
//! [`IntoSource`] trait. Implementations for both `bytes::Bytes` and
//! `&[u8]` are available.
//!
//! During decoding, errors can happen. There are two kinds of errors: for
//! one, the source can fail to gather more data, e.g., when reading from a
//! file fails. Such errors are called _source errors._ Their type is
//! provided by the source.
//!
//! Second, data that cannot be decoded according to the syntax is said to
//! result in a _content error._ The [`ContentError`] type is used for such
//! errors.
//!
//! When decoding data from a source, both errors can happen. The type
//! `DecodeError` provides a way to store either of them and is the error
//! type you will likely encounter the most.

pub use self::content::{Content, Constructed, Primitive};
pub use self::error::{ContentError, DecodeError};
pub use self::source::{
    BytesSource, CaptureSource, IntoSource, Pos, LimitedSource, SliceSource,
    Source
};

mod content;
mod error;
mod source;

