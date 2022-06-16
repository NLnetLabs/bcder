//! Parsing BER-encoded data.
//!
//! This modules provides the means to parse BER-encoded data.
//!
//! The basic idea is that for each type a function exists that knows how
//! to decode one value of that type. For constructed types, this function
//! in turn relies on similar functions provided for its consituent types.
//! For a detailed introduction to how to write these functions, please
//! refer to the [decode section of the guide].
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
//! Decoding is jumpstarted by providing a data source to parse data from.
//! This is any value that implements the [`Source`] trait.
//!
//! [decode section of the guide]: ../guide/decode/index.html
//! [`Primitive`]: struct.Primitive.html
//! [`Constructed`]: struct.Constructed.html
//! [`Content`]: enum.Content.html
//! [`Source`]: trait.Source.html

pub use self::content::{Content, Constructed, Primitive};
pub use self::error::{ContentError, Error};
pub use self::source::{CaptureSource, LimitedSource, Source};

mod content;
mod error;
mod source;

