//! Decoding BER-encoded data.
//!
//! _Note: This guide is still work in progress and will be extended._
//!
//! Data encoded in BER is a stream of nested values for which the length
//! may or may not be known. Primitive values, for which the length _is_
//! always known, contain a sequence of octets representing a value of
//! a certain type. Constructed values are a sequence of other values. These
//! values may either have a pre-determined length or a bounded by a special
//! value marking the end of the sequence. The overall stream of data can be
//! viewed as the content of a constructed value bounded by the end of the
//! stream.
//!
//! In the *ber* crate, the content of a value is parsed through functions.
//! These functions are given a mutable reference to the value’s content and
//! are tasked with reading and processing all the content of the value. It
//! does so by calling methods on the content value. Some of these methods
//! dive into nested values. They require their own parsing functions and
//! take them as function arguments such as closures.
//!
//! An example will make this concept more clear. Let’s say we have the
//! following ASN.1 specification:
//!
//! ```text
//! EncapsulatedContentInfo  ::=  SEQUENCE  {
//!     eContentType ContentType,
//!     eContent [0] EXPLICIT OCTET STRING OPTIONAL
//! }
//!
//! ContentType  ::=  OBJECT IDENTIFIER
//! ```
//!
//! Using the types provided by the *ber* crate for object identifiers and
//! octet strings, this definition is easily mapped into a Rust struct:
//!
//! ```
//! use bcder::{Oid, OctetString};
//!
//! pub struct EncapsulatedContentInfo {
//!     content_type: Oid,
//!     content: Option<OctetString>,
//! }
//! ```
//!
//! By convention, the decoder function is called `take_from`. It looks like
//! this:
//!
//! ```
//! # use bcder::{Oid, OctetString};
//! use bcder::Tag;
//! use bcder::decode;
//! use bcder::decode::DecodeError;
//!
//! # pub struct EncapsulatedContentInfo {
//! #     content_type: Oid,
//! #     content: Option<OctetString>,
//! # }
//! #
//! impl EncapsulatedContentInfo {
//!     pub fn take_from<S: decode::Source>(
//!         cons: &mut decode::Constructed<S>
//!     ) -> Result<Self, DecodeError<S::Error>> {
//!         cons.take_sequence(|cons| {
//!             Ok(EncapsulatedContentInfo {
//!                 content_type: Oid::take_from(cons)?,
//!                 content: cons.take_opt_constructed_if(Tag::ctx(0), |cons| {
//!                     OctetString::take_from(cons)
//!                 })?
//!             })
//!         })
//!     }
//! }
//! ```
//!
//! _TODO: Elaborate._
//!
//!
//! Some types are used with an implicit tag, i.e., the encoding uses
//! a different tag than what would normally it would. For these types, a
//! function should be provided that only decodes the content. Depending on
//! the encoding used for the type, this function should be `from_primitive`,
//! `from_constructed`, or `from_content` for types that always use
//! primitive encoding, always constructed encoding, or can appear in both
//! encodings, respectively.
//!
//! As our example type always uses constructed encoding, its content
//! decoder would look like this:
//!
//! ```
//! # use bcder::{Oid, OctetString};
//! use bcder::Tag;
//! use bcder::decode;
//! use bcder::decode::DecodeError;
//!
//! # pub struct EncapsulatedContentInfo {
//! #     content_type: Oid,
//! #     content: Option<OctetString>,
//! # }
//! #
//! impl EncapsulatedContentInfo {
//!     pub fn from_constructed<S: decode::Source>(
//!         cons: &mut decode::Constructed<S>
//!     ) -> Result<Self, DecodeError<S::Error>> {
//!         Ok(EncapsulatedContentInfo {
//!             content_type: Oid::take_from(cons)?,
//!             content: cons.take_opt_constructed_if(Tag::ctx(0), |cons| {
//!                 OctetString::take_from(cons)
//!             })?
//!         })
//!     }
//! }
//! ```
//!
//! _TODO: Elaborate._
