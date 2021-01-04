//! A short introduction to ASN.1 and BER.
//!
//! # ASN.1 and Encoding Rules
//!
//! The _Abstract Syntax Notation One_ (ASN.1) is a formal language that can
//! be used to describe the structure of data. Statements describe both data
//! types and how they are composed from other types. In addition, values of
//! these types can be specified. These rules do not, however, describe how
//! the values are to be represented in files or on the network. This is done
//! by accompanying standards known as _encoding rules._ Different such rules
//! exist.
//! 
//! On set of such encoding rules is the _Basic Encoding Rules_ (BER). They
//! are a relatively simple type-length-values encoding that can be derived
//! straightforwardly from the ASN.1 notation. BER gives the encoder a number
//! of options to accommodate differing use cases. As this means there is not
//! necessarily a canonical encoding of a type, two restrictive profiles on
//! top of BER have been defined: The _Canonical Encoding Rules_ (CER) cater
//! for cases where data is streamed and the final size of values is not
//! necessarily known up front while _Distinguished Encoding Rules_ (DER)
//! always use the most simple option but require the overall length to be
//! availbale before starting to encode.
//!
//! ASN.1 is currently defined in ITU-T recommendation [X.680], the three
//! encoding rules in [X.690]. Both these recommendations are freely available
//! from the ITU.
//!
//! [X.680]: https://www.itu.int/rec/T-REC-X.680-201508-I/en
//! [X.690]: https://www.itu.int/rec/T-REC-X.690-201508-I/en
//!
//!
//! # ASN.1 Definitions
//!
//! ASN.1 collects definitions into documents called modules. All definitions
//! create named objects: data types if the names start with a capital letter
//! or values if they start with a small letter.
//!
//! As an example, here is how a certificate is defined by RFC 5280:
//!
//! ```text
//! Certificate  ::=  SEQUENCE  {
//!      tbsCertificate       TBSCertificate,
//!      signatureAlgorithm   AlgorithmIdentifier,
//!      signature            BIT STRING  }
//! ```
//! 
//! This snippet defines a data type `Certificate` in terms of a number of
//! other types. The terms in all caps are universal types that are part of
//! the standard. `SEQUENCE` is a sequence of well defined elements
//! provided one after another within the braces. In this case there are
//! three elements. The first part is the name of the element and the
//! second its type. The two types `TBSCertificate` and `AlgorithmIdentifer`
//! are in turn defined elsewhere in the module while `BIT STRING` is a
//! universal type representing a sequence of bits.
//!
//! Universal types are the fundamental building blocks that all ASN.1
//! structures eventually boil down to. Each of these types has an
//! identifying code called their tag. The BIT STRING type, for instance,
//! has the tag 3 in universal class.
//!
//! > _Continues:_
//! > * implicit v. explicit tags,
//! > * OPTIONAL, DEFAULT.
//!
//!
//! # Encoding ASN.1 Values
//!
//! The Basic Encoding Rules describe how to encode a values of data types
//! described by ASN.1 defintions. Since these definitions are either
//! fundamental types or composed from other types, BER distinguishes two
//! categories of encodings: primitive encodings for those fundamental
//! types and constructed encodings for types that are composed from other
//! types.
//!
//! Both categories consist of three parts: identifier octets, length octets,
//! and content octets. The idenitifer octets describe the type of the value.
//! They contain its tag and whether primitive or constructed encoding is
//! used. The length octets determine the length of the value, more
//! specifically the number of octets in the content octet. Those content
//! octets finally contain the value’s content. For values in primitive
//! encoding the interpretation of those octets depends on the type. For
//! values in constructed encoding, the content octets are a sequence of
//! values in BER encoding – i.e., the value is constructed from a sequence
//! of more values.
//!
//! > _Continues:_
//! > * details on encoding of tag,
//! > * definite v. indefinite length.
//!
//!
//! # Selected Universal Types
//!
//! ASN.1 defines a wide range of types for all sorts of occassions. In
//! practice, you are likely to encounter only a few. The following has
//! some details on the types that the _ber_ crate supports.
//!
//! > _well, it will have, soon …_
