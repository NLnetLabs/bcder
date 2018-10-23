# bcder – BER, CER, and DER Encoding and Decoding for Rust

This crate provides decoding and encoding for Basic Encoding Rules
(BER) of the ASN.1 standard as well as the more strict variants
Canonical Encoding Rules (CER) and Distinguished Encoding Rules (DER).
It provides the basic machinery as well as implementation for the most
important universal types of ASN.1.


## Usage

Add the following dependency to your `Cargo.toml`:

```
[dependencies]
bcder = "^0.1"
```

A guide introducing ASN.1, BER, and how to use this crate is part of the
source as the [`ber::guide`] module.

[`bcder::guide`]: https://docs.rs/bcder/0.1/bcder/guide/index.html


## Contributing

If you have comments, proposed changes, or would like to contribute,
please open an issue.


## License

_bcder_ is distributed under the terms of the BSD-3-clause license. See
LICENSE for details.

