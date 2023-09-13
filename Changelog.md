# Change Log

## 0.7.3

Release 2023-09-13.

This release fixes a number of decoding issues that can lead to panics on
invalid input data. They have been assigned CVE-2023-39914.

Bug fixes

* Fixes various decoding that lead to a panic on invalid data.
  Specifically:
    * error out rather than panic when a nested value has a greater length
      than allowed by the outer value,
    * check that there is enough data available before skipping over a
      primitive value’s content,
    * check that enough data is available before trying to parse a tag value,
    * check for correct encoding of bit strings: don’t allow the number of
      unused bits to be greater than 7 and that they are zero for an empty
      bit string,
    * check for correct encoding of object identifiers: they cannot be empty
      and the last byte must have bit 7 cleared.


## 0.7.2

Released 2023-06-01.

New
* Added an implementation of `FromStr` for `Oid`. ([#71] by [@Outurnate])

[#71]: https://github.com/NLnetLabs/bcder/pull/71
[@Outurnate]: https://github.com/Outurnate


## 0.7.1

Released 2022-12-09.

New

* Added a number of missing well-defined tags as `Tag` constants,
  specifically: `CHARACTER STRING`, `TIME`, `DATA`, `TIME_OF_DAY`,
  `DATE_TIME`, `DURATION`, `OID-IRI`, and `RELATIVE-OID-IRI`.
  ([#67] by [@lvkv])

Bug fixes

* Fix `Tag::BMP_STRING` to `UNIVERSAL 30`. ([#67] by [@lvkv])

[#67]: https://github.com/NLnetLabs/bcder/pull/67
[@lvkv]: https://github.com/lvkv


## 0.7.0

Released 2022-07-18.

Breaking Changes

* Redesign error handling in `decode` module ([#65]):
  * three error types, `Source::Error`, `ContentError`, and `DecodeError`,
    for data fetching errors, syntax errors, and a combination of these,
    respectively;
  * new trait `IntoSource` to convert a type into its `Source`
    implementation;
  * `Source::advance` now panics if advancing past the end of seen data.

[#65]: https://github.com/NLnetLabs/bcder/pull/65


## 0.6.1

Released 2012-10-29.

New

* `int::Unsigned` can now be created from an arbitrary length big-endian
  representation of an unsigned integer. ([#59])
* Add `OctetString::take_opt_from`. ([#61])

[#59]: https://github.com/NLnetLabs/bcder/pull/59
[#61]: https://github.com/NLnetLabs/bcder/pull/61


## 0.6.0

Released 2021-01-04.

Breaking Changes

* Minimum supported Rust version is now 1.42. ([#56])
* Upgrade *bytes* to 1.0. ([#57])

[#56]: https://github.com/NLnetLabs/bcder/pull/56
[#57]: https://github.com/NLnetLabs/bcder/pull/57


## 0.5.1

Released 2021-01-04.

Bug Fixes

* Fix `oid::Iter` to actually iterate over the components. ([#50])

[#50]: https://github.com/NLnetLabs/bcder/pull/50


## 0.5.0 

Breaking

* Move extending a `Captured` to an explicit `CapturedBuilder`. This
  becomes necessary with bytes 0.5. Both these types now reside in the
  module `captured` with `Captured` re-exported at crate level.
  ([#46], [#47])

Dependencies

* Upgrade bytes to 0.5. ([#43], thanks to [@Fabian-Gruenbichler])
* Upgrade smallvec to 1.1. ([#48])

[#43]: https://github.com/NLnetLabs/bcder/pull/43
[#46]: https://github.com/NLnetLabs/bcder/pull/46
[#47]: https://github.com/NLnetLabs/bcder/pull/47
[#48]: https://github.com/NLnetLabs/bcder/pull/48
[@Fabian-Gruenbichler]: https://github.com/Fabian-Gruenbichler


## 0.4.2

Bug Fixes

* Fix handling of incomplete multi-byte tags. ([#44], based on [#41] by
  [@dovreshef])


[#41]: https://github.com/NLnetLabs/bcder/pull/41
[#44]: https://github.com/NLnetLabs/bcder/pull/44
[@dovreshef]: https://github.com/dovreshef


## 0.4.1

New

* Support for multi-byte tags with tag numbers of up to `0x1F_FFFF`.
  ([#37], thanks to by [@dovreshef])

Bug Fixes

* Fix encoding of signed builtin integer (`i8`, `i16`, …). [(#39)]


[#37]: https://github.com/NLnetLabs/bcder/pull/37
[(#39)]: https://github.com/NLnetLabs/bcder/pull/39
[@dovreshef]: https://github.com/dovreshef


## 0.4.0

Breaking

* Dropped `RestrictedString::to_string` and implemented it via `Display`
  instead. Therefore, you will have to `use std::fmt::Display` to get it
  back. [(#33)]

Bug Fixes

* Safely decode deeply nested BER such as octet strings. Decoding such
  types now uses an allocated artificial stack and will thus not overflow
  the regular one. [(#30)]

Miscellaneous

* Dropped dependency on `derive_more` for fewer dependencies and faster
  compiling. ([#32], thanks to [@nocduro]).

[(#30)]: https://github.com/NLnetLabs/bcder/pull/30
[#32]: https://github.com/NLnetLabs/bcder/pull/32
[(#33)]: https://github.com/NLnetLabs/bcder/pull/33
[@nocduro]: https://github.com/nocduro


## 0.3.1

Bug Fixes

* Fix a lifetime warning from the new borrow checker. [(#27)]
* Build on 32 bit systems. [(#29)]

Other Changes

* Switch to Rust edition 2018.

[(#27)]: https://github.com/NLnetLabs/bcder/pull/27
[(#29)]: https://github.com/NLnetLabs/bcder/pull/29


## 0.3.0

Breaking

* The minimum supported Rust version is now 1.34.0. [(#22)]

New

* New methods for checking the class and number on `Tag`. [(#20)]
* Implement `TryFrom` for builtin integers and `Integer` and `Unsigned`.
  [(#23)]
* `RestrictedString::into_bytes` [(#24)]

Other Changes

* The `xerr!` macro now prints a backtrace with the `extra-debug` feature
  enabled instead of panicking. [(#21)]

[(#20)]: https://github.com/NLnetLabs/rpki-rs/pull/20
[(#21)]: https://github.com/NLnetLabs/rpki-rs/pull/21
[(#22)]: https://github.com/NLnetLabs/rpki-rs/pull/22
[(#23)]: https://github.com/NLnetLabs/rpki-rs/pull/23
[(#24)]: https://github.com/NLnetLabs/rpki-rs/pull/24


## 0.2.1

New

*  Add `BitString::encode_slice` and `encode_slice_as`. [(#17)]

Bug Fixes

*  Fix incorrect encoding of primitive unsigned integers for values with a
   number of leading zero bits divisible by eight. [(#16)]
*  Fix the mkoid tool to correctly encode large subidentifiers. [(#18)]

[(#16)]: https://github.com/NLnetLabs/rpki-rs/pull/16
[(#17)]: https://github.com/NLnetLabs/rpki-rs/pull/17
[(#18)]: https://github.com/NLnetLabs/rpki-rs/pull/18


## 0.2.0

Breaking Changes

*  Drop use of _failure_ crate. Error types now provide a `Display`
   implementation only. [(#15)]

*  `PrimitiveContent`’s methods take `self` instead of `&self`. This
   avoids the lifetime argument in `Primitive`, its encoder. [(#7)]

*  For all provided type, change `encode` and `encode_as` methods to take
   self by value and introduce `encode_ref` and `encode_ref_as` that take
   self by reference. [(#12)]

*  `RestrictedString::from_str` replaced by an implementation of the
   `FromStr` trait. [(#13)]

New

*  `encode::Values` implemented for tuples of up to twelve elements.
   [(#9)]

*  `OctetString::encode_slice` and `encode_slice_as`: allows encoding a bytes
   slice as an octet string without going through making an `OctetString`
   first.

*  `encode::Slice` wraps a slice of values encoding `encode::Values` and
   provides an encoder for it. [(#11)]

*  new functions: `encode::slice` and `encode::iter` as shortcuts for the
   respective associated functions. [(#11)]

*  `OctetString::is_empty` [(#13)], `OctetString::into_bytes` [(#14)].

[(#7)]: https://github.com/NLnetLabs/bcder/pull/7
[(#9)]: https://github.com/NLnetLabs/bcder/pull/9
[(#10)]: https://github.com/NLnetLabs/bcder/pull/10
[(#11)]: https://github.com/NLnetLabs/bcder/pull/11
[(#12)]: https://github.com/NLnetLabs/bcder/pull/12
[(#13)]: https://github.com/NLnetLabs/bcder/pull/13
[(#14)]: https://github.com/NLnetLabs/bcder/pull/14
[(#14)]: https://github.com/NLnetLabs/bcder/pull/15


## 0.1.0

Initial public release.

