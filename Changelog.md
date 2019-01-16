# Change Log

## 0.2.0

Breaking Changes

*  `PrimitiveContent`’s methods take `self` instead of `&self`. This
   avoids the lifetime argument in `Primitive`, its encoder. [(#7)]

New

*  `encode::Values` implemented for tuples of up to twelve elements.
   [(#9)]

Bug Fixes

Dependencies

[(#7)]: https://github.com/NLnetLabs/bcder/pull/7
[(#9)]: https://github.com/NLnetLabs/bcder/pull/9


## 0.1.0

Initial public release.

