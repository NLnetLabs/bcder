//! Handling of restricted character strings.

// XXX Review note: This module is a bit makeshift for now and needs some
//     more refactoring. In particular, since we currently only support
//     character sets that are a subset of UTF-8, we don’t actually need
//     conversion, just checking.

pub use self::charset::CharSetError;
pub use self::ia5::Ia5String;
pub use self::numeric::NumericString;
pub use self::printable::PrintableString;
pub use self::string::RestrictedString;
pub use self::utf8::Utf8String;

mod charset;
mod ia5;
mod numeric;
mod printable;
mod string;
mod utf8;

