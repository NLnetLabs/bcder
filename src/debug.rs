//! Macros for last-resort debugging.
//!
//! _Note:_ This facility is going to be replaced by an error type that
//! includes a backtrace of the `extra-debug` feature is set.
//!
//! Since error reporting of the BER parser is limited on purpose, debugging
//! code using it may be difficult. To remedy this somewhat, this module
//! contains a macro `xerr!()` that will print out a backtrace if the
//! `extra-debug` feature is enable during build before resolving into
//! whatever the expression it encloses resolves to otherwise. Use it
//! whenever you initially produce an error, i.e.:
//!
//! ```rust,ignore
//! if foo {
//!     xerr!(Err(Error::Malformed))
//! }
//! ```
//!
//! or, with an early return:
//!
//! ```rust,ignore
//! if foo {
//!     xerr!(return Err(Error::Malformed)));
//! }
//! ```

#[cfg(feature = "extra-debug")]
extern crate backtrace;

#[cfg(feature="extra-debug")]
pub use self::backtrace::Backtrace;

#[cfg(feature = "extra-debug")]
#[macro_export]
macro_rules! xerr {
    ($test:expr) => {{
        eprintln!(
            "--- EXTRA DEBUG ---\n{:?}\n--- EXTRA DEBUG ---",
            $crate::debug::Backtrace::new()
        );
        $test
    }}
}

#[cfg(not(feature = "extra-debug"))]
#[macro_export]
macro_rules! xerr {
    ($test:expr) => { $test };
}

