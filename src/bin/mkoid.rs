//! Generates an object identifier.
//!
//! This replaces a procmacro that can produce the encoded object identifer
//! content from its components in order to define object identifier contants.
//!
//! Provide a sequence of object identifiers in ‘dot integer’ notation and
//! you will receive the octet array for it.

use std::env;
use bcder::oid::{Oid, ParseOidError};

fn process_one(arg: &str) -> Result<(), ParseOidError> {
    let oid = arg.parse::<Box<Oid>>()?;

    print!("[");
    for byte in oid.as_slice() {
        print!("{},", byte);
    }
    println!("]");

    Ok(())
}

fn main() {
    let mut args = env::args();
    args.next().unwrap(); // Skip executable name.
    for arg in args {
        if let Err(err) = process_one(arg.as_ref()) {
            println!("{}: {}.", arg, err)
        }
    }
}

