//! Generates an object identifier.
//!
//! This replaces a procmacro that can produce the encoded object identifer
//! content from its components in order to define object identifier contants.
//!
//! Provide a sequence of object identifiers in ‘dot integer’ notation and
//! you will receive the octet array for it.

use std::env;
use bcder::Oid;

fn process_one(arg: &str) -> Result<(), &'static str> {
    let oid_bytes = arg.parse::<Oid<Vec<u8>>>()?.0;

    print!("[");
    for byte in oid_bytes { // rust doesn't mind an extra trailing comma
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

