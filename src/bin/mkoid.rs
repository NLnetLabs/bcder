//! Generates an object identifier.
//!
//! This replaces a procmacro that can produce the encoded object identifer
//! content from its components in order to define object identifier contants.
//!
//! Provide a sequence of object identifiers in ‘dot integer’ notation and
//! you will receive the octet array for it.

use std::env;
use std::str::FromStr;

fn from_str(s: &str) -> Result<u32, &'static str> {
    u32::from_str(s).map_err(|_| "only integer components allowed")
}

fn process_one(arg: &str) -> Result<(), &'static str> {
    let mut components = arg.split(".");
    let (first, second) = match (components.next(), components.next()) {
        (Some(first), Some(second)) => (first, second),
        _ => {
            return Err("at least two components required");
        }
    };
    let first = from_str(first)?;
    if first > 2 {
        return Err("first component can only be 0, 1, or 2.")
    }
    let second = from_str(second)?;
    if first < 2 && second >= 40 {
        return Err("second component for 0. and 1. must be less than 40");
    }
    let mut res = vec![40 * first + second];
    for item in components {
        res.push(from_str(item)?);
    }

    let mut first = true;
    print!("[");
    for item in res {
        if !first { print!(", "); }
        else { first = false }
        // 1111 1111  1111 1111  1111 1111  1111 1111
        // EEEE DDDD  DDDC CCCC  CCBB BBBB  BAAA AAAA
        if item > 0x0FFF_FFFF { print!("{}, ", item >> 28) }
        if item > 0x001F_FFFF { print!("{}, ", (item >> 21) & 0x7F) }
        if item > 0x0000_3FFF { print!("{}, ", (item >> 14) & 0x7F) }
        if item > 0x0000_007F { print!("{}, ", (item >> 7) & 0x7F) }
        print!("{}", item & 0x7F);
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

