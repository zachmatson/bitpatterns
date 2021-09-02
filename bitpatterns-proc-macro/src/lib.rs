//! Procedural macro for the bitpatterns crate to handle string parsing to numeric tokens at compile time

#![doc(hidden)]

use std::str::FromStr;

// We have to keep this function technically public because the public macros will insert it
// Could keep privacy by making this a helper function and just handling all of the macros
// as proc-macros in this crate, but this is not ideal

/// ***Do not use this macro in your code. Ever.
/// This is an internal library function and has no guarantee of API stability across any updates
/// including patch updates. Consider using the other macros exported by bitpatterns.***
///
/// Generates a BitPattern from a pattern literal at compile time. Arguments should be the crate prefix
/// as an ident, the pattern, and optionally a specified type.
#[doc(hidden)]
#[proc_macro]
pub fn __bitpattern_inner(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    __bitpattern_testable(input.into()).into()
}

#[cfg(not(test))]
use proc_macro::*;
#[cfg(test)]
use proc_macro2::*;

/// Another inner layer under our proc macro which can be tested and will use `proc_macro` for normal use
///  or `proc_macro2` for testing
fn __bitpattern_testable(input: TokenStream) -> TokenStream {
    // Input is a TokenStream consisting of:
    // - The crate prefix identifier ($crate)
    // - A pattern string literal
    // - An optional type name
    // We control the inputs here so these panics should never be triggered if our code works
    let mut stream = flatten_tokenstream(input).into_iter();
    let crate_prefix = stream.next().expect(PARSE_FAILED_MSG);
    let pattern_literal = match stream.next() {
        Some(TokenTree::Literal(literal)) => literal.to_string(),
        _ => panic!("{}", PARSE_FAILED_MSG),
    };
    let declared_type = match stream.next() {
        Some(TokenTree::Ident(ident)) => Some(ident.to_string()),
        _ => None,
    };

    // The to_string form of a string literal contains the quotes in the string
    // We will require the literal here to be a string
    let pattern = pattern_literal
        .strip_prefix('"')
        .expect(PARSE_FAILED_MSG)
        .strip_suffix('"')
        .expect(PARSE_FAILED_MSG);

    // Support optional 0b prefix and _ separator
    let pattern = pattern
        .strip_prefix("0b")
        .unwrap_or(pattern)
        .replace(&['_', ' '][..], "");

    let set = map_bitstring(&pattern, |c| match c {
        '1' => Some('1'),
        '0' | '.' => Some('0'),
        _ => None,
    });
    let cleared = map_bitstring(&pattern, |c| match c {
        '0' => Some('1'),
        '1' | '.' => Some('0'),
        _ => None,
    });

    let size = [8, set.len(), cleared.len()]
        .iter()
        .max()
        .unwrap()
        .next_power_of_two();

    assert!(size <= 128, "{}", PATTERN_TOO_LARGE_MSG);

    let type_suffix = declared_type.map_or_else(
        || format!("u{}", size),
        |t| match get_primitive_int_size(&t) {
            // The type must be *large enough* to hold the pattern
            Some(declared_size) if declared_size >= size => t,
            _ => panic_invalid_type_size(size),
        },
    );

    // We don't need to worry about preserving the span because the output of this will be wrapped in another macro
    // Crate prefix must be added separately because we get the special `$crate` ident from the declarative macro,
    // and a procedural macro cannot generate this ident
    let output_fragment = format!(
        "::BitPattern::<{output_type}>::set_and_cleared_const(0b{}{output_type}, 0b{}{output_type})",
        set,
        cleared,
        output_type = type_suffix,
    )
    .parse()
    .expect(PARSE_FAILED_MSG);

    vec![
        crate_prefix,
        TokenTree::Group(Group::new(Delimiter::None, output_fragment)),
    ]
    .into_iter()
    .collect()
}

/// Extract the stream from a TokenTree group
fn flatten_tokenstream(input: TokenStream) -> Vec<TokenTree> {
    fn flatten_tokenstream_inner(input: TokenStream, mut output: Vec<TokenTree>) -> Vec<TokenTree> {
        for token in input {
            if let TokenTree::Group(group) = token {
                output = flatten_tokenstream_inner(group.stream(), output);
            } else {
                output.push(token);
            }
        }
        output
    }
    flatten_tokenstream_inner(input, Vec::new())
}

/// Map the characters of a bitstring using a mapper function and panic with appropriate message if some characters
/// cannot be mapped. `_` characters are ignored.
fn map_bitstring<F>(bitstring: &str, mapper: F) -> String
where
    F: Fn(char) -> Option<char>,
{
    let result: String = bitstring
        .chars()
        .map(|c| mapper(c).unwrap_or_else(|| panic_invalid_num_char(bitstring, c)))
        // Skips *leading* zeros in the mapped string
        // This might allow us to optimize the size of a pattern with leading ignored bits
        .skip_while(|c| *c == '0')
        .collect();

    match result.len() {
        0 => "0".to_string(),
        _ => result,
    }
}

/// Get the size of a primitive int type given the name, or return `None` if the input isn't of the form `[ui](\d+)`
fn get_primitive_int_size(type_name: &str) -> Option<usize> {
    usize::from_str(type_name.strip_prefix(&['u', 'i'][..])?).ok()
}

/// Failure message for generic parse failure
const PARSE_FAILED_MSG: &str = "Failed to parse bitpattern! arguments.";
/// Failure message for pattern that is too large
const PATTERN_TOO_LARGE_MSG: &str = "A pattern cannot have a size greater than 128 bits.";
/// Failure message for invalid or too small type
fn panic_invalid_type_size(required_size: usize) -> ! {
    panic!("Explicit type given for bitpattern! is invalid or too small to fit the pattern. The pattern requires a type with at least {} bits.", required_size)
}
/// Failure message for failure to parse the pattern as numbers
fn panic_invalid_num_char(pattern: &str, invalid_char: char) -> ! {
    panic!(
        "Failed to parse pattern {} as a number due to the invalid character {}. The pattern should contain the digits '0' and '1', with '.' used for a wildcard.",
        pattern, invalid_char
    )
}

#[cfg(test)]
mod tests {
    use std::panic::catch_unwind;

    use quote::quote;

    use crate::__bitpattern_testable;
    use PanicStatus::*;
    enum PanicStatus {
        Panic,
        Success,
    }

    macro_rules! bp_macro_test {
        ($panic_status:ident, $($test:tt)+) => {
            let thread_result = catch_unwind(|| __bitpattern_testable(quote!($($test)+)));
            assert!(match $panic_status {
                Panic => thread_result.is_err(),
                Success => thread_result.is_ok(),
            }, "{:?}", thread_result);
        };
    }

    #[test]
    fn type_too_small() {
        bp_macro_test!(Panic, test "0b1010101010" u8);
        bp_macro_test!(Panic, test "0b1010101010" i8);
        bp_macro_test!(Success, test "0b.....0000" u8);
        bp_macro_test!(Success, test "0b.....0000" i8);
        bp_macro_test!(Panic,
            test
            // 129 bit pattern
            "100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
            i128
        );
        bp_macro_test!(Success, test "10101010" u8);
        bp_macro_test!(Success, test "10101010" u16);
    }

    #[test]
    fn pattern_too_long() {
        bp_macro_test!(Panic,
            test
            // 129 bit pattern
            "100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
        );
        bp_macro_test!(Success,
            test
            // 128 bit pattern
            "10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
        );
    }

    #[test]
    fn invalid_pattern_chars() {
        bp_macro_test!(Panic, test "1234");
        bp_macro_test!(Panic, test "/\0..10.3");
        bp_macro_test!(Success, test "10010");
    }

    #[test]
    fn wrong_literal_type() {
        bp_macro_test!(Panic, test 0b100_01);
        bp_macro_test!(Success, test "0b100_01");
        bp_macro_test!(Panic, test 0b10..0_01 u8);
        bp_macro_test!(Success, test "0b10..0_01" u8);
    }

    #[test]
    fn wrong_input_tokens() {
        // Missing crate ident
        bp_macro_test!(Panic, "0b101010");
        bp_macro_test!(Panic, "0b101010" u8);
        // Good
        bp_macro_test!(Success, test "0b101010" u8);

        bp_macro_test!(Panic, test u8 "0b101010");
        bp_macro_test!(Panic, test u8);
        bp_macro_test!(Panic, u8);
    }
}
