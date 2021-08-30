//! Procedural macro for the bitpatterns crate to handle string parsing to numeric tokens at compile time
#![doc(hidden)]

use proc_macro::*;

// We have to keep this function technically public because the public macros will insert it
// Could keep privacy by making this a helper function and just handling all of the macros
// as proc-macros in this crate, but this is not ideal

/// ***Do not use this macro in your code. Ever.
/// This is an internal library function and has no guarantee of API stability across any updates
/// including patch updates. Consider using the other macros exported by bitpatterns.***
///
/// Extracts a tuple of `(set, cleared)` bits from the input `TokenStream`, which should contain
/// a string from which to extract these as its first token. Inserts the tuple where the macro is called.
#[doc(hidden)]
#[proc_macro]
pub fn __extract_set_and_cleared(input: TokenStream) -> TokenStream {
    // input is a proc_macro TokenStream with the layout:
    // TokenStream [
    //     Group {
    //         ...,
    //         stream: TokenStream [
    //             Literal { ... }
    //         ]
    //     }
    // ]
    //
    // So we need to extract the group, then the literal from the group
    // We control the inputs here so these panics should never be triggered if our code works
    let token_group = if let Some(TokenTree::Group(group)) = input.into_iter().next() {
        group
    } else {
        panic!("{}", PARSE_FAILED_MSG);
    };
    let pattern_literal =
        if let Some(TokenTree::Literal(literal)) = token_group.stream().into_iter().next() {
            literal.to_string()
        } else {
            panic!("{}", PARSE_FAILED_MSG);
        };

    // The to_string form of a string literal contains the quotes in the string,
    // and we will support the literal being provided as a string
    let pattern_contents = pattern_literal.trim_matches('"');

    // Support optional 0b prefix and _ separator
    let pattern = pattern_contents
        .strip_prefix("0b")
        .unwrap_or(&pattern_contents)
        .replace(|c| ['_', ' '].contains(&c), "");

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

    // This should never panic because map_bitstring will only produce a string of 1's and 0's,
    // which is a valid binary number
    // We don't need to worry about preserving the span because the output of this will be wrapped in another macro
    format!("(0b{}, 0b{})", set, cleared)
        .parse()
        .expect(PARSE_FAILED_MSG)
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
        .collect();

    match result.len() {
        0 => "0".to_string(),
        _ => result,
    }
}

/// Failure message for generic parse failure
const PARSE_FAILED_MSG: &str = "Failed to parse bitpattern! arguments.";
/// Failure message for failure to parse the pattern as numbers
fn panic_invalid_num_char(pattern: &str, invalid_char: char) -> ! {
    panic!(
        "Failed to parse pattern {} as a number due to the invalid character {}. The pattern should contain the digits '0' and '1', with '.' used for a wildcard.",
        pattern, invalid_char
    )
}
