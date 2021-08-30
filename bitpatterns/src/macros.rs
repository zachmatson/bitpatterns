//! Macros for the BitPattern crate

pub use bitpatterns_proc_macro::*;

// We need to use a proc_macro for parsing to get strings parsed at compile time
// But declarative macros are more expressive for handling these different cases,
// so we split the macro code between a proc_macro for parsing and declarative
// macros for plain syntax.

/// Create a [`BitPattern`][crate::BitPattern] from a "literal" with wildcards.
/// See the documentation for that type for more details.
///
/// Specify the pattern as a binary number inside of a string, with optional
/// 0b prefix and underscore separators. Dots `.` will be treated as ignored/
/// wildcard bits which can take any value. Unspecified bits (those in places
/// beyond those in the string pattern) are always ignored.
///
/// Optionally, a type can be provdied as a second parameter, which will also
/// make the result a constant expression.
///
/// If not storing to a variable, prefer the [`is_bit_match!`] macro over
/// `bitpattern!(...).is_match(...)`.
///
/// # Examples
/// ```rust
/// use bitpatterns::*;
///
/// // Use the macro to define a BitPattern clearly
/// let pattern_1 = bitpattern!("10..01");
/// // And when specifying a type, the pattern can even be stored as a constant
/// // Note the supported 0b prefix and _ separator
/// let PATTERN_2: BitPattern<u8> = bitpattern!("0b00_01..");
///
/// // Now we can use the patterns to match numbers
/// assert!(pattern_1.is_match(45)); // 45 == 0b101101
/// assert!(!PATTERN_2.is_match(45));
///
/// assert!(!pattern_1.is_match(6)); // 6 = 0b000110
/// assert!(PATTERN_2.is_match(6));
/// ```
#[macro_export]
macro_rules! bitpattern {
    ($pattern:literal) => {{
        let (set, cleared) = $crate::__extract_set_and_cleared!($pattern);
        $crate::BitPattern::set_and_cleared(set, cleared)
    }};
    ($pattern:literal, $type_name:ident) => {{
        let (set, cleared) = $crate::__extract_set_and_cleared!($pattern);
        $crate::BitPattern::<$type_name>::set_and_cleared_const(set, cleared)
    }};
}

/// Match a number against a pattern of bits.
///
/// Patterns are "literals" of bits with an optional `0b` prefix and underscore `_`
/// separators. Dots `.` are used to denote ignored bits/wildcards. Bits more significant
/// than those specified in the pattern are also ignored. The type of the `other` being
/// compared will determine the type of the pattern that is created.
///
/// This uses a temporary [`BitPattern`][crate::BitPattern] to check a number against,
/// see the documentation on that type for more details about it.
///
/// # Examples
/// ```rust
/// use bitpatterns::*;
///
/// // Patterns use . to denote ignored bits
/// assert!(is_bit_match!("0b10..", 8));   // 8  == 0b1000
/// assert!(is_bit_match!("0b10..", 11));  // 11 == 0b1011
/// // The 0b prefix is optional, it will still be a binary pattern
/// assert!(!is_bit_match!("10..", 7));  // 7  == 0b0111
/// // Underscore separators can be used anywhere in the pattern
/// assert!(!is_bit_match!("10_..", 16)); // 16 == 0b10000
/// // Digits which are more significant than those in the pattern are always ignored
/// assert!(is_bit_match!("0b1", 3));  // 3 == 0b11
/// assert!(!is_bit_match!("0b1", 2)); // 2 == 0b10
/// ```
#[macro_export]
macro_rules! is_bit_match {
    ($pattern:literal, $other:ident) => {
        bitpattern!($pattern).is_match($other)
    };
    ($pattern:literal, $other:expr) => {
        bitpattern!($pattern).is_match($other)
    };
}
