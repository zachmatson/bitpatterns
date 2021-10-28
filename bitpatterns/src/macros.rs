//! Macros for the BitPattern crate

pub use bitpatterns_proc_macro::__bitpattern_inner;

/// Create a `const` [`BitPattern`][crate::BitPattern] from a "literal" with wildcards.
/// See the documentation for that type for more details.
///
/// Specify the pattern as a binary number inside of a string, with optional
/// `0b` prefix and underscore separators. Dots (`.`) will be treated as ignored/
/// wildcard bits which can take any value. Unspecified bits (those in places
/// beyond those in the string pattern) are always ignored.
///
/// The pattern will be given the smallest unsigned integer type capable of
/// storing it. To override this behavior, specify a type manually as a second
/// parameter. Explicitly specifying a type which is too small will cause
/// a compilation failure.
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
/// // The pattern can be stored as a constant too
/// // Note the supported 0b prefix and _ separator
/// let PATTERN_2: BitPattern<u8> = bitpattern!("0b00_01..");
/// // We can also store the pattern as another type with explicit specification
/// // This will have type BitPattern<i32>
/// let pattern_3 = bitpattern!("0b00_01..", i32);
/// // But specifying a type that is too small will fail
/// // let pattern_4 = bitpattern!("0b000010001000", u8); // Doesn't compile
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
    // We need to use a proc_macro for parsing to get strings parsed at compile time
    // But declarative macros are more expressive for handling these different cases,
    // so we split the macro code between a proc_macro for parsing and declarative
    // macros for plain syntax.
    // We also pass $crate to the proc_macro as a hack because procedural macros can't
    // construct this identifier themselves but can receive it from a declarative macro.
    // This allows us to get the behavior of $crate from the procedural macro

    ($pattern:literal $(, $type_name:ident)?) => {{
        $crate::__bitpattern_inner!($crate $pattern $($type_name)?)
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
/// see the documentation on that type for more details about it. This macro will handle
/// type issues for you; the argument will be extended/shrunk to the minimal size
/// needed for the pattern.
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
    ($pattern:literal, $other:expr) => {
        bitpattern!($pattern).is_match(($other) as _)
    };
}
