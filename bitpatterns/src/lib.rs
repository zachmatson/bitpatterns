//! Simple bitwise pattern testing for integers.
//!
//! Provides functionality to compare integers against patterns of bits which include wildcards.
//! Patterns can be declared with convenient macros, the generated code is incredibly small and
//! efficient, and the crate has *zero* dependencies on external crates.
//!
//! Bitwise patterns are stored in the [`BitPattern`] type, which provides the [`is_match`][BitPattern::is_match] method to
//! test for matches. The easiest way to create one of these patterns is with the [`bitpattern!`] macro,
//! or the [`is_bit_match!`] macro if the pattern is only being used once.
//!    
//! # Examples
//! ```rust
//! use bitpatterns::*;
//!
//! // BitPatterns can be stored as normal variables
//! let pattern_1 = bitpattern!("0b1_0..1");
//! // Or even consts, although this requires specifying a type in the macro
//! // due to limitations with generic const functions
//! // The 0b prefix and _ separators are supported but never required
//! const PATTERN_2: BitPattern<u8> = bitpattern!("00..1", u8);
//!
//! // Now, we can test these patterns against numbers
//! assert!(pattern_1.is_match(19)); // 19 == 0b10011
//! assert!(!PATTERN_2.is_match(19));
//!
//! assert!(!pattern_1.is_match(5)); // 5 == 0b00101
//! assert!(PATTERN_2.is_match(5));
//!
//! // Any digits which are not part of the pattern string are automatically
//! // treated as wildcards
//! assert!(PATTERN_2.is_match(35)); // 35 == 0b100011
//!
//! // The is_bit_match macro can be used without declaring a pattern variable
//! assert!(is_bit_match!("101..", 20)); // 20 == 0b10100
//!
//! // Using an `as` conversion to compare a number to a pattern of a different
//! // size/signedness always works, keeping in mind that bits not specified in
//! // the pattern are considered wildcards
//! let pattern_3: BitPattern<u8> = bitpattern!("1..01");
//! let x: i16 = 0b0000_0010_1001_1001;
//! assert!(pattern_3.is_match(x as u8));
//! ```

#![deny(missing_docs)]

use std::{fmt::Display, mem::size_of};

mod macros;
pub use macros::*;

/// Used to provide a namespace for the private `BitPatternType`,
/// so the types which implement the public `BitPatternType` can't be extended later
mod private {
    use std::ops::{BitAnd, BitOr, Not, Shl};

    /// Sealed trait which defines which types can be used in `BitPattern`s  
    /// This can't be implemented outside of this crate, so it "seals off"
    /// the `BitPatternType` trait
    pub trait BitPatternType:
        Copy
        + Eq
        + BitOr<Output = Self>
        + BitAnd<Output = Self>
        // These last three are used in the format function
        + Not<Output = Self>
        + Shl<usize, Output = Self>
        + From<bool>
    {
    }
}

/// Implemented for all Rust primitive integer types; indicates types that can
/// be used in a `BitPattern`.
///
/// It is not possible to implement this for other outside types.
pub trait BitPatternType: private::BitPatternType {}
impl<T: private::BitPatternType> BitPatternType for T {}

/// A pattern of bits that integers can be matched against.
///
/// A BitPattern requires specific bits to be set and specific
/// bits to be cleared, with others ignored. It can be constructed
/// using the [`set_and_cleared`][BitPattern::set_and_cleared] method or the [`bitpattern!`] macro.
/// The [`is_match`][BitPattern::is_match] method can be used for matching numbers against the pattern.
///
/// There is also a constant [`set_and_cleared_const`][BitPattern::set_and_cleared_const] method, which
/// does not support type inference, due to a lack of support
/// for generic const functions.
///
/// See the [`bitpatterns`][crate] crate documentation for more
/// details.
///
/// # Examples
/// ```rust
/// use bitpatterns::*;
///
/// // Create a bitpattern using the set_and_cleared methods
/// let pattern_1 = BitPattern::set_and_cleared(0b1100, 0b0001);
/// const PATTERN_2: BitPattern<u8> = BitPattern::<u8>::set_and_cleared_const(0b0010, 0b1001);
/// // Create equivalent patterns with the bitpattern! macro
/// // Creating patterns this way is typically clearer
/// let macro_pattern_1 = bitpattern!("0b11.0");
/// const MACRO_PATTERN_2: BitPattern<u8> = bitpattern!("0b0.10", u8);
///
/// // Now check for matches
/// // Note that bits which weren't specified in the patterns are ignored by default
/// assert!(pattern_1.is_match(30)); // 30 == 0b11110
/// assert!(!PATTERN_2.is_match(30));
///
/// assert!(!pattern_1.is_match(2)); // 2 == 0b0010
/// assert!(PATTERN_2.is_match(2));
/// ```
#[derive(PartialEq, Eq, Hash)]
pub struct BitPattern<T: BitPatternType> {
    set: T,
    set_or_cleared: T,
}

impl<T: BitPatternType> BitPattern<T> {
    /// Match a number against the [`BitPattern`]
    ///
    /// See the [`BitPattern`] type documentation, the [`bitpattern!`] macro documentation,
    /// or the [`bitpatterns`][crate] documentation for more details about constructing
    /// patterns and the corresponding matching rules. Also see the [`is_bit_match!`] macro
    /// documentation for details on matching against a temporary/single-use `BitPattern`.
    ///
    /// # Examples
    /// ```rust
    /// use bitpatterns::*;
    ///
    /// let pattern_1 = bitpattern!("0b10..");
    /// // Compare numbers against pattern_1
    /// assert!(pattern_1.is_match(8));   // 8  == 0b1000
    /// assert!(pattern_1.is_match(11));  // 11 == 0b1011
    /// assert!(!pattern_1.is_match(7));  // 7  == 0b0111
    /// assert!(!pattern_1.is_match(16)); // 16 == 0b10000
    ///  
    /// // Digits which are more significant than those in the pattern are always ignored
    /// let pattern_2 = bitpattern!("0b1");
    /// assert!(pattern_2.is_match(3));  // 3 == 0b11
    /// assert!(!pattern_2.is_match(2)); // 2 == 0b10
    /// ```
    pub fn is_match(&self, other: T) -> bool {
        other & self.set_or_cleared == self.set
    }

    /// Create a [`BitPattern`] by specifying the bits that must be set and cleared to match it
    ///
    /// The bits that are set in `set` must be set in a matching number, and the bits that are
    /// set in `cleared` must not be set in a matching number. Any bits not specified in either
    /// will be ignored when matching numbers.
    ///
    /// The behavior of a [`BitPattern`] in which a particular bit is set in both `set` and
    /// `cleared` (i.e. `set & cleared != 0`) is guaranteed to be deterministic for a particular
    /// version of this crate, but should not be considered stable across versions.
    /// Presently, the bits in `set` take precedence over those in `cleared`.
    ///
    /// See the [`bitpattern!`] macro for a simpler way to construct a [`BitPattern`], or
    /// [`set_and_cleared_const`][BitPattern::<u8>::set_and_cleared_const] on the various
    /// [`BitPattern`] implementations for a constant version of this function.
    pub fn set_and_cleared(set: T, cleared: T) -> Self {
        BitPattern {
            set,
            set_or_cleared: set | cleared,
        }
    }
}

// We need specific impl's for the different types instead of being generic over a trait
// so we can impl a const fn
// TODO: Possibly can be improved if https://github.com/rust-lang/rfcs/pull/2632 is merged
/// Implement `private::BitPatternType` and a non-generic `BitPattern::set_and_cleared_const` for an integer type
macro_rules! impl_bit_pattern {
    ($($T:ident),+) => {$(
        impl private::BitPatternType for $T {}

        impl BitPattern<$T> {
            /// Create a [`BitPattern`] by specifying the bits that must be set and cleared to match it
            ///
            /// The bits that are set in `set` must be set in a matching number, and the bits that are
            /// set in `cleared` must not be set in a matching number. Any bits not specified in either
            /// will be ignored when matching numbers.
            ///
            /// The behavior of a [`BitPattern`] in which a particular bit is set in both `set` and
            /// `cleared` (i.e. `set & cleared != 0`) is guaranteed to be deterministic for a particular
            /// version of this crate, but should not be considered stable across versions.
            /// Presently, the bits in `set` take precedence over those in `cleared`.
            ///
            /// See the [`bitpattern!`] macro for a simpler way to construct a constant [`BitPattern`], or
            /// [`set_and_cleared`][BitPattern::set_and_cleared] for a generic (but not constant) version of
            /// this function.
            pub const fn set_and_cleared_const(set: $T, cleared: $T) -> Self {
                BitPattern {
                    set,
                    set_or_cleared: set | cleared,
                }
            }
        }
    )+};
}

impl_bit_pattern! {
    u8, u16, u32, u64, u128,
    i8, i16, i32, i64, i128
}

impl<T: BitPatternType> Display for BitPattern<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // 8 bits per byte, and we are only dealing with integer primitives
        let num_bits: usize = size_of::<T>() * 8;
        let set = self.set;
        let cleared = self.set_or_cleared & !self.set;
        // Had to do this generically somehow, this is the only way to do it with infallible
        // conversions for every integer type
        let one: T = true.into();
        let zero: T = false.into();

        let formatted_pattern = (0..num_bits)
            .map(|i| {
                let pattern = BitPattern::<T>::set_and_cleared(one << num_bits - i - 1, zero);
                if pattern.is_match(set) {
                    '1'
                } else if pattern.is_match(cleared) {
                    '0'
                } else {
                    '.'
                }
            })
            .collect::<String>();
        let formatted_pattern = formatted_pattern.trim_start_matches('.');

        write!(
            f,
            "BitPattern ( 0b{} )",
            match formatted_pattern.len() {
                0 => ".",
                _ => formatted_pattern,
            }
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_eq_display<T: Eq + Display>(left: T, right: T) {
        assert!(left == right, "Expected {} to equal {}", left, right);
    }

    #[test]
    fn bitpattern_macro() {
        // Just making sure this is still const compatible
        const PATTERN_1: BitPattern<u8> = bitpattern!("0b10..", u8);
        assert_eq_display(PATTERN_1, BitPattern::set_and_cleared(0b1000, 0b0100));
        // And testing the other form too
        let pattern_2 = bitpattern!("0b.10.");
        assert_eq_display(pattern_2, BitPattern::set_and_cleared(0b0100, 0b0010));
    }

    #[test]
    fn matching() {
        let pattern_1 = bitpattern!("0b10..", u8);

        assert!(pattern_1.is_match(0b1000));
        assert!(pattern_1.is_match(0b1001));
        assert!(pattern_1.is_match(0b1010));
        assert!(pattern_1.is_match(0b1011));
        assert!(pattern_1.is_match(0b10101011));
        assert!(pattern_1.is_match(0b01001001));
        assert!(pattern_1.is_match(-0b01001000i8 as u8));
        assert!(
            pattern_1.is_match(0b0010101010101101100010101000001001111101000101101001001i64 as u8)
        );

        assert!(!pattern_1.is_match(0b1100));
        assert!(!pattern_1.is_match(0b0100));
        assert!(!pattern_1.is_match(0b0010));
        assert!(!pattern_1.is_match(0b00101110));
        assert!(!pattern_1.is_match(-0b01001100i8 as u8));
        assert!(
            !pattern_1.is_match(0b0010101010101101100010101000001001111101000101101000001i64 as u8)
        );

        let pattern_2 = bitpattern!("0b0..0");

        assert!(pattern_2.is_match(0b0000));
        assert!(pattern_2.is_match(0b0010));
        assert!(pattern_2.is_match(0b0100));
        assert!(pattern_2.is_match(0b0110));
        assert!(pattern_2.is_match(0b10100010));
        assert!(pattern_2.is_match(0b01000100));
        assert!(pattern_2.is_match(-0b01011110i8 as u8));
        assert!(
            pattern_2.is_match(0b0010101010101101100010101000001001111101000101101000110i64 as u8)
        );

        assert!(!pattern_2.is_match(0b1100));
        assert!(!pattern_2.is_match(0b0101));
        assert!(!pattern_2.is_match(0b0011));
        assert!(!pattern_2.is_match(0b00101110));
        assert!(!pattern_2.is_match(-0b01000010i8 as u8));
        assert!(
            !pattern_2.is_match(0b0010101010101101100010101000001001111101000101101000001i64 as u8)
        );
    }

    #[test]
    fn is_bit_match_macro() {
        assert!(is_bit_match!("0b1..0", 0b1010));
        assert!(!is_bit_match!("0b1..0", 0b1001));
    }
}

#[cfg(test)]
mod fmt_tests {
    use super::*;

    #[test]
    fn normal_patterns() {
        assert_eq!(bitpattern!("0b10..").to_string(), "BitPattern ( 0b10.. )");
        assert_eq!(
            bitpattern!("0b001..1001...1.01.0").to_string(),
            "BitPattern ( 0b001..1001...1.01.0 )"
        );
        assert_eq!(bitpattern!("0b1010").to_string(), "BitPattern ( 0b1010 )");
        assert_eq!(bitpattern!("1").to_string(), "BitPattern ( 0b1 )");
        assert_eq!(bitpattern!("0").to_string(), "BitPattern ( 0b0 )");
    }

    // We might change this later but for now make sure the behavior is as expected

    #[test]
    fn leading_explicit_ignore() {
        assert_eq!(
            bitpattern!("0b..1010..").to_string(),
            "BitPattern ( 0b1010.. )"
        );
        assert_eq!(bitpattern!("0b...").to_string(), "BitPattern ( 0b. )");
    }

    #[test]
    fn empty_pattern() {
        assert_eq!(bitpattern!("").to_string(), "BitPattern ( 0b. )");
    }
}
