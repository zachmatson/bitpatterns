# bitpatterns
---

[![Crates.io](https://img.shields.io/crates/v/bitpatterns)](https://crates.io/crates/bitpatterns)
[![docs.rs](https://img.shields.io/docsrs/bitpatterns)](https://docs.rs/bitpatterns)
![Crates.io](https://img.shields.io/crates/l/bitpatterns)
[![Crates.io](https://img.shields.io/crates/d/bitpatterns)](https://crates.io/crates/bitpatterns)

Simple bitwise pattern testing for integers.

Provides functionality to compare integers against patterns of bits which include wildcards.
Patterns can be declared with convenient macros, the generated code is incredibly small and
efficient, `no_std`, and the crate depends only on its `bitpatterns-proc-macro`, which itself
has *zero* dependencies.

Bitwise patterns are stored in the [`BitPattern`] type, which provides the [`is_match`][BitPattern::is_match] method to
test for matches. The easiest way to create one of these patterns is with the [`bitpattern!`] macro,
or the [`is_bit_match!`] macro if the pattern is only being used once.

## Examples
```rust
use bitpatterns::*;

// BitPatterns can be stored as normal variables
let pattern_1 = bitpattern!("0b1_0..1");
// Or even consts
const PATTERN_2: BitPattern<u8> = bitpattern!("00..1");

// Now, we can test these patterns against numbers
assert!(pattern_1.is_match(19)); // 19 == 0b10011
assert!(!PATTERN_2.is_match(19));

assert!(!pattern_1.is_match(5)); // 5 == 0b00101
assert!(PATTERN_2.is_match(5));

// Any digits which are not part of the pattern string are automatically
// treated as wildcards
assert!(PATTERN_2.is_match(35)); // 35 == 0b100011

// The is_bit_match macro can be used without declaring a pattern variable
assert!(is_bit_match!("101..", 20)); // 20 == 0b10100

// Using an `as` conversion to compare a number to a pattern of a different
// size/signedness always works, keeping in mind that bits not specified in
// the pattern are considered wildcards
let pattern_3 = bitpattern!("1..01", u8);
let x: i16 = 0b0100_0010_1001_1001;
assert!(pattern_3.is_match(x as u8));
```

## License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or https://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or https://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
