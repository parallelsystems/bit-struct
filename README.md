# bit-struct #![no_std]

[![crates.io](https://img.shields.io/crates/v/bit-struct.svg)](https://crates.io/crates/bit-struct)
[![codecov](https://codecov.io/gh/andrewgazelka/bit-struct/branch/main/graph/badge.svg?token=60R82VBBVF)](https://codecov.io/gh/andrewgazelka/bit-struct)
![Minimum rustc version](https://img.shields.io/badge/rustc-1.57.0+-yellow.svg)

Bit struct is a crate which allows for ergonomic use of C-like bit fields without mediocre IDE support resulting from proc macros.
In addition, everything is statically typed checked!

Take the following example

```rust
use bit_struct::*; 

enums! {
    // 2 bits, i.e., 0b00, 0b01, 0b10
    HouseKind { Urban, Suburban, Rural}
}

bit_struct! {
    // u8 is the base storage type. This can be any multiple of 8
    struct HouseConfig(u8) {
        // 2 bits
        kind: HouseKind,
        
        // two's compliment 3-bit signed number
        lowest_floor: i3,
        
        // 2 bit unsigned number
        highest_floor: u2,
    }
}
```

We can create a new `HouseConfig` like such:
```rust
let config = HouseConfig::new(HouseKind::Suburban, i3!(-2), u2!(1));
```
where all numbers are statically checked to be in bounds. We can get the 
raw `u8` which represents `config`:
```rust
let raw: u8 = config.raw();
```
or we can get a `HouseConfig` from a `u8` like
```rust
let config: HouseConfig = HouseConfig::try_from(123_u8).unwrap();
```
We need to unwrap because `HouseConfig` is not valid for all numbers. For instance, if the
most significant bits are `0b11`, it encodes an invalid `HouseKind`. However, 
if all elements of a struct are always valid (suppose we removed the `kind` field), the struct will
auto implement a trait which allows calling
```rust
let config: HouseConfig = HouseConfig::exact_from(123_u8);
```
which will never panic. We can access values of `config` like so:
```rust
// get a value
let kind: HouseKind = config.kind().get();

// set a value
config.lowest_floor().set(i3!(0));
```
We can also access bit-level numbers as std-lib values like this
```rust
let lowest_floor: i3 = config.lowest_floor().get();
let lowest_floor_std: i8 = lowest_floor.value();
```

## Benefits
- No proc macros
- Autocompletion fully works (tested in IntelliJ Rust)
- Fast compile times
- Statically checked bounds (structs cannot be over-filled)
- Statically checked types

## Further Documentation
Look at the integration tests in the `tests` folder for further insight.
