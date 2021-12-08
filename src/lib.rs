//! bit-struct

#![no_std]

use core::fmt::{Debug, Formatter};
use core::marker::PhantomData;
use core::ops::{BitAnd, BitOrAssign, BitXorAssign, Shl, ShlAssign, Shr, ShrAssign};
use num_traits::{Bounded, Num};

/// A struct which allows for getting/setting a given property
pub struct GetSet<'a, P, T, const START: usize, const STOP: usize> {
    /// The referenced bitfield type.
    parent: &'a mut P,
    /// The type in the get/set operations
    _phantom: PhantomData<T>,
}

impl<'a, P, T, const START: usize, const STOP: usize> GetSet<'a, P, T, START, STOP> {
    pub fn start(&self) -> usize {
        START
    }

    pub fn stop(&self) -> usize {
        STOP
    }
}

/// A trait which defines how many bits are needed to store a struct.
///
/// # Safety
/// Define `Num` as `{i,u}{8,16,32,64,128}`.
/// - when calling `core::mem::transmute` on `Self`, only bits [0, COUNT) can be non-zero
/// - TryFrom<Num> produces Some(x) <=> core::mem::transmute(num) produces a valid Self(x)
/// - TryFrom<Num> produces None <=> core::mem::transmute(num) produces an invalid state for Self
pub unsafe trait BitCount {
    const COUNT: usize;
}

macro_rules! bit_counts {
    ($($num: ty = $count: literal),*) => {
        $(
        unsafe impl BitCount for $num {
            const COUNT: usize = $count;
        }
        )*
    };
}

bit_counts!(u8 = 8, u16 = 16, u32 = 32, u64 = 64, u128 = 128, bool = 1);

impl u1 {
    pub const TRUE: u1 = u1(1);
    pub const FALSE: u1 = u1(0);
}

macro_rules! new_types {
    (
        $($name: ident($count: literal, $inner: ty) => [$($into: ty),*]),*
    ) => {
        $(

        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
        pub struct $name($inner);

        impl Debug for $name {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                f.write_fmt(format_args!("{}", self.0))
            }
        }

        #[macro_export]
        macro_rules! $name {
            ($value: literal) => {
                {
                    const VALUE: $inner = $value;

                    // this is always valid because we have one more bit than we need in $inner
                    // type
                    const MAX: $inner = (1 << ($count)) - 1;
                    const PANIC_IF_GT: $inner = MAX - VALUE;
                    unsafe {bit_struct::$name::new_unchecked(VALUE)}
                }
            };
        }


        unsafe impl BitCount for $name {
            const COUNT: usize = $count;
        }

        impl $name {
            /// Create a new $name from value
            /// # Safety
            /// - value must fit within the number of bits defined in the type
            pub unsafe fn new_unchecked(value: $inner) -> Self {
                Self(value)
            }

            pub fn inner(self) -> $inner {
                self.0
            }
        }

        impl Default for $name {
            fn default() -> Self {
                Self(0)
            }
        }

        $(
            impl From<$name> for $into {
                fn from(name: $name) -> $into {
                    name.0 as $into
                }
            }

            impl TryFrom<$into> for $name {
                type Error = ();

                fn try_from(inner: $into) -> Result<$name, ()>{
                   if inner >= (1 << $count) {
                       Err(())
                   }  else {
                       Ok($name(inner as $inner))
                   }
                }
            }
        )*
        )*
    };
}

new_types!(
    u1  (1, u8)   => [u8, u16, u32, u64, u128],
    u2  (2, u8)   => [u8, u16, u32, u64, u128],
    u3  (3, u8)   => [u8, u16, u32, u64, u128],
    u4  (4, u8)   => [u8, u16, u32, u64, u128],
    u5  (5, u8)   => [u8, u16, u32, u64, u128],
    u6  (6, u8)   => [u8, u16, u32, u64, u128],
    u7  (7, u8)   => [u8, u16, u32, u64, u128],
    u9  (9, u16)  => [u16, u32, u64, u128],
    u10 (10, u16) => [u16, u32, u64, u128],
    u11 (11, u16) => [u16, u32, u64, u128],
    u12 (12, u16) => [u16, u32, u64, u128],
    u13 (13, u16) => [u16, u32, u64, u128],
    u14 (14, u16) => [u16, u32, u64, u128],
    u15 (15, u16) => [u16, u32, u64, u128],
    u17 (17, u32) => [u32, u64, u128],
    u18 (18, u32) => [u32, u64, u128],
    u19 (19, u32) => [u32, u64, u128],
    u20 (20, u32) => [u32, u64, u128],
    u21 (21, u32) => [u32, u64, u128],
    u22 (22, u32) => [u32, u64, u128],
    u23 (23, u32) => [u32, u64, u128],
    u24 (24, u32) => [u32, u64, u128],
    u25 (25, u32) => [u32, u64, u128],
    u26 (26, u32) => [u32, u64, u128],
    u27 (27, u32) => [u32, u64, u128],
    u28 (28, u32) => [u32, u64, u128],
    u29 (29, u32) => [u32, u64, u128],
    u30 (30, u32) => [u32, u64, u128],
    u31 (31, u32) => [u32, u64, u128],
    u33 (33, u64) => [u64, u128],
    u34 (34, u64) => [u64, u128],
    u35 (35, u64) => [u64, u128],
    u36 (36, u64) => [u64, u128],
    u37 (37, u64) => [u64, u128],
    u38 (38, u64) => [u64, u128],
    u39 (39, u64) => [u64, u128],
    u40 (40, u64) => [u64, u128],
    u41 (41, u64) => [u64, u128],
    u42 (42, u64) => [u64, u128],
    u43 (43, u64) => [u64, u128],
    u44 (44, u64) => [u64, u128],
    u45 (45, u64) => [u64, u128],
    u46 (46, u64) => [u64, u128],
    u47 (47, u64) => [u64, u128],
    u48 (48, u64) => [u64, u128],
    u49 (49, u64) => [u64, u128],
    u50 (50, u64) => [u64, u128],
    u51 (51, u64) => [u64, u128],
    u52 (52, u64) => [u64, u128],
    u53 (53, u64) => [u64, u128],
    u54 (54, u64) => [u64, u128],
    u55 (55, u64) => [u64, u128],
    u56 (56, u64) => [u64, u128],
    u57 (57, u64) => [u64, u128],
    u58 (58, u64) => [u64, u128],
    u59 (59, u64) => [u64, u128],
    u60 (60, u64) => [u64, u128],
    u61 (61, u64) => [u64, u128],
    u62 (62, u64) => [u64, u128],
    u63 (63, u64) => [u64, u128]
);

impl<
        'a,
        P: Num + Bounded + ShlAssign<usize> + ShrAssign<usize>,
        T,
        const START: usize,
        const STOP: usize,
    > GetSet<'a, P, T, START, STOP>
{
    /// Create a new [GetSet]. This should be called from methods generated by the [bit_struct]
    /// macro
    pub fn new(parent: &'a mut P) -> Self {
        Self {
            parent,
            _phantom: PhantomData::default(),
        }
    }

    /// Get a mask of STOP-START + 1 length. This doesn't use the shift left and subtract one
    /// trick because of the special case where (0b1 << (STOP - START + 1)) - 1 will cause an
    /// overflow
    fn mask(&self) -> P {
        let num_bits = core::mem::size_of::<P>() * 8;
        let mut max_value = P::max_value();
        let keep_bits = STOP - START + 1;

        max_value >>= num_bits - keep_bits;
        max_value
    }
}

impl<
        'a,
        P: Num
            + Shl<usize, Output = P>
            + Shr<usize, Output = P>
            + ShlAssign<usize>
            + ShrAssign<usize>
            + Bounded
            + BitAnd<Output = P>
            + Copy,
        T: TryFrom<P>,
        const START: usize,
        const STOP: usize,
    > GetSet<'a, P, T, START, STOP>
{
    /// Get the property. Returns an error it does not exist.
    pub fn get(&self) -> T {
        let section = self.get_raw();
        unsafe { core::mem::transmute_copy(&section) }
    }

    pub fn is_valid(&self) -> bool {
        let section = self.get_raw();
        T::try_from(section).is_ok()
    }

    pub fn get_raw(&self) -> P {
        let parent = *self.parent;
        let mask = self.mask();
        (parent >> START) & mask
    }
}

impl<
        'a,
        P: Num
            + Shl<usize, Output = P>
            + Copy
            + BitOrAssign
            + BitXorAssign
            + BitAnd<Output = P>
            + ShlAssign<usize>
            + ShrAssign<usize>
            + PartialOrd
            + Bounded
            + Sized,
        T: Into<P> + Sized,
        const START: usize,
        const STOP: usize,
    > GetSet<'a, P, T, START, STOP>
{
    /// Set the property with a core::mem::transmute_copy
    pub fn set(&mut self, value: T) {
        let value = unsafe { core::mem::transmute_copy(&value) };
        unsafe { self.set_raw(value) }
    }

    /// Set the field to a raw value.
    /// # Safety
    /// value must be a valid representation of the field. i.e., `core::mem::transmute` between
    /// P and T must be defined.
    pub unsafe fn set_raw(&mut self, value: P) {
        let mask = self.mask();
        let mask_shifted = mask << START;

        // zero out parent
        *self.parent |= mask_shifted;
        *self.parent ^= mask_shifted;

        let to_set = value & mask;
        *self.parent |= to_set << START;
    }
}

#[macro_export]
macro_rules! impl_fields {

    ($on: expr, $kind: ty =>
    [$($first_field_doc: expr),*], $head_field: ident, $head_actual: ty $(, [$($field_doc: expr),*], $field: ident, $actual: ty)*) => {
        $(#[doc=$first_field_doc])*
        pub fn $head_field(&mut self) -> bit_struct::GetSet<'_, $kind, $head_actual, {$on - <$head_actual as bit_struct::BitCount>::COUNT}, {$on - 1}> {
            bit_struct::GetSet::new(&mut self.0)
        }

        bit_struct::impl_fields!($on - <$head_actual as bit_struct::BitCount>::COUNT, $kind => $([$($field_doc),*], $field, $actual),*);
    };
    ($on: expr, $kind: ty =>) => {};
}

/// Helper macro
#[macro_export]
macro_rules! bit_struct_impl {
    (
        $(#[doc = $struct_doc:expr])*
        #[derive(Default)]
        $struct_vis: vis struct $name: ident ($kind: ty) {
        $(
            $(#[doc = $field_doc:expr])*
            $field: ident: $actual: ty
        ),* $(,)?
        }
    ) => {

        bit_struct::bit_struct_impl!(
        $(#[doc = $struct_doc])*
        $struct_vis struct $name ($kind) {
        $(
            $(#[doc = $field_doc])*
            $field: $actual
        ),*
        }

        );

        impl Default for $name {
            fn default() -> Self {
                Self::of_defaults()
            }
        }

    };

    (
        $(#[doc = $struct_doc:expr])*
        $struct_vis: vis struct $name: ident ($kind: ty) {
        $(
            $(#[doc = $field_doc:expr])*
            $field: ident: $actual: ty
        ),* $(,)?
        }
    ) => {

        impl $name {

            /// Returns a valid representation for the bit_struct, where all values are
            /// the defaults. This is different than Self::default(), because the actual
            /// default implementation might not be composed of only the defaults of the
            /// given fields
            pub fn of_defaults() -> Self {
                let mut res = unsafe { Self::from_unchecked(0) };
                $(
                    res.$field().set(Default::default());
                )*
                res
            }
        }

        impl ::core::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> core::fmt::Result {
                let mut copied = *self;
                f.debug_struct(stringify!($name))
                    $(
                        .field(stringify!($field), &copied.$field().get())
                    )*
                    .finish()
            }
        }
    };
}

// the main is actually needed

#[allow(clippy::needless_doctest_main)]
/// Create a bit struct.
///
///
/// This macro can only be used once for each module.
/// This is because the macro creates sub-module to limit access to certain
/// unsafe access. In the macro, bit-structs can be defined just like a struct outside of the
/// the macro. The catch is a **base type** must be specified. Valid base types are
/// u{8,16,32,64,128}. The elements stored in the struct are statically guaranteed to not
/// exceed the number of bits in the base type. This means we cannot store a `u16` in a `u8`, but
/// it also means we cannot store 9 `u1`s in a u8.
///
/// Elements start at the top of the number (for a u16 this would be the 15th bit) and progress
/// down.
///
/// # Example
/// ```
/// bit_struct::enums! {
///     /// The default value for each enum is always the first
///     pub ThreeVariants { Zero, One, Two }
///
///     /// This is syntax to set the default value to Cat
///     pub Animal(Cat) { Cow, Bird, Cat, Dog }
///
///     pub Color { Orange, Red, Blue, Yellow, Green }
/// }
///
/// bit_struct::bit_struct! {
///     /// We can write documentation for the struct here. Here BitStruct1
///     /// derives default values from the above enums macro
///     #[derive(Default)]
///     struct BitStruct1 (u16){
///         /// a 1 bit element. This is stored in u16[15]
///         a: bit_struct::u1,
///
///         /// This is calculated to take up 2 bits. This is stored in u16[13..=14]
///         variant: ThreeVariants,
///
///         /// This also takes 2 bits. This is stored in u16[11..=12]
///         animal: Animal,
///
///         /// This takes up 3 bits. This is stored u16[8..=10]
///         color: Color,
///     }
///
///     struct BitStruct2(u32) {
///         /// We could implement for this too. Note, this does not have a default
///         a_color: Color,
///         b: bit_struct::u3,
///     }
/// }
///
/// fn main() {
///     use std::convert::TryFrom;
///     let mut bit_struct: BitStruct1 = BitStruct1::default();
///
///     assert_eq!(bit_struct.a().start(), 15);
///     assert_eq!(bit_struct.a().stop(), 15);
///
///     assert_eq!(bit_struct.color().start(), 8);
///     assert_eq!(bit_struct.color().stop(), 10);
///
///     assert_eq!(format!("{:?}", bit_struct), "BitStruct1 { a: 0, variant: Zero, animal: Cat, color: Orange }");
///     assert_eq!(bit_struct.raw(), 4096);
///
///     let reverse_bit_struct = BitStruct1::try_from(4096);
///     assert_eq!(format!("{:?}", reverse_bit_struct), "Ok(BitStruct1 { a: 0, variant: Zero, animal: Cat, color: Orange })");
///
///
///     // u3! macro provides a static assert that the number is not too large
///     let mut other_struct = BitStruct2::new(Color::Green, bit_struct::u3!(0b101));
///     assert_eq!(format!("{:?}", other_struct), "BitStruct2 { a_color: Green, b: 5 }");
///
///     assert_eq!(other_struct.a_color().get(), Color::Green);
///
///     other_struct.a_color().set(Color::Red);
///
///     assert_eq!(other_struct.a_color().get(), Color::Red);
/// }
/// ```
///
#[macro_export]
macro_rules! bit_struct {
    (
        $(
        $(#[doc = $struct_doc:expr])*
        $(#[derive($($struct_der: ident),+)])?
        $struct_vis: vis struct $name: ident ($kind: ty) {
        $(
            $(#[doc = $field_doc:expr])*
            $field: ident: $actual: ty
        ),* $(,)?
        }
        )*
    ) => {

        mod bit_struct_private_impl {
            use super::*;

            $(
            $(#[doc = $struct_doc])*
            #[derive(Copy, Clone, PartialOrd, PartialEq, Eq, Ord, Hash)]
            pub struct $name($kind);

            impl TryFrom<$kind> for $name {
                type Error = ();
                fn try_from(elem: $kind) -> Result<$name, ()> {
                    let mut res = Self(elem);
                    $(
                        if !res.$field().is_valid() {
                            return Err(());
                        }
                    )*
                    Ok(res)
                }
            }

            impl $name {

                pub unsafe fn from_unchecked(inner: $kind) -> Self {
                   Self(inner)
                }

                #[allow(clippy::too_many_arguments)]
                pub fn new($($field: $actual),*) -> Self {
                    let mut res = Self(0);
                    $(
                        res.$field().set($field);
                    )*
                    res
                }

                pub fn raw(self) -> $kind {
                    self.0
                }

                bit_struct::impl_fields!(<$kind as bit_struct::BitCount>::COUNT, $kind => $([$($field_doc),*], $field, $actual),*);
            }

            )*
        }

        $(
        pub use bit_struct_private_impl::$name;
        )*


        $(
        bit_struct::bit_struct_impl!(
        $(#[doc = $struct_doc])*
        $(#[derive($($struct_der),+)])?
        $struct_vis struct $name ($kind) {
        $(
            $(#[doc = $field_doc])*
            $field: $actual
        ),*
        }

        );
        )*
    };
}

#[macro_export]
macro_rules! count_idents {
    ($on: expr, [$head: ident $(,$xs: ident)*]) => {
        bit_struct::count_idents!($on + 1, [$($xs),*])
    };
    ($on: expr, []) => {
        $on
    }
}

pub const fn bits(num: usize) -> usize {
    const fn helper(count: usize, on: usize) -> usize {
        // 0b11 = 3  log2_ceil(0b11) = 2 .. 2^2
        // 0b10 = 2 log2_ceil = 2 .. 2^1
        if on > 0 {
            helper(count + 1, on >> 1)
        } else {
            count
        }
    }

    helper(0, num)
}

/// Not meant to be directly used
#[macro_export]
macro_rules! enum_impl {
    (
        $(#[doc = $struct_doc:expr])*
        $(#[derive($($struct_der:ident),+)])?
        $enum_vis: vis $name: ident($default: ident){
            $(#[doc = $fst_field_doc:expr])*
            $fst_field: ident
            $(,
                $(#[doc = $field_doc:expr])*
                $field: ident
            )* $(,)?
        }
    ) => {

        #[repr(u8)]
        $(#[doc = $struct_doc])*
        $(#[derive($($struct_der),+)])?
        #[derive(Copy, Clone, Debug, PartialOrd, PartialEq)]
        $enum_vis enum $name {
            $(#[doc = $fst_field_doc])*
            $fst_field,
            $(
                $(#[doc = $field_doc])*
                $field
            ),*
        }

        unsafe impl bit_struct::BitCount for $name {
            const COUNT: usize = bit_struct::bits(bit_struct::count_idents!(0, [$($field),*]));
        }

        impl Default for $name {
            fn default() -> Self {
                $name::$default
            }
        }

        impl TryFrom<u8> for $name {

            type Error = ();

            fn try_from(value: u8) -> Result<$name, Self::Error> {
                let variants = [$name::$fst_field, $($name::$field),*];
                if (value as usize) < variants.len() {
                    Ok(variants[value as usize])
                } else {
                    Err(())
                }
            }
        }

        impl TryFrom<u16> for $name {

            type Error = ();

            fn try_from(value: u16) -> Result<$name, Self::Error> {
                $name::try_from(value as u8)
            }
        }

        impl TryFrom<u32> for $name {

            type Error = ();

            fn try_from(value: u32) -> Result<$name, Self::Error> {
                $name::try_from(value as u8)
            }
        }

        impl TryFrom<u64> for $name {

            type Error = ();

            fn try_from(value: u64) -> Result<$name, Self::Error> {
                $name::try_from(value as u8)
            }
        }

        impl TryFrom<u128> for $name {

            type Error = ();

            fn try_from(value: u128) -> Result<$name, Self::Error> {
                $name::try_from(value as u8)
            }
        }

        impl From<$name> for u8 {
            fn from(value: $name) -> u8 {
                value as u8
            }
        }

        impl From<$name> for u16 {
            fn from(value: $name) -> u16 {
                (value as u8) as u16
            }
        }

        impl From<$name> for u32 {
            fn from(value: $name) -> u32 {
                (value as u8) as u32
            }
        }
        impl From<$name> for u64 {
            fn from(value: $name) -> u64 {
                (value as u8) as u64
            }
        }

        impl From<$name> for u128 {
            fn from(value: $name) -> u128 {
                (value as u8) as u128
            }
        }


    };


    (
        $(#[doc = $struct_doc:expr])*
        $(#[derive($($struct_der:ident),+)])?
        $enum_vis: vis $name: ident {
            $(#[doc = $fst_field_doc:expr])*
            $fst_field: ident
            $(,
                $(#[doc = $field_doc:expr])*
                $field: ident
            )* $(,)?
        }
    ) => {
        #[repr(u8)]
        $(#[doc = $struct_doc])*
        $(#[derive($($struct_der),+)])?
        #[derive(Copy, Clone, Debug, PartialOrd, PartialEq)]
        $enum_vis enum $name {
            $(#[doc = $fst_field_doc])*
            $fst_field,
            $(
                $(#[doc = $field_doc])*
                $field
            ),*
        }

        impl Default for $name {
            fn default() -> Self {
                $name::$fst_field
            }
        }

        unsafe impl bit_struct::BitCount for $name {
            const COUNT: usize = bit_struct::bits(bit_struct::count_idents!(0, [$($field),*]));
        }


        impl TryFrom<u8> for $name {

            type Error = ();

            fn try_from(value: u8) -> Result<$name, Self::Error> {
                let variants = [$name::$fst_field, $($name::$field),*];
                if (value as usize) < variants.len() {
                    Ok(variants[value as usize])
                } else {
                    Err(())
                }
            }
        }

        impl TryFrom<u16> for $name {

            type Error = ();

            fn try_from(value: u16) -> Result<$name, Self::Error> {
                $name::try_from(value as u8)
            }
        }

        impl TryFrom<u32> for $name {

            type Error = ();

            fn try_from(value: u32) -> Result<$name, Self::Error> {
                $name::try_from(value as u8)
            }
        }

        impl TryFrom<u64> for $name {

            type Error = ();

            fn try_from(value: u64) -> Result<$name, Self::Error> {
                $name::try_from(value as u8)
            }
        }

        impl TryFrom<u128> for $name {

            type Error = ();

            fn try_from(value: u128) -> Result<$name, Self::Error> {
                $name::try_from(value as u8)
            }
        }

        impl From<$name> for u8 {
            fn from(value: $name) -> u8 {
                value as u8
            }
        }

        impl From<$name> for u16 {
            fn from(value: $name) -> u16 {
                (value as u8) as u16
            }
        }

        impl From<$name> for u32 {
            fn from(value: $name) -> u32 {
                (value as u8) as u32
            }
        }
        impl From<$name> for u64 {
            fn from(value: $name) -> u64 {
                (value as u8) as u64
            }
        }

        impl From<$name> for u128 {
            fn from(value: $name) -> u128 {
                (value as u8) as u128
            }
        }
    };
}

/// Create enums which have convenient TryFrom/From implementations. This makes using them with
/// the [bit_struct] macro much easier.
#[macro_export]
macro_rules! enums {
    (
        $(
        $(#[doc = $struct_doc:expr])*
        $(#[derive($($struct_der:ident),+)])?
        $enum_vis: vis $name: ident $(($enum_default: ident))? {
            $(#[doc = $fst_field_doc:expr])*
            $fst_field: ident
            $(,
                $(#[doc = $field_doc:expr])*
                $field: ident
            )* $(,)?
        }
        )+
    ) => {
        $(
        bit_struct::enum_impl!(
        $(#[doc = $struct_doc])*
        $(#[derive($($struct_der),+)])?
        $enum_vis $name $(($enum_default))?{
            $(#[doc = $fst_field_doc])*
            $fst_field
            $(,
                $(#[doc = $field_doc])*
                $field
            )*
        }
        );
        )+
    }
}
