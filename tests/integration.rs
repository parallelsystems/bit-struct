use bit_struct::*;

enums!(
    /// A doc comment
    pub ModeA(Two) { Zero, One, Two }
    pub ModeB(One) { Zero, One, Two }
    pub ModeC(Zero) { Zero, One, Two }
    ModeD { Zero, One, Two }
    OrderA {A, B}
    OrderB(B) {A, B}
);

bit_struct!(
    /// Abc struct
    #[derive(Default)]
    struct Abc(u16){
        mode: ModeA,
        _padding: u4,
        count: u2,
    }

    struct FullCount(u16){
        count: u16,
    }

    struct NonCoreBase(u24){
        count: u16,
        next: u8,
    }

    struct Bools(u24){
        flag_a: bool,
        flag_b: bool,
    }
);

#[test]
fn test_bools() {
    let mut bools = Bools::of_defaults();
    assert_eq!(bools.flag_a().get(), false);
    assert_eq!(bools.flag_b().get(), false);

    bools.flag_a().set(true);
    assert_eq!(bools.flag_a().get(), true);
    assert_eq!(bools.flag_b().get(), false);

    bools.flag_a().set(false);
    bools.flag_b().set(true);
    assert_eq!(bools.flag_a().get(), false);
    assert_eq!(bools.flag_b().get(), true);

    bools.flag_a().set(true);
    bools.flag_b().set(true);
    assert_eq!(bools.flag_a().get(), true);
    assert_eq!(bools.flag_b().get(), true);
}

#[test]
fn test_round_trip_bytes() {
    {
        let num = u24!(0x04D3);

        let bytes = num.to_be_bytes();
        assert_eq!(bytes, [0x0, 0x4, 0xD3]);

        let num_cloned = u24::from_be_bytes(bytes);

        assert_eq!(num, num_cloned);
    }

    {
        let num = u24!(1235);
        let bytes = num.to_le_bytes();
        let num_cloned = u24::from_le_bytes(bytes);

        assert_eq!(num, num_cloned);
    }
}

#[test]
fn test_non_core_base() {
    let mut non_core_base = NonCoreBase::new(123, 67);

    let count = non_core_base.count().get();
    assert_eq!(count, 123);

    let next = non_core_base.next().get();
    assert_eq!(next, 67);

    let raw = non_core_base.raw();

    let circle = NonCoreBase::try_from(raw).unwrap();
    assert_eq!(circle, non_core_base)
}

#[test]
fn test_full_count() {
    let full_count = FullCount::new(124);
    assert_eq!(full_count.raw(), 124);
}

#[test]
fn test_of_defaults() {
    let full_count = FullCount::of_defaults();
    assert_eq!(full_count.raw(), 0);
}

#[test]
fn test_toggle() {
    let v = u1::TRUE;
    assert_eq!(v, u1::TRUE);
    assert_eq!(v.toggle(), u1::FALSE);
    assert_eq!(v.toggle().toggle(), u1::TRUE);
}

#[test]
fn test_enum_intos() {
    macro_rules! intos {
        ($enum_var: ty, $($kind: ty),*) => {
            $(
            assert_eq!(<$kind>::from(<$enum_var>::Zero), 0);
            assert_eq!(<$kind>::from(<$enum_var>::One), 1);
            assert_eq!(<$kind>::from(<$enum_var>::Two), 2);
            )*
        };
    }

    intos!(ModeA, u8, u16, u32, u64, u128);
    intos!(ModeD, u8, u16, u32, u64, u128);
}

#[test]
fn test_enum_defaults() {
    // default is manually set to last
    assert_eq!(ModeA::default(), ModeA::Two);
    assert_eq!(ModeB::default(), ModeB::One);
    assert_eq!(ModeC::default(), ModeC::Zero);
    assert_eq!(ModeD::default(), ModeD::Zero);

    assert_eq!(OrderA::default(), OrderA::A);
    assert_eq!(OrderB::default(), OrderB::B);
}

#[test]
fn test_bit_struct_defaults() {
    let mut abc = Abc::default();
    assert_eq!(abc.count().get(), u2!(0));
    assert_eq!(abc.mode().get(), ModeA::Two);
}

#[test]
fn test_bit_struct_debug() {
    let abc = Abc::default();
    assert_eq!(
        format!("{:?}", abc),
        "Abc { mode: Two, _padding: 0, count: 0 }"
    );
}

#[test]
fn test_bit_struct_raw_values() {
    let mut abc = Abc::default();
    abc.mode().set(ModeA::One); // 0b01
    abc.count().set(u2!(0b10));

    // 0b 0100 0010 0000 0000
    // 0x    4    2    0    0
    // 0x4200
    assert_eq!(abc.raw(), 0x4200);

    let eq_abc = unsafe { Abc::from_unchecked(0x4200) };

    assert_eq!(eq_abc.raw(), 0x4200);
    assert_eq!(eq_abc, abc);
}

#[test]
fn test_new_signed_types() {
    assert_eq!(i2::MAX, 1);
    assert_eq!(i2::MIN, -2);

    assert_eq!(i2!(-2).inner_raw(), 0b10);
    assert_eq!(i2!(-1).inner_raw(), 0b11);
    assert_eq!(i2!(0).inner_raw(), 0b00);
    assert_eq!(i2!(1).inner_raw(), 0b01);

    assert_eq!(i2!(-2).signed(), -2);
    assert_eq!(i2!(-1).signed(), -1);
    assert_eq!(i2!(0).signed(), 0);
    assert_eq!(i2!(1).signed(), 1);

    assert_eq!(i3!(-4).inner_raw(), 0b100);
    assert_eq!(i3!(-3).inner_raw(), 0b101);
    assert_eq!(i3!(-2).inner_raw(), 0b110);
    assert_eq!(i3!(-1).inner_raw(), 0b111);
    assert_eq!(i3!(0).inner_raw(), 0b000);
    assert_eq!(i3!(1).inner_raw(), 0b001);
    assert_eq!(i3!(2).inner_raw(), 0b010);
    assert_eq!(i3!(3).inner_raw(), 0b011);

    assert_eq!(i3!(-4).inner_raw(), 0b100);
    assert_eq!(i3!(-3).inner_raw(), 0b101);
    assert_eq!(i3!(-2).inner_raw(), 0b110);
    assert_eq!(i3!(-1).inner_raw(), 0b111);
    assert_eq!(i3!(0).inner_raw(), 0b000);
    assert_eq!(i3!(1).inner_raw(), 0b001);
    assert_eq!(i3!(2).inner_raw(), 0b010);
    assert_eq!(i3!(3).inner_raw(), 0b011);

    assert!(i3::new(-5).is_none());
    assert!(i3::new(-4).is_some());
    assert!(i3::new(-3).is_some());
    assert!(i3::new(-2).is_some());
    assert!(i3::new(-1).is_some());
    assert!(i3::new(0).is_some());
    assert!(i3::new(1).is_some());
    assert!(i3::new(2).is_some());
    assert!(i3::new(3).is_some());
    assert!(i3::new(4).is_none());
}

#[test]
fn test_new_unsigned_types() {
    assert_eq!(u1!(0).inner(), 0b0);
    assert_eq!(u1!(1).inner(), 0b1);

    assert_eq!(u8::from(u1!(0)), 0b0);
    assert_eq!(u8::from(u1!(1)), 0b1);
    assert_eq!(u32::from(u1!(0)), 0b0);
    assert_eq!(u32::from(u1!(1)), 0b1);
    assert_eq!(u128::from(u1!(0)), 0b0);
    assert_eq!(u128::from(u1!(1)), 0b1);

    assert_eq!(u1::try_from(0b0_u8).unwrap().inner(), 0);
    assert_eq!(u1::try_from(0b1_u8).unwrap().inner(), 1);
    assert!(u1::try_from(0b11_u8).is_err());

    assert_eq!(u2!(0).inner(), 0b00);
    assert_eq!(u2!(1).inner(), 0b01);
    assert_eq!(u2!(2).inner(), 0b10);
    assert_eq!(u2!(3).inner(), 0b11);
    assert_eq!(u2::try_from(0b0_u8).unwrap().inner(), 0);
    assert_eq!(u2::try_from(0b1_u8).unwrap().inner(), 1);
    assert_eq!(u2::try_from(0b10_u8).unwrap().inner(), 2);
    assert_eq!(u2::try_from(0b11_u8).unwrap().inner(), 3);
    assert!(u2::try_from(0b100_u8).is_err());

    assert_eq!(format!("{}", u1!(0)), "0");
    assert_eq!(format!("{}", u1!(1)), "1");

    assert_eq!(format!("{}", u2!(0)), "0");
    assert_eq!(format!("{}", u2!(1)), "1");
    assert_eq!(format!("{}", u2!(2)), "2");
    assert_eq!(format!("{}", u2!(3)), "3");
}

#[test]
fn test_valid_struct() {
    // 0b[AA]** **** **** ****
    // makes Abc valid where AA is 0b00, 0b01, 0b10
    // makes Abc invalid where AA is 0b11

    for first_bits in 0x0..0xF {
        let raw = first_bits << 12;
        let mode_a_bits = first_bits >> 2;
        let conversion = Abc::try_from(raw);
        let valid = match mode_a_bits {
            0b00 | 0b01 | 0b10 => conversion.is_ok(),
            0b11 => conversion.is_err(),
            _ => panic!("impossible"),
        };

        assert!(valid);
    }
}

#[test]
fn test_bits() {
    assert_eq!(bits(0b0), 0);

    assert_eq!(bits(0b1), 1);

    assert_eq!(bits(0b10), 2);
    assert_eq!(bits(0b11), 2);

    assert_eq!(bits(0b100), 3);
    assert_eq!(bits(0b101), 3);
    assert_eq!(bits(0b110), 3);
    assert_eq!(bits(0b111), 3);

    assert_eq!(bits(0b1000), 4);
    assert_eq!(bits(0b1001), 4);
    assert_eq!(bits(0b1010), 4);
    assert_eq!(bits(0b1011), 4);
    assert_eq!(bits(0b1100), 4);
    assert_eq!(bits(0b1101), 4);
    assert_eq!(bits(0b1110), 4);
    assert_eq!(bits(0b1111), 4);

    assert_eq!(bits(0b10000), 5);
}

#[test]
fn test_bit_struct_creation() {
    let mut abc = Abc::new(ModeA::Two, u4::default(), u2!(0b11));
    assert_eq!(abc.mode().get(), ModeA::Two);
    assert_eq!(abc._padding().get(), u4!(0));
    assert_eq!(abc.count().get(), u2!(0b11));
}

#[test]
fn fails() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile/*.rs");
}
