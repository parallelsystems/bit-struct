use bit_struct::{bit_struct, enum_impl, enums};

enums!(
    Mode { Zero, One }
    ModeTwo(One) { Zero, One }
);

bit_struct!(
    /// Abc struct
    struct Abc(u16){
        /// Gets the mode
        mode(15,15): Mode,
        count(1,5): u8,
    }

    struct FullCount(u16){
        count(0,15): u16,
    }

    struct TooManyBits(u16) {
        count(0,15): u8
    }

);

#[test]
fn test_defaults() {
    assert_eq!(Mode::default(), Mode::Zero);
    assert_eq!(ModeTwo::default(), ModeTwo::One);
}

#[test]
fn test_abc() {
    let mut abc = Abc(0);

    assert_eq!(abc.mode().get(), Ok(Mode::Zero));
    assert_eq!(abc.count().get(), Ok(0));

    abc.mode().set(Mode::One);
    abc.count().set(12);

    assert_eq!(abc.mode().get(), Ok(Mode::One));
    assert_eq!(abc.count().get(), Ok(12));
}

#[test]
fn test_full_count() {
    let mut full = FullCount(0);
    assert_eq!(full.count().get(), Ok(0));
    full.count().set(u16::MAX);
    assert_eq!(full.count().get(), Ok(u16::MAX));
}

#[test]
fn test_too_many_bits() {
    let mut too_many = TooManyBits(u16::MAX);
    assert!(too_many.count().get().is_err());

    too_many.count().set(u8::MAX);
    assert_eq!(too_many.count().get(), Ok(u8::MAX));
}
