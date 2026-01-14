//! `core::num::NonZero*` types.
use crate::{CborLen, Decode, Decoder, Encode, Encoder};

/// Possible errors when decoding non-zero values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Error<E> {
    /// The value is zero.
    Zero,
    /// Error decoding the value.
    Value(E),
}

impl<E: core::fmt::Display> core::fmt::Display for Error<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Zero => write!(f, "value is zero"),
            Error::Value(_) => write!(f, "non-zero value error"),
        }
    }
}

impl<E> From<E> for Error<E> {
    fn from(e: E) -> Self {
        Error::Value(e)
    }
}

impl<E: core::error::Error + 'static> core::error::Error for Error<E> {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Error::Zero => None,
            Error::Value(e) => Some(e),
        }
    }
}

macro_rules! impl_ {
    ($($t:ty)*) => {
        $(
            impl<'b> Decode<'b> for core::num::NonZero<$t> {
                type Error = Error<<$t as Decode<'b>>::Error>;

                fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
                    Self::new(Decode::decode(d)?).ok_or_else(|| Error::Zero)
                }
            }

            impl Encode for core::num::NonZero<$t> {
                fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
                    self.get().encode(e)
                }
            }

            impl CborLen for core::num::NonZero<$t> {
                fn cbor_len(&self) -> usize {
                    self.get().cbor_len()
                }
            }
        )*
    }
}

impl_! {
    u16 u32 u64 usize i8 i16 i32 i64 isize
}

impl<'b> Decode<'b> for core::num::NonZeroU8 {
    type Error = Error<super::Error>;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        super::U8::decode(d)?.0.try_into().map_err(|_| Error::Zero)
    }
}

impl Encode for core::num::NonZeroU8 {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        (self.get() as u64).encode(e)
    }
}

impl CborLen for core::num::NonZeroU8 {
    fn cbor_len(&self) -> usize {
        (self.get() as u64).cbor_len()
    }
}

#[cfg(test)]
mod tests {
    use crate::{Decode, test};
    use core::num::*;

    #[test]
    fn nonzero() {
        assert!(test(NonZeroU8::new(1).unwrap(), &[0x01]).unwrap());
        assert!(test(NonZeroU8::new(42).unwrap(), &[0x18, 0x2a]).unwrap());
        assert!(test(NonZeroU16::new(256).unwrap(), &[0x19, 0x01, 0x00]).unwrap());
        assert!(
            test(
                NonZeroU32::new(65536).unwrap(),
                &[0x1a, 0x00, 0x01, 0x00, 0x00]
            )
            .unwrap()
        );
        assert!(test(NonZeroU64::new(1).unwrap(), &[0x01]).unwrap());

        assert!(test(NonZeroI8::new(-1).unwrap(), &[0x20]).unwrap());
        assert!(test(NonZeroI16::new(-256).unwrap(), &[0x38, 0xff]).unwrap());
        assert!(test(NonZeroI32::new(100).unwrap(), &[0x18, 0x64]).unwrap());
        assert!(test(NonZeroI64::new(-1).unwrap(), &[0x20]).unwrap());
    }

    #[test]
    fn zero() {
        use crate::Decoder;

        let cbor = [0x00];
        let err = NonZeroU8::decode(&mut Decoder(&cbor)).unwrap_err();
        assert_eq!(err, super::Error::Zero);

        let err = NonZeroU16::decode(&mut Decoder(&cbor)).unwrap_err();
        assert_eq!(err, super::Error::Zero);

        let err = NonZeroI32::decode(&mut Decoder(&cbor)).unwrap_err();
        assert_eq!(err, super::Error::Zero);
    }
}
