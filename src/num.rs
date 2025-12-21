//! Numeric types.
use crate::{CborLen, Decode, Decoder, Encode, Encoder, EndOfInput, InvalidHeader, SIGNED, SIMPLE, primitive};

pub mod nonzero;

/// Errors that can occur when decoding numbers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The encoded number is malformed.
    Malformed(primitive::Error),
    /// The decoded number could not be represented without overflow or precision loss.
    Narrowing,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Malformed(e) => write!(f, "primitive error: {}", e),
            Error::Narrowing => write!(f, "overflow or precision loss"),
        }
    }
}

impl From<primitive::Error> for Error {
    fn from(e: primitive::Error) -> Self {
        Error::Malformed(e)
    }
}

impl From<EndOfInput> for Error {
    fn from(e: EndOfInput) -> Self {
        Error::Malformed(primitive::Error::from(e))
    }
}

impl core::error::Error for Error {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Error::Malformed(e) => Some(e),
            Error::Narrowing => None,
        }
    }
}

/// CBOR integer type that covers values of [-2<sup>64</sup>, 2<sup>64</sup> - 1]
///
/// CBOR integers keep the sign bit in the major type so there is one extra bit
/// available for signed numbers compared to Rust's integer types. This type can
/// be used to encode and decode the full CBOR integer range.
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Int {
    /// `true` if the integer is negative.
    pub negative: bool,
    /// The bits of the integer.
    ///
    /// This is the value of the integer for positive integers, and the absolute value minus one
    /// for negative integers.
    pub bits: u64,
}

impl core::fmt::Display for Int {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", i128::from(*self))
    }
}

impl From<u8> for Int {
    fn from(i: u8) -> Self {
        Int::from(u64::from(i))
    }
}

impl From<u16> for Int {
    fn from(i: u16) -> Self {
        Int::from(u64::from(i))
    }
}

impl From<u32> for Int {
    fn from(i: u32) -> Self {
        Int::from(u64::from(i))
    }
}

impl From<u64> for Int {
    fn from(i: u64) -> Self {
        Int {
            negative: false,
            bits: i,
        }
    }
}

impl From<usize> for Int {
    fn from(i: usize) -> Self {
        Int::from(i as u64)
    }
}

impl From<i8> for Int {
    fn from(i: i8) -> Self {
        Int::from(i64::from(i))
    }
}

impl From<i16> for Int {
    fn from(i: i16) -> Self {
        Int::from(i64::from(i))
    }
}

impl From<i32> for Int {
    fn from(i: i32) -> Self {
        Int::from(i64::from(i))
    }
}

impl From<i64> for Int {
    fn from(i: i64) -> Self {
        if i.is_negative() {
            Int {
                negative: true,
                bits: (-1 - i) as u64,
            }
        } else {
            Int {
                negative: false,
                bits: i as u64,
            }
        }
    }
}

impl From<isize> for Int {
    fn from(i: isize) -> Self {
        Int::from(i64::try_from(i).unwrap())
    }
}

impl From<Int> for i128 {
    fn from(i: Int) -> Self {
        let j = i128::from(i.bits);
        if i.negative { -1 - j } else { j }
    }
}

impl Decode<'_> for Int {
    type Error = primitive::Error;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        Ok(match d.peek()? {
            0x00..=0x1b => Int {
                negative: false,
                bits: u64::decode(d)?,
            },
            _ => Int {
                negative: true,
                bits: match d.read()? {
                    n @ 0x20..=0x37 => n as u64 - 0x20,
                    0x38 => d.read().map(|n| n as u64)?,
                    0x39 => d.read_array().map(u16::from_be_bytes).map(|n| n as u64)?,
                    0x3a => d.read_array().map(u32::from_be_bytes).map(|n| n as u64)?,
                    0x3b => d.read_array().map(u64::from_be_bytes)?,
                    _ => return Err(primitive::Error::InvalidHeader(InvalidHeader)),
                },
            },
        })
    }
}

impl Encode for Int {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        if !self.negative {
            return self.bits.encode(e);
        }
        match self.bits {
            n @ 0..=0x17 => e.put(&[SIGNED | n as u8]),
            n @ 0x18..=0xff => e.put(&[SIGNED | 24, n as u8]),
            n @ 0x100..=0xffff => {
                e.put(&[SIGNED | 25])?;
                e.put(&(n as u16).to_be_bytes()[..])
            }
            n @ 0x1_0000..=0xffff_ffff => {
                e.put(&[SIGNED | 26])?;
                e.put(&(n as u32).to_be_bytes()[..])
            }
            n => {
                e.put(&[SIGNED | 27])?;
                e.put(&n.to_be_bytes()[..])
            }
        }
    }
}

impl CborLen for Int {
    fn cbor_len(&self) -> usize {
        self.bits.cbor_len()
    }
}

/// A newtype wrapper to handle `u8` as a CBOR number type.
///
/// Because rust does not yet have specialization, a newtype wrapper is needed to encode and decode
/// `u8` as a number type, rather than as a byte string.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct U8(pub u8);

impl From<U8> for u8 {
    fn from(u: U8) -> Self {
        u.0
    }
}

impl From<u8> for U8 {
    fn from(u: u8) -> Self {
        U8(u)
    }
}

impl AsRef<u8> for U8 {
    fn as_ref(&self) -> &u8 {
        &self.0
    }
}

impl AsMut<u8> for U8 {
    fn as_mut(&mut self) -> &mut u8 {
        &mut self.0
    }
}

impl AsRef<U8> for u8 {
    fn as_ref(&self) -> &U8 {
        // Safety: U8 is #[repr(transparent)] over u8
        unsafe { &*(self as *const u8 as *const U8) }
    }
}

impl AsMut<U8> for u8 {
    fn as_mut(&mut self) -> &mut U8 {
        // Safety: U8 is #[repr(transparent)] over u8
        unsafe { &mut *(self as *mut u8 as *mut U8) }
    }
}

impl Decode<'_> for U8 {
    type Error = Error;
    fn decode(d: &mut Decoder<'_>) -> Result<Self, Error> {
        u64::decode(d)?
            .try_into()
            .map(U8)
            .map_err(|_| Error::Narrowing)
    }
}

impl Encode for U8 {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        (self.0 as u64).encode(e)
    }
}

impl CborLen for U8 {
    fn cbor_len(&self) -> usize {
        (self.0 as u64).cbor_len()
    }
}

macro_rules! decode_unsigned {
    ($t:ident) => {
        impl<'b> Decode<'b> for $t {
            type Error = Error;
            fn decode(d: &mut Decoder<'b>) -> Result<Self, Error> {
                u64::decode(d)?.try_into().map_err(|_| Error::Narrowing)
            }
        }
    };
}

macro_rules! encode_unsigned {
    ($t:ident) => {
        impl Encode for $t {
            fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
                (*self as u64).encode(e)
            }
        }

        impl CborLen for $t {
            fn cbor_len(&self) -> usize {
                (*self as u64).cbor_len()
            }
        }
    };
}

macro_rules! impl_unsigned {
    ($($t:ident)*) => {
        $(
            decode_unsigned! { $t }

            encode_unsigned! { $t }
        )*
    }
}

impl_unsigned!(u16 u32);

impl Decode<'_> for u64 {
    type Error = primitive::Error;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        let value = match d.read()? {
            n @ 0..=0x17 => Ok(u64::from(n)),
            0x18 => d.read().map(u64::from),
            0x19 => d.read_array().map(u16::from_be_bytes).map(u64::from),
            0x1a => d.read_array().map(u32::from_be_bytes).map(u64::from),
            0x1b => d.read_array().map(u64::from_be_bytes),
            _ => return Err(primitive::Error::InvalidHeader(InvalidHeader)),
        }?;
        Ok(value)
    }
}

impl Encode for u64 {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        match self {
            0..=0x17 => e.put(&[*self as u8]),
            0x18..=0xff => e.put(&[24, *self as u8]),
            0x100..=0xffff => {
                e.put(&[25])?;
                e.put(&(*self as u16).to_be_bytes()[..])
            }
            0x1_0000..=0xffff_ffff => {
                e.put(&[26])?;
                e.put(&(*self as u32).to_be_bytes()[..])
            }
            _ => {
                e.put(&[27])?;
                e.put(&self.to_be_bytes()[..])
            }
        }
    }
}

impl CborLen for u64 {
    fn cbor_len(&self) -> usize {
        match self {
            0..=0x17 => 1,
            0x18..=0xff => 2,
            0x100..=0xffff => 3,
            0x1_0000..=0xffff_ffff => 5,
            _ => 9,
        }
    }
}

// if we have a less than 64-bit pointer width, usize may overflow
#[cfg(any(target_pointer_width = "16", target_pointer_width = "32"))]
decode_unsigned!(usize);

// If we have 64-bit pointer width, `usize` can be decoded from u64 without overflow.
#[cfg(target_pointer_width = "64")]
impl Decode<'_> for usize {
    type Error = primitive::Error;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        u64::decode(d).map(|n| n as usize)
    }
}

encode_unsigned!(usize);

impl Decode<'_> for u128 {
    type Error = primitive::Error;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        u64::decode(d).map(u128::from)
    }
}

macro_rules! impl_signed {
    ($($t:ident)*) => {
        $(
            impl<'b> Decode<'b> for $t {
                type Error = Error;
                fn decode(d: &mut Decoder<'b>) -> Result<Self, Error> {
                    i128::from(crate::num::Int::decode(d)?)
                        .try_into()
                        .map_err(|_| Error::Narrowing)
                }
            }

            impl Encode for $t {
                fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
                    crate::num::Int::from(*self).encode(e)
                }
            }

            impl CborLen for $t {
                fn cbor_len(&self) -> usize {
                    crate::num::Int::from(*self).cbor_len()
                }
            }
        )*
    }
}

impl_signed!(i8 i16 i32 i64 isize);

impl Decode<'_> for i128 {
    type Error = primitive::Error;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        Int::decode(d).map(i128::from)
    }
}

impl Decode<'_> for core::sync::atomic::AtomicBool {
    type Error = primitive::Error;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        let value = bool::decode(d)?;
        Ok(core::sync::atomic::AtomicBool::new(value))
    }
}

impl Decode<'_> for core::sync::atomic::AtomicU8 {
    type Error = Error;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        let value = U8::decode(d)?.0;
        Ok(core::sync::atomic::AtomicU8::new(value))
    }
}

macro_rules! decode_atomic {
    ($($prim:ty, $t:ty)*) => {
        $(
            impl<'b> Decode<'b> for $t {
                type Error = <$prim as Decode<'b>>::Error;
                fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
                    <$prim>::decode(d).map(<$t>::new)
                }
            }
        )*
    }
}

#[cfg(target_has_atomic = "8")]
decode_atomic! {
    i8, core::sync::atomic::AtomicI8
}

#[cfg(target_has_atomic = "16")]
decode_atomic! {
    u16, core::sync::atomic::AtomicU16
    i16, core::sync::atomic::AtomicI16
}

#[cfg(target_has_atomic = "32")]
decode_atomic! {
    u32, core::sync::atomic::AtomicU32
    i32, core::sync::atomic::AtomicI32
}

#[cfg(target_has_atomic = "64")]
decode_atomic! {
    u64, core::sync::atomic::AtomicU64
    i64, core::sync::atomic::AtomicI64
}

#[cfg(target_has_atomic = "ptr")]
decode_atomic! {
    usize, core::sync::atomic::AtomicUsize
    isize, core::sync::atomic::AtomicIsize
}

/// Taken from `half` crate https://github.com/VoidStarKat/half-rs/blob/v2.7.1/src/binary16/arch.rs#L685-L729
const fn f16_to_f32(i: u16) -> f32 {
    // Check for signed zero
    if i & 0x7FFFu16 == 0 {
        return f32::from_bits((i as u32) << 16);
    }

    let half_sign = (i & 0x8000u16) as u32;
    let half_exp = (i & 0x7C00u16) as u32;
    let half_man = (i & 0x03FFu16) as u32;

    // Check for an infinity or NaN when all exponent bits set
    if half_exp == 0x7C00u32 {
        // Check for signed infinity if mantissa is zero
        if half_man == 0 {
            return f32::from_bits((half_sign << 16) | 0x7F80_0000u32);
        } else {
            // NaN, keep current mantissa but also set most significiant mantissa bit
            return f32::from_bits((half_sign << 16) | 0x7FC0_0000u32 | (half_man << 13));
        }
    }

    // Calculate single-precision components with adjusted exponent
    let sign = half_sign << 16;
    // Unbias exponent
    let unbiased_exp = ((half_exp as i32) >> 10) - 15;

    // Check for subnormals, which will be normalized by adjusting exponent
    if half_exp == 0 {
        // Calculate how much to adjust the exponent by
        let e = (half_man as u16).leading_zeros() - 6;

        // Rebias and adjust exponent
        let exp = (127 - 15 - e) << 23;
        let man = (half_man << (14 + e)) & 0x7F_FF_FFu32;
        return f32::from_bits(sign | exp | man);
    }

    // Rebias exponent for a normalized normal
    let exp = ((unbiased_exp + 127) as u32) << 23;
    let man = (half_man & 0x03FFu32) << 13;
    f32::from_bits(sign | exp | man)
}

/// Taken from `half` crate https://github.com/VoidStarKat/half-rs/blob/v2.7.1/src/binary16/arch.rs#L556-L614
///
/// Modified to also return whether the conversion was lossless.
const fn f32_to_f16(value: f32) -> (u16, bool) {
    let x: u32 = value.to_bits();

    // Extract IEEE754 components
    let sign = x & 0x8000_0000u32;
    let exp = x & 0x7F80_0000u32;
    let man = x & 0x007F_FFFFu32;

    // If exp and man are both 0, it is zero.
    if (x & 0x7FFF_FFFFu32) == 0 {
        return ((sign >> 16) as u16, true);
    }

    // Check for all exponent bits being set, which is Infinity or NaN
    if exp == 0x7F80_0000u32 {
        // Set mantissa MSB for NaN (and also keep shifted mantissa bits)
        let nan_bit = if man == 0 { 0 } else { 0x0200u32 };
        // Lossless if mantissa is zero (infinity)
        return (
            ((sign >> 16) | 0x7C00u32 | nan_bit | (man >> 13)) as u16,
            man == 0,
        );
    }

    // The number is normalized, start assembling half precision version
    let half_sign = sign >> 16;
    // Unbias the exponent, then bias for half precision
    let unbiased_exp = ((exp >> 23) as i32) - 127;
    let half_exp = unbiased_exp + 15;

    // Check for exponent overflow, return +infinity
    if half_exp >= 0x1F {
        return ((half_sign | 0x7C00u32) as u16, false);
    }

    // Check for underflow
    if half_exp <= 0 {
        // Check mantissa for what we can do
        if 14 - half_exp > 24 {
            // No rounding possibility, so this is a full underflow, return signed zero
            // Already handled 0 above, so this is not lossless
            return (half_sign as u16, false);
        }
        // Don't forget about hidden leading mantissa bit when assembling mantissa
        let man = man | 0x0080_0000u32;
        let shift = 14 - half_exp;
        let half_man = man >> shift;
        // Check for lost bits to determine if lossless
        let lost_mask = (1 << shift) - 1;
        let is_lossless = (man & lost_mask) == 0;

        // Check for rounding (see comment above functions)
        let round_bit = 1 << (shift - 1);
        if (man & round_bit) != 0 && (man & (3 * round_bit - 1)) != 0 {
            return ((half_sign | (half_man + 1)) as u16, false);
        }
        // No exponent for subnormals
        return ((half_sign | half_man) as u16, is_lossless);
    }

    // Rebias the exponent
    let half_exp = (half_exp as u32) << 10;
    let half_man = man >> 13;
    // Check for rounding (see comment above functions)
    let round_bit = 0x0000_1000u32;
    if (man & round_bit) != 0 && (man & (3 * round_bit - 1)) != 0 {
        // Round it
        (((half_sign | half_exp | half_man) + 1) as u16, false)
    } else {
        (
            (half_sign | half_exp | half_man) as u16,
            (man & 0x1FFF) == 0,
        )
    }
}

impl Decode<'_> for f32 {
    type Error = Error;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        Ok(match d.read()? {
            0xf9 => f16_to_f32(d.read_array().map(u16::from_be_bytes)?),
            0xfa => f32::from_be_bytes(d.read_array()?),
            0xfb => {
                let double = f64::from_be_bytes(d.read_array()?);
                let narrowed = double as f32;
                if narrowed as f64 != double {
                    return Err(Error::Narrowing);
                }
                narrowed
            }
            _ => return Err(Error::Malformed(primitive::Error::InvalidHeader(InvalidHeader))),
        })
    }
}

impl Encode for f32 {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        let (half, lossless) = f32_to_f16(*self);
        if lossless {
            e.put(&[SIMPLE | 25])?;
            return e.put(&half.to_be_bytes()[..]);
        }
        e.put(&[SIMPLE | 26])?;
        e.put(&self.to_be_bytes()[..])
    }
}

impl CborLen for f32 {
    fn cbor_len(&self) -> usize {
        if let (_, true) = f32_to_f16(*self) {
            3
        } else {
            5
        }
    }
}

impl Decode<'_> for f64 {
    type Error = primitive::Error;

    fn decode(d: &mut Decoder<'_>) -> Result<f64, Self::Error> {
        match d.read()? {
            0xf9 => {
                let half = d.read_array().map(u16::from_be_bytes)?;
                let float = f16_to_f32(half);
                Ok(f64::from(float))
            }
            0xfa => Ok(f32::from_be_bytes(d.read_array()?).into()),
            0xfb => Ok(f64::from_be_bytes(d.read_array()?)),
            _ => Err(primitive::Error::InvalidHeader(InvalidHeader)),
        }
    }
}

impl Encode for f64 {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        let float = *self as f32;
        if float as f64 != *self {
            e.put(&[SIMPLE | 27])?;
            return e.put(&self.to_be_bytes()[..]);
        }
        let (half, lossless) = f32_to_f16(float);
        if lossless {
            e.put(&[SIMPLE | 25])?;
            return e.put(&half.to_be_bytes()[..]);
        }
        e.put(&[SIMPLE | 26])?;
        e.put(&float.to_be_bytes()[..])
    }
}

impl CborLen for f64 {
    fn cbor_len(&self) -> usize {
        let float = *self as f32;
        if float as f64 != *self {
            9
        } else if let (_, true) = f32_to_f16(float) {
            3
        } else {
            5
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{test, Decode};

    #[test]
    fn u64() {
        // Values 0-23 should encode in 1 byte
        assert!(test::<u64>(0, &[0x00]).unwrap());
        assert!(test::<u64>(1, &[0x01]).unwrap());
        assert!(test::<u64>(23, &[0x17]).unwrap());
        // Values 24-255 should encode in 2 bytes
        assert!(test::<u64>(24, &[0x18, 0x18]).unwrap());
        assert!(test::<u64>(255, &[0x18, 0xff]).unwrap());
        // Values 256-65535 should encode in 3 bytes
        assert!(test::<u64>(256, &[0x19, 0x01, 0x00]).unwrap());
        assert!(test::<u64>(65535, &[0x19, 0xff, 0xff]).unwrap());
        // Values 65536-4294967295 should encode in 5 bytes
        assert!(test::<u64>(65536, &[0x1a, 0x00, 0x01, 0x00, 0x00]).unwrap());
        assert!(test::<u64>(4294967295, &[0x1a, 0xff, 0xff, 0xff, 0xff]).unwrap());
        // Values > 4294967295 should encode in 9 bytes
        assert!(test::<u64>(4294967296, &[0x1b, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00]).unwrap());
        assert!(test::<u64>(u64::MAX, &[0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]).unwrap());
    }

    #[test]
    fn i64() {
        assert!(test::<i64>(0, &[0x00]).unwrap());
        assert!(test::<i64>(23, &[0x17]).unwrap());
        assert!(test::<i64>(i64::MAX, &[0x1b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]).unwrap());
        // Negative values use major type 1
        assert!(test::<i64>(-1, &[0x20]).unwrap());
        assert!(test::<i64>(-24, &[0x37]).unwrap());
        assert!(test::<i64>(-25, &[0x38, 0x18]).unwrap());
        assert!(test::<i64>(-256, &[0x38, 0xff]).unwrap());
        assert!(test::<i64>(i64::MIN, &[0x3b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]).unwrap());
    }

    #[test]
    fn int_full_range() {
        // Test Int type with full CBOR integer range
        let pos_max = Int { negative: false, bits: u64::MAX };
        assert!(test::<Int>(pos_max, &[0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]).unwrap());

        let neg_max = Int { negative: true, bits: u64::MAX };
        assert!(test::<Int>(neg_max, &[0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]).unwrap());
    }

    #[test]
    fn int_out_of_range() {
        // -(2^64 - 1) = -18446744073709551615 can only be decoded into Int
        use crate::Decoder;
        let cbor = [0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff];
        
        // Should work for Int
        assert!(Int::decode(&mut Decoder(&cbor)).is_ok());
        
        // Should fail for i64 due to narrowing
        let err = i64::decode(&mut Decoder(&cbor)).unwrap_err();
        assert_eq!(err, Error::Narrowing);
    }

    #[test]
    fn narrowing() {
        use crate::Decoder;
        
        // Value too large for u32
        let cbor = [0x1b, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00];
        let err = u32::decode(&mut Decoder(&cbor)).unwrap_err();
        assert_eq!(err, Error::Narrowing);
        
        // Value too large for u16
        let cbor = [0x19, 0xff, 0xff];
        assert!(u16::decode(&mut Decoder(&cbor)).is_ok());
        
        let cbor = [0x1a, 0x00, 0x01, 0x00, 0x00];
        let err = u16::decode(&mut Decoder(&cbor)).unwrap_err();
        assert_eq!(err, Error::Narrowing);
        
        // Value too large for i32
        let cbor = [0x1b, 0x00, 0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00];
        let err = i32::decode(&mut Decoder(&cbor)).unwrap_err();
        assert_eq!(err, Error::Narrowing);
        
        // Negative value too small for i32
        let cbor = [0x3b, 0x00, 0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00];
        let err = i32::decode(&mut Decoder(&cbor)).unwrap_err();
        assert_eq!(err, Error::Narrowing);
    }

    #[test]
    fn u8() {
        assert!(test(U8(0), &[0x00]).unwrap());
        assert!(test(U8(42), &[0x18, 0x2a]).unwrap());
        assert!(test(U8(255), &[0x18, 0xff]).unwrap());
        
        let cbor = [0x19, 0x01, 0x00]; // 256
        let err = U8::decode(&mut crate::Decoder(&cbor)).unwrap_err();
        assert_eq!(err, Error::Narrowing);
    }

    #[test]
    fn f32() {
        // Values that can be represented exactly in f16 should encode in 3 bytes
        assert!(test::<f32>(0.0, &[0xf9, 0x00, 0x00]).unwrap());
        assert!(test::<f32>(1.0, &[0xf9, 0x3c, 0x00]).unwrap());
        assert!(test::<f32>(-2.0, &[0xf9, 0xc0, 0x00]).unwrap());
        
        // Values requiring f32 precision should encode in 5 bytes
        let val = 1.1f32;
        let cbor = [0xfa, 0x3f, 0x8c, 0xcc, 0xcd];
        assert!(test::<f32>(val, &cbor).unwrap());
    }

    #[test]
    fn f64() {
        use crate::Decoder;
        // f64 can decode from all float formats
        let cbor_f16 = [0xf9, 0x3c, 0x00];
        assert_eq!(f64::decode(&mut Decoder(&cbor_f16)).unwrap(), 1.0);
        
        let cbor_f32 = [0xfa, 0x3f, 0x80, 0x00, 0x00];
        assert_eq!(f64::decode(&mut Decoder(&cbor_f32)).unwrap(), 1.0);
        
        let cbor_f64 = [0xfb, 0x3f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        assert_eq!(f64::decode(&mut Decoder(&cbor_f64)).unwrap(), 1.0);

        
        // f64 values that can be represented exactly in f16 should encode in 3 bytes
        assert!(test::<f64>(1.0, &[0xf9, 0x3c, 0x00]).unwrap());
        assert!(test::<f64>(-2.0, &[0xf9, 0xc0, 0x00]).unwrap());
        
        // Values requiring f64 precision should encode in 9 bytes
        let val = core::f64::consts::PI;
        let cbor = [0xfb, 0x40, 0x09, 0x21, 0xfb, 0x54, 0x44, 0x2d, 0x18];
        assert!(test::<f64>(val, &cbor).unwrap());
        let err = f32::decode(&mut Decoder(&cbor)).unwrap_err();
        assert_eq!(err, Error::Narrowing);
        
        // f64 values that fit in f32 but not f16 should encode in 5 bytes
        // Using a value that is exactly representable in f32
        let val = 3.00006103515625f64; // Exactly representable in f32
        let cbor = [0xfa, 0x40, 0x40, 0x01, 0x00];
        assert!(test::<f64>(val, &cbor).unwrap());
    }

    #[test]
    fn special_floats() {
        // Test special float values
        assert!(test::<f32>(f32::INFINITY, &[0xf9, 0x7c, 0x00]).unwrap());
        assert!(test::<f32>(f32::NEG_INFINITY, &[0xf9, 0xfc, 0x00]).unwrap());
        
        assert!(test::<f64>(f64::INFINITY, &[0xf9, 0x7c, 0x00]).unwrap());
        assert!(test::<f64>(f64::NEG_INFINITY, &[0xf9, 0xfc, 0x00]).unwrap());

        // NaN encoding (specific NaN bit pattern may vary)
        use crate::{Encoder, Decoder};
        let mut buf = Vec::new();
        f32::NAN.encode(&mut Encoder(&mut buf)).unwrap();
        assert!(f32::decode(&mut Decoder(&buf)).unwrap().is_nan());
        
        buf.clear();
        f64::NAN.encode(&mut Encoder(&mut buf)).unwrap();
        assert!(f64::decode(&mut Decoder(&buf)).unwrap().is_nan());
    }

    #[test]
    fn int() {
        // Test Int conversions
        assert_eq!(Int::from(42u64), Int { negative: false, bits: 42 });
        assert_eq!(Int::from(-1i64), Int { negative: true, bits: 0 });
        assert_eq!(Int::from(-100i64), Int { negative: true, bits: 99 });
        
        assert_eq!(i128::from(Int { negative: false, bits: 42 }), 42);
        assert_eq!(i128::from(Int { negative: true, bits: 0 }), -1);
        assert_eq!(i128::from(Int { negative: true, bits: 99 }), -100);
    }
}
