//! Tagged values.
use core::ops::Deref;

use embedded_io::Write;

use crate::{CborLen, Decode, Encode, Encoder, InvalidHeader, TAGGED, primitive, type_of};

/// Errors which can occur when decoding a tagged value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error<E> {
    /// The tagged value is malformed.
    Malformed(primitive::Error),
    /// The tag value does not match the expected tag.
    InvalidTag,
    /// An error occurred while decoding the inner value.
    Inner(E),
}

impl<E> Error<E> {
    /// Map a function on the inner error.
    pub fn map<O>(self, f: impl FnOnce(E) -> O) -> Error<O> {
        match self {
            Error::Malformed(e) => Error::Malformed(e),
            Error::InvalidTag => Error::InvalidTag,
            Error::Inner(e) => Error::Inner(f(e)),
        }
    }
}

impl<E: core::fmt::Display> core::fmt::Display for Error<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Malformed(e) => write!(f, "malformed tag: {}", e),
            Error::InvalidTag => write!(f, "invalid tag"),
            Error::Inner(e) => write!(f, "{}", e),
        }
    }
}

impl<E> From<primitive::Error> for Error<E> {
    fn from(e: primitive::Error) -> Self {
        Error::Malformed(e)
    }
}

impl<E> From<crate::EndOfInput> for Error<E> {
    fn from(e: crate::EndOfInput) -> Self {
        Error::Malformed(primitive::Error::EndOfInput(e))
    }
}

impl<E: core::error::Error + 'static> core::error::Error for Error<E> {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Error::Malformed(e) => Some(e),
            Error::InvalidTag => None,
            Error::Inner(e) => Some(e),
        }
    }
}

/// Statically tag a value.
///
/// # Example
///
/// ```
/// use tinycbor::{tag::{Tagged, IanaTag}, Decode, Decoder};
///
/// let input = [
///     0xc0, 0x74, 0x32, 0x30, 0x31, 0x33, 0x2d, 0x30,
///     0x33, 0x2d, 0x32, 0x31, 0x54, 0x32, 0x30, 0x3a,
///     0x30, 0x34, 0x3a, 0x30, 0x30, 0x5a
/// ];
///
/// let date_time: Tagged<&str, {IanaTag::DateTime as u64}> = Decode::decode(&mut Decoder(&input))?;
/// assert_eq!(date_time.0, "2013-03-21T20:04:00Z");
/// # Ok::<_, Box<dyn core::error::Error>>(())
/// ```
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Tagged<T: ?Sized, const N: u64>(pub T);

impl<T, const N: u64> Tagged<T, N> {
    /// Unwrap the tagged value.
    pub fn into(self) -> T {
        self.0
    }
}

impl<T, const N: u64> From<Tagged<T, N>> for Option<T> {
    fn from(val: Tagged<T, N>) -> Self {
        Some(val.0)
    }
}

impl<T, const N: u64> From<T> for Tagged<T, N> {
    fn from(val: T) -> Self {
        Self(val)
    }
}

impl<'a, T: ?Sized, const N: u64> From<&'a T> for &'a Tagged<T, N> {
    fn from(val: &T) -> Self {
        // SAFETY: Tagged is repr(transparent)
        unsafe { &*(val as *const T as *const Tagged<T, N>) }
    }
}

impl<T: ?Sized, const N: u64> AsRef<T> for Tagged<T, N> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: ?Sized, const N: u64> AsMut<T> for Tagged<T, N> {
    fn as_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T: ?Sized, const N: u64> Deref for Tagged<T, N> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: ?Sized, const N: u64> core::ops::DerefMut for Tagged<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a, T, const N: u64> Decode<'a> for Tagged<T, N>
where
    T: Decode<'a>,
{
    type Error = Error<T::Error>;

    fn decode(d: &mut crate::Decoder<'a>) -> Result<Self, Self::Error> {
        let b = d
            .peek()
            .map_err(|e| Error::Malformed(primitive::Error::from(e)))?;
        if TAGGED != type_of(b) {
            return Err(Error::Malformed(primitive::Error::InvalidHeader(
                InvalidHeader,
            )));
        }
        if d.unsigned().map_err(Error::Malformed)? != N {
            return Err(Error::InvalidTag);
        }

        T::decode(d).map(Tagged::<T, N>).map_err(Error::Inner)
    }
}

impl<const N: u64, T: Encode + ?Sized> Encode for Tagged<T, N> {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        e.type_len(TAGGED, N)?;
        self.0.encode(e)
    }
}

impl<const N: u64, T: CborLen + ?Sized> CborLen for Tagged<T, N> {
    fn cbor_len(&self) -> usize {
        N.cbor_len() + self.0.cbor_len()
    }
}

/// IANA registered tags.
///
/// See <https://www.iana.org/assignments/cbor-tags/cbor-tags.xhtml> for details.
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
#[repr(u64)]
#[non_exhaustive]
pub enum IanaTag {
    DateTime = 0x00,
    Timestamp = 0x01,
    PosBignum = 0x02,
    NegBignum = 0x03,
    Decimal = 0x04,
    Bigfloat = 0x05,
    ToBase64Url = 0x15,
    ToBase64 = 0x16,
    ToBase16 = 0x17,
    Cbor = 0x18,
    Uri = 0x20,
    Base64Url = 0x21,
    Base64 = 0x22,
    Regex = 0x23,
    Mime = 0x24,
    MultiDimArrayR = 0x28, // row-major order
    // Typed arrays (RFC 8746):
    HomogenousArray = 0x29,
    TypedArrayU8 = 0x40,
    TypedArrayU16B = 0x41,
    TypedArrayU32B = 0x42,
    TypedArrayU64B = 0x43,
    TypedArrayU8Clamped = 0x44,
    TypedArrayU16L = 0x45,
    TypedArrayU32L = 0x46,
    TypedArrayU64L = 0x47,
    TypedArrayI8 = 0x48,
    TypedArrayI16B = 0x49,
    TypedArrayI32B = 0x4a,
    TypedArrayI64B = 0x4b,
    TypedArrayI16L = 0x4d,
    TypedArrayI32L = 0x4e,
    TypedArrayI64L = 0x4f,
    TypedArrayF16B = 0x50,
    TypedArrayF32B = 0x51,
    TypedArrayF64B = 0x52,
    TypedArrayF128B = 0x53,
    TypedArrayF16L = 0x54,
    TypedArrayF32L = 0x55,
    TypedArrayF64L = 0x56,
    TypedArrayF128L = 0x57,
    MultiDimArrayC = 0x410, // column-major order
}

impl TryFrom<u64> for IanaTag {
    type Error = Unknown;

    fn try_from(t: u64) -> Result<Self, Self::Error> {
        match t {
            0x00 => Ok(Self::DateTime),
            0x01 => Ok(Self::Timestamp),
            0x02 => Ok(Self::PosBignum),
            0x03 => Ok(Self::NegBignum),
            0x04 => Ok(Self::Decimal),
            0x05 => Ok(Self::Bigfloat),
            0x15 => Ok(Self::ToBase64Url),
            0x16 => Ok(Self::ToBase64),
            0x17 => Ok(Self::ToBase16),
            0x18 => Ok(Self::Cbor),
            0x20 => Ok(Self::Uri),
            0x21 => Ok(Self::Base64Url),
            0x22 => Ok(Self::Base64),
            0x23 => Ok(Self::Regex),
            0x24 => Ok(Self::Mime),
            0x28 => Ok(Self::MultiDimArrayR),
            0x29 => Ok(Self::HomogenousArray),
            0x40 => Ok(Self::TypedArrayU8),
            0x41 => Ok(Self::TypedArrayU16B),
            0x42 => Ok(Self::TypedArrayU32B),
            0x43 => Ok(Self::TypedArrayU64B),
            0x44 => Ok(Self::TypedArrayU8Clamped),
            0x45 => Ok(Self::TypedArrayU16L),
            0x46 => Ok(Self::TypedArrayU32L),
            0x47 => Ok(Self::TypedArrayU64L),
            0x48 => Ok(Self::TypedArrayI8),
            0x49 => Ok(Self::TypedArrayI16B),
            0x4a => Ok(Self::TypedArrayI32B),
            0x4b => Ok(Self::TypedArrayI64B),
            0x4d => Ok(Self::TypedArrayI16L),
            0x4e => Ok(Self::TypedArrayI32L),
            0x4f => Ok(Self::TypedArrayI64L),
            0x50 => Ok(Self::TypedArrayF16B),
            0x51 => Ok(Self::TypedArrayF32B),
            0x52 => Ok(Self::TypedArrayF64B),
            0x53 => Ok(Self::TypedArrayF128B),
            0x54 => Ok(Self::TypedArrayF16L),
            0x55 => Ok(Self::TypedArrayF32L),
            0x56 => Ok(Self::TypedArrayF64L),
            0x57 => Ok(Self::TypedArrayF128L),
            0x410 => Ok(Self::MultiDimArrayC),
            _ => Err(Unknown),
        }
    }
}

/// Error indicating that a tag value is not a known IANA tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Unknown;

impl core::fmt::Display for Unknown {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "unknown IANA tag")
    }
}

impl core::error::Error for Unknown {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test;

    #[test]
    fn u32() {
        let cbor = [0xc0, 0x18, 0x2a];
        assert!(test::<Tagged<u32, 0>>(Tagged(42), &cbor).unwrap());
    }

    #[test]
    fn string() {
        let cbor = [
            0xc0, 0x74, 0x32, 0x30, 0x31, 0x33, 0x2d, 0x30, 0x33, 0x2d, 0x32, 0x31, 0x54, 0x32,
            0x30, 0x3a, 0x30, 0x34, 0x3a, 0x30, 0x30, 0x5a,
        ];
        assert!(test::<Tagged<&str, 0>>(Tagged("2013-03-21T20:04:00Z"), &cbor).unwrap());
    }

    #[test]
    fn bignum() {
        let cbor = [0xc2, 0x42, 0x01, 0x00];
        assert!(test::<Tagged<&[u8], 2>>(Tagged(&[0x01, 0x00]), &cbor).unwrap());
    }

    #[test]
    fn uri() {
        let cbor = [
            0xd8, 0x20, 0x6b, 0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x61, 0x2e, 0x62, 0x63,
        ];
        assert!(test::<Tagged<&str, 32>>(Tagged("http://a.bc"), &cbor).unwrap());
    }

    #[test]
    fn invalid() {
        use crate::Decoder;
        let cbor = [0xc0, 0x18, 0x2a];
        let err = <Tagged<u32, 1>>::decode(&mut Decoder(&cbor)).unwrap_err();
        assert_eq!(err, Error::InvalidTag);
    }

    #[test]
    fn untagged() {
        use crate::Decoder;
        let cbor = [0x18, 0x2a];
        let err = <Tagged<u32, 0>>::decode(&mut Decoder(&cbor)).unwrap_err();
        assert_eq!(
            err,
            Error::Malformed(primitive::Error::InvalidHeader(InvalidHeader))
        );
    }
}
