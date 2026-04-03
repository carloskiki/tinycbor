//! Maintain the encoded bytes that represent a value.
//!
//! Utilities for maintaining the encoded bytes of a value, which can be used to avoid re-encoding
//! the value.

use crate::{CborLen, Decode, Encode};

/// A value with its encoded bytes.
///
/// The value and bytes can be accessed with the [`AsRef`] and [`From`] implementations.
///
/// Modification of the value or the bytes is unsupported because the bytes must always match the
/// value. This is a requirement for [`With`] to implement [`Encode`] and [`CborLen`] efficiently,
/// by reusing the bytes.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct With<'a, T> {
    value: T,
    bytes: &'a [u8],
}

impl<T> AsRef<T> for With<'_, T> {
    fn as_ref(&self) -> &T {
        &self.value
    }
}

impl<T> AsRef<[u8]> for With<'_, T> {
    fn as_ref(&self) -> &[u8] {
        self.bytes
    }
}

impl<'a, T> From<With<'a, T>> for (T, &'a [u8]) {
    fn from(With { value, bytes }: With<'a, T>) -> Self {
        (value, bytes)
    }
}

impl<T> Encode for With<'_, T>
where
    T: Encode,
{
    fn encode<W: embedded_io::Write>(&self, e: &mut crate::Encoder<W>) -> Result<(), W::Error> {
        e.0.write_all(self.bytes)
    }
}

impl<'a, T> Decode<'a> for With<'a, T>
where
    T: Decode<'a>,
{
    type Error = T::Error;

    fn decode(d: &mut crate::Decoder<'a>) -> Result<Self, Self::Error> {
        let bytes = d.0;
        let value = T::decode(d)?;
        let offset = d.0.as_ptr() as usize - bytes.as_ptr() as usize;
        Ok(With {
            value,
            bytes: &bytes[..offset],
        })
    }
}

impl<T> CborLen for With<'_, T>
where
    T: CborLen,
{
    fn cbor_len(&self) -> usize {
        self.bytes.len()
    }
}

/// `T` encoded as cbor bytes.
///
/// Compared to [`With`], the value `T` is not readily decoded. It can be accessed by decoding the
/// bytes with [`Self::decode`]. This is useful when a value needs to be passed around without
/// decoding it.
pub struct Lazy<B, T> {
    /// The encoded bytes.
    ///
    /// Note that since the value is not decoded, the bytes may be invalid.
    pub bytes: B,
    pub(crate) _phantom: core::marker::PhantomData<T>,
}

impl<B, T> Lazy<B, T> {
    /// Access the value by decoding it.
    pub fn decode<'a>(&'a self) -> Result<T, T::Error>
    where
        B: AsRef<[u8]>,
        T: Decode<'a>,
    {
        T::decode(&mut crate::Decoder(self.bytes.as_ref()))
    }
}

/// Create a new `Encoded` value from the given bytes.
impl<B, T> From<B> for Lazy<B, T> {
    fn from(bytes: B) -> Self {
        Self {
            bytes,
            _phantom: core::marker::PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Lazy, With};
    use crate::{Decode, Decoder};
    use alloc::{string::String, vec::Vec};

    const HELLO_CBOR: &[u8] = &[0x65, b'h', b'e', b'l', b'l', b'o', 0x00];

    #[test]
    fn borrow() {
        let with = With::<&str>::decode(&mut Decoder(HELLO_CBOR)).unwrap();
        let encoded = <With<'_, &str> as AsRef<[u8]>>::as_ref(&with);

        let lazy_slice = Lazy::<&[u8], &str>::from(encoded);
        assert_eq!(lazy_slice.decode().unwrap(), "hello");
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn owned() {
        let with = With::<String>::decode(&mut Decoder(HELLO_CBOR)).unwrap();
        let encoded = <With<'_, String> as AsRef<[u8]>>::as_ref(&with);

        let lazy_box = Lazy::<Box<[u8]>, String>::from(encoded.to_vec().into_boxed_slice());
        assert_eq!(lazy_box.decode().unwrap(), "hello");

        let lazy_vec = Lazy::<Vec<u8>, String>::from(encoded.to_vec());
        assert_eq!(lazy_vec.decode().unwrap(), "hello");
    }
}
