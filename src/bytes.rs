use crate::{
    BYTES, CborLen, Decode, Decoder, Encode, Encoder, InvalidHeader, Write,
    collections::{self, fixed},
    info_of,
    primitive::Error,
    type_of,
};

/// Decodes a definite-length byte string.
///
/// If you need to also support indefinite-length byte strings, consider using an allocated type
/// such as `Vec<u8>` or `Box<[u8]>`.
impl<'a, 'b> Decode<'b> for &'a [u8]
where
    'b: 'a,
{
    type Error = Error;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        let b = d.peek()?;
        if BYTES != type_of(b) || info_of(b) == 31 {
            return Err(Error::InvalidHeader(InvalidHeader));
        }
        let n = d.length()?;
        Ok(d.read_slice(n)?)
    }
}

impl Encode for [u8] {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        e.type_len(BYTES, self.len() as u64)?;
        e.put(self)
    }
}

impl CborLen for [u8] {
    fn cbor_len(&self) -> usize {
        let n = self.len();
        n.cbor_len() + n
    }
}

/// Decodes a byte string, supporting both definite-length and indefinite-length encodings.
#[cfg(feature = "alloc")]
impl<'a> Decode<'a> for alloc::vec::Vec<u8> {
    type Error = Error;

    fn decode(d: &mut Decoder<'a>) -> Result<Self, Self::Error> {
        let mut vec = alloc::vec::Vec::new();
        for slice in d.bytes_iter()? {
            let slice = slice?;
            vec.extend_from_slice(slice);
        }
        Ok(vec)
    }
}

#[cfg(feature = "alloc")]
impl Encode for alloc::vec::Vec<u8> {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        self.as_slice().encode(e)
    }
}

#[cfg(feature = "alloc")]
impl CborLen for alloc::vec::Vec<u8> {
    fn cbor_len(&self) -> usize {
        self.as_slice().cbor_len()
    }
}

/// Decodes a byte string, supporting both definite-length and indefinite-length encodings.
#[cfg(feature = "alloc")]
impl<'a> Decode<'a> for alloc::boxed::Box<[u8]> {
    type Error = Error;
    fn decode(d: &mut Decoder<'a>) -> Result<Self, Self::Error> {
        alloc::vec::Vec::<u8>::decode(d).map(|v| v.into_boxed_slice())
    }
}

/// Decodes a byte string, supporting only definite-length encodings.
impl<const N: usize> Decode<'_> for [u8; N] {
    type Error = collections::Error<fixed::Error<core::convert::Infallible>>;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        <&[u8; N] as Decode>::decode(d).copied()
    }
}

impl<'a, 'b, const N: usize> Decode<'b> for &'a [u8; N]
where
    'b: 'a,
{
    type Error = collections::Error<fixed::Error<core::convert::Infallible>>;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        let slice: &[u8] = Decode::decode(d)?;
        slice.try_into().map_err(|_| {
            if slice.len() < N {
                collections::Error::Element(fixed::Error::Missing)
            } else {
                collections::Error::Element(fixed::Error::Surplus)
            }
        })
    }
}

impl<const N: usize> Encode for [u8; N] {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        self.as_slice().encode(e)
    }
}

impl<const N: usize> CborLen for [u8; N] {
    fn cbor_len(&self) -> usize {
        self.as_slice().cbor_len()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        InvalidHeader,
        collections::{self, fixed},
        test,
    };

    #[test]
    fn empty() {
        assert!(test::<&[u8]>(&[], &[0x40]).unwrap());
        assert!(test::<[u8; _]>([], &[0x40]).unwrap());
        #[cfg(feature = "alloc")]
        {
            use alloc::{boxed::Box, vec::Vec};

            assert!(test::<Vec<u8>>(Vec::new(), &[0x40]).unwrap());
            assert!(test::<Box<[u8]>>(Box::new([]), &[0x40]).unwrap());
        }
    }

    #[test]
    fn definite() {
        let cbor = [0x45, 99, 243, 111, 255, 9];
        let result = [99, 243, 111, 255, 9];

        assert!(test::<&[u8]>(&result, &cbor).unwrap());
        assert!(test(result, &cbor).unwrap());

        #[cfg(feature = "alloc")]
        {
            use alloc::{boxed::Box, vec::Vec};

            assert!(test(Vec::from(result), &cbor).unwrap());
            assert!(test(Box::<[u8]>::from(result), &cbor).unwrap());
        }
    }

    #[test]
    fn indefinite() {
        let err = test::<&[u8]>(&[], &[0x5F, 0x40, 0xFF]).unwrap_err();
        assert_eq!(err, crate::primitive::Error::InvalidHeader(InvalidHeader));
        let err = test::<[u8; 0]>([], &[0x5F, 0x40, 0xFF]).unwrap_err();
        assert_eq!(
            err,
            collections::Error::Malformed(crate::primitive::Error::InvalidHeader(InvalidHeader))
        );

        #[cfg(feature = "alloc")]
        {
            use alloc::{boxed::Box, vec::Vec};
            let cbor = [0x5f, 0x44, 1, 110, 255, 3, 0xff];
            let result = [1, 110, 255, 3];

            assert!(!test(Vec::from(result), &cbor).unwrap());
            assert!(!test(Box::<[u8]>::from(result), &cbor).unwrap());

            let cbor = [0x5f, 0x40, 0x40, 0x40, 0x40, 0xff];

            assert!(!test::<Vec<u8>>(Vec::new(), &cbor).unwrap());
            assert!(!test::<Box<[u8]>>(Box::new([]), &cbor).unwrap());

            let cbor = [0x5f, 0xff];

            assert!(!test::<Vec<u8>>(Vec::new(), &cbor).unwrap());
            assert!(!test::<Box<[u8]>>(Box::new([]), &cbor).unwrap());
        }
    }

    #[test]
    fn length_mismatch() {
        let err = test::<[u8; 3]>([1, 2, 3], &[0x42, 1, 2]).unwrap_err();
        assert_eq!(err, collections::Error::Element(fixed::Error::Missing));
        let err = test::<[u8; 2]>([1, 2], &[0x43, 1, 2, 3]).unwrap_err();
        assert_eq!(err, collections::Error::Element(fixed::Error::Surplus));
    }
}
