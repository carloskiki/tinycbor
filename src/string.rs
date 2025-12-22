//! Text.
use crate::{
    CborLen, Decode, Decoder, Encode, Encoder, InvalidHeader, TEXT, info_of, primitive, type_of,
};

/// Errors which can occur when decoding a UTF-8 string.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The string is malformed.
    Malformed(primitive::Error),
    /// The string is not valid UTF-8.
    Utf8(core::str::Utf8Error),
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Malformed(e) => write!(f, "{}", e),
            Error::Utf8(e) => write!(f, "{}", e),
        }
    }
}

impl From<primitive::Error> for Error {
    fn from(e: primitive::Error) -> Self {
        Error::Malformed(e)
    }
}

impl From<core::str::Utf8Error> for Error {
    fn from(e: core::str::Utf8Error) -> Self {
        Error::Utf8(e)
    }
}

impl From<crate::EndOfInput> for Error {
    fn from(e: crate::EndOfInput) -> Self {
        Error::Malformed(primitive::Error::EndOfInput(e))
    }
}

impl core::error::Error for Error {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Error::Malformed(e) => Some(e),
            Error::Utf8(e) => Some(e),
        }
    }
}

/// Decodes a definite-length string.
///
/// If you need to also support indefinite-length byte strings, consider using an allocated type
/// such as `String` or `Box<str>`.
impl<'a, 'b> Decode<'b> for &'a str
where
    'b: 'a,
{
    type Error = Error;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        let b = d.peek().map_err(primitive::Error::from)?;
        if TEXT != type_of(b) || info_of(b) == 31 {
            return Err(Error::Malformed(primitive::Error::InvalidHeader(
                InvalidHeader,
            )));
        }
        let n = d.length()?;
        let s = d.read_slice(n).map_err(primitive::Error::from)?;
        core::str::from_utf8(s).map_err(Error::from)
    }
}

impl Encode for str {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        e.type_len(TEXT, self.len() as u64)?;
        e.put(self.as_bytes())
    }
}

impl CborLen for str {
    fn cbor_len(&self) -> usize {
        let n = self.len();
        n.cbor_len() + n
    }
}

/// Decodes a byte string, supporting both definite-length and indefinite-length encodings.
#[cfg(feature = "alloc")]
impl<'a> Decode<'a> for alloc::string::String {
    type Error = Error;
    fn decode(d: &mut Decoder<'a>) -> Result<Self, Self::Error> {
        d.str_iter()?.collect()
    }
}

#[cfg(feature = "alloc")]
impl Encode for alloc::string::String {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        self.as_str().encode(e)
    }
}

#[cfg(feature = "alloc")]
impl CborLen for alloc::string::String {
    fn cbor_len(&self) -> usize {
        self.as_str().cbor_len()
    }
}

/// Decodes a byte string, supporting both definite-length and indefinite-length encodings.
#[cfg(feature = "alloc")]
impl<'a> Decode<'a> for alloc::boxed::Box<str> {
    type Error = Error;
    fn decode(d: &mut Decoder<'a>) -> Result<Self, Self::Error> {
        d.str_iter()?.collect()
    }
}

// === Decode Only Types ===

/// Decodes a definite-length string as a `&Path`.
///
/// If you need to also support indefinite-length byte strings, consider using an allocated type
/// such as `PathBuf` or `Box<Path>`.
#[cfg(feature = "std")]
impl<'b> Decode<'b> for &'b std::path::Path {
    type Error = Error;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Error> {
        <&'b str>::decode(d).map(std::path::Path::new)
    }
}

#[cfg(feature = "std")]
impl<'b> Decode<'b> for Box<std::path::Path> {
    type Error = Error;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Error> {
        std::path::PathBuf::decode(d).map(std::path::PathBuf::into_boxed_path)
    }
}

#[cfg(feature = "std")]
impl<'b> Decode<'b> for std::path::PathBuf {
    type Error = Error;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Error> {
        <&'b std::path::Path>::decode(d).map(std::path::Path::to_path_buf)
    }
}

#[cfg(test)]
mod tests {
    use crate::{InvalidHeader, test};

    #[test]
    fn empty() {
        assert!(test::<&str>("", &[0x60]).unwrap());
        #[cfg(feature = "alloc")]
        {
            use alloc::{boxed::Box, string::String};

            assert!(test::<String>(String::new(), &[0x60]).unwrap());
            assert!(test::<Box<str>>(Box::<str>::from(""), &[0x60]).unwrap());
        }
    }

    #[test]
    fn definite() {
        let cbor = [0x65, 0x68, 0x65, 0x6c, 0x6c, 0x6f];
        let result = "hello";

        assert!(test::<&str>(result, &cbor).unwrap());

        #[cfg(feature = "alloc")]
        {
            use alloc::{boxed::Box, string::String};

            assert!(test(String::from(result), &cbor).unwrap());
            assert!(test(Box::<str>::from(result), &cbor).unwrap());
        }
    }

    #[test]
    fn definite_unicode() {
        let cbor = [0x69, 0xf0, 0x9f, 0x98, 0x80, 0x20, 0xf0, 0x9f, 0xa6, 0x80];
        let result = "😀 🦀";

        assert!(test::<&str>(result, &cbor).unwrap());

        #[cfg(feature = "alloc")]
        {
            use alloc::{boxed::Box, string::String};

            assert!(test(String::from(result), &cbor).unwrap());
            assert!(test(Box::<str>::from(result), &cbor).unwrap());
        }
    }

    #[test]
    fn indefinite() {
        let err = test::<&str>("", &[0x7F, 0x60, 0xFF]).unwrap_err();
        assert_eq!(
            err,
            super::Error::Malformed(crate::primitive::Error::InvalidHeader(InvalidHeader))
        );

        #[cfg(feature = "alloc")]
        {
            use alloc::{boxed::Box, string::String};

            let cbor = [0x7f, 0x62, 0x68, 0x65, 0x63, 0x6c, 0x6c, 0x6f, 0xff];
            let result = "hello";

            assert!(!test(String::from(result), &cbor).unwrap());
            assert!(!test(Box::<str>::from(result), &cbor).unwrap());

            let cbor = [0x7f, 0x60, 0x60, 0x60, 0x60, 0xff];

            assert!(!test::<String>(String::new(), &cbor).unwrap());
            assert!(!test::<Box<str>>(Box::<str>::from(""), &cbor).unwrap());

            let cbor = [0x7f, 0xff];

            assert!(!test::<String>(String::new(), &cbor).unwrap());
            assert!(!test::<Box<str>>(Box::<str>::from(""), &cbor).unwrap());
        }
    }

    #[test]
    #[cfg(feature = "std")]
    fn path() {
        use crate::{Decode, Decoder};
        use std::path::{Path, PathBuf};

        let cbor = [0x68, 0x2f, 0x74, 0x6d, 0x70, 0x2f, 0x66, 0x6f, 0x6f];
        let result = "/tmp/foo";

        assert_eq!(
            <&Path>::decode(&mut Decoder(&cbor)).unwrap(),
            Path::new(result)
        );
        assert_eq!(
            PathBuf::decode(&mut Decoder(&cbor)).unwrap(),
            PathBuf::from(result)
        );
        assert_eq!(
            Box::<Path>::decode(&mut Decoder(&cbor)).unwrap(),
            PathBuf::from(result).into_boxed_path()
        );
    }
}
