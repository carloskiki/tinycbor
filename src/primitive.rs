//! Primitive types.
use core::fmt::{Display, Formatter};

use crate::{CborLen, Decode, Decoder, Encode, Encoder, EndOfInput, InvalidHeader, SIMPLE, Write};

/// Errors that can occur when encoding or decoding CBOR primitive types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Error {
    /// The input ended unexpectedly.
    EndOfInput(EndOfInput),
    /// The header found did not match the expected header.
    InvalidHeader(InvalidHeader),
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::EndOfInput(e) => write!(f, "{e}"),
            Error::InvalidHeader(e) => write!(f, "{e}"),
        }
    }
}

impl From<EndOfInput> for Error {
    fn from(e: EndOfInput) -> Self {
        Error::EndOfInput(e)
    }
}

impl core::error::Error for Error {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Error::EndOfInput(e) => Some(e),
            Error::InvalidHeader(e) => Some(e),
        }
    }
}

/// CBOR null type.
#[derive(Clone, Copy, Default, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub struct Null;

impl Display for Null {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_str("null")
    }
}

impl Decode<'_> for Null {
    type Error = Error;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        match d.read()? {
            0xf6 => Ok(Null),
            _ => Err(Error::InvalidHeader(InvalidHeader)),
        }
    }
}

impl Encode for Null {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        e.put(&[0xf6])
    }
}

impl CborLen for Null {
    fn cbor_len(&self) -> usize {
        1
    }
}

/// CBOR undefined type.
#[derive(Clone, Copy, Default, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub struct Undefined;

impl Display for Undefined {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_str("undefined")
    }
}

impl Decode<'_> for Undefined {
    type Error = Error;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        match d.read()? {
            0xf7 => Ok(Undefined),
            _ => Err(Error::InvalidHeader(InvalidHeader)),
        }
    }
}

impl Encode for Undefined {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        e.put(&[0xf7])
    }
}

impl CborLen for Undefined {
    fn cbor_len(&self) -> usize {
        1
    }
}

/// A CBOR simple value.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Simple(u8);

impl TryFrom<u8> for Simple {
    type Error = InvalidHeader;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if !(20..32).contains(&value) {
            Ok(Simple(value))
        } else {
            Err(InvalidHeader)
        }
    }
}

impl Display for Simple {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "simple({})", self.0)
    }
}

impl Decode<'_> for Simple {
    type Error = Error;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        match d.read()? {
            n @ SIMPLE..=0xf3 => Ok(Simple(n - SIMPLE)),
            0xf8 => {
                let byte = d.read()?;
                if byte < 0x20 {
                    return Err(Error::InvalidHeader(InvalidHeader));
                }
                Ok(Simple(byte))
            }
            _ => Err(Error::InvalidHeader(InvalidHeader)),
        }
    }
}

impl Encode for Simple {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        if self.0 < 24 {
            e.put(&[SIMPLE | self.0])
        } else {
            e.put(&[SIMPLE | 24])?;
            e.put(&[self.0])
        }
    }
}

impl CborLen for Simple {
    fn cbor_len(&self) -> usize {
        if self.0 < 24 { 1 } else { 2 }
    }
}

impl Decode<'_> for bool {
    type Error = Error;

    fn decode(d: &mut Decoder<'_>) -> Result<Self, Self::Error> {
        match d.read()? {
            0xf4 => Ok(false),
            0xf5 => Ok(true),
            _ => Err(Error::InvalidHeader(InvalidHeader)),
        }
    }
}

impl Encode for bool {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        e.put(&[SIMPLE | if *self { 0x15 } else { 0x14 }])
    }
}

impl CborLen for bool {
    fn cbor_len(&self) -> usize {
        1
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test;

    #[test]
    fn null() {
        assert!(test(Null, &[0xf6]).unwrap());
    }

    #[test]
    fn undefined() {
        assert!(test(Undefined, &[0xf7]).unwrap());
    }

    #[test]
    fn simple() {
        assert!(test(Simple(0), &[0xe0]).unwrap());
        assert!(test(Simple(19), &[0xf3]).unwrap());
        assert!(test(Simple(32), &[0xf8, 0x20]).unwrap());
        assert!(test(Simple(255), &[0xf8, 0xff]).unwrap());
    }

    #[test]
    fn bool() {
        assert!(test(false, &[0xf4]).unwrap());
        assert!(test(true, &[0xf5]).unwrap());
    }
}
