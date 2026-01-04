//! A minimal CBOR implementation.
//!
//! This was designed from scratch, but is inspired by [`minicbor`][minicbor].
//!
//! # Overview
//!
//! This crate is organised around the following traits:
//! - [`Decode`]: Decode types from CBOR. This is equivalent to `Deserialize` in
//!   [`serde`][serde].
//! - [`Encode`]: Encode types to CBOR. This is equivalent to `Serialize` in
//!   [`serde`][serde].
//! - [`CborLen`]: Calculate the length of a type's CBOR encoding without encoding it.
//!
//! One can derive these traits on a type using [`tinycbor-derive`], or implement them manually.
//!
//! [minicbor]: https://docs.rs/minicbor
//! [serde]: https://serde.rs
//! [`tinycbor-derive`]: https://docs.rs/tinycbor-derive
//!
//! # Feature flags
//!
//! - `alloc`: Enables support for types in the `alloc` crate, such as `Vec`, `Box`, `Cow`, etc.
//! - `std`: Implies `alloc`, and adds implementations for types and collections only available
//!   in the standard library.
//!
//! # Example
//!
//! A simple encoding and decoding round-trip:
//! ```
//! use tinycbor::{Encode, Decode, Encoder, Decoder};
//!
//! let input = ["hello", "world"];
//! let mut buffer = [0u8; 128];
//! input.encode(&mut Encoder(buffer.as_mut()))?;
//!
//! let output: [&str; 2] = Decode::decode(&mut Decoder(&buffer))?;
//! assert_eq!(input, output);
//!
//! # Ok::<_, Box<dyn core::error::Error>>(())
//! ```
#![doc = include_str!("../DESIGN.md")]
#![cfg_attr(not(any(feature = "std", test)), no_std)]

// To support targets with 128 bit pointers, we would need to handle collections having lengths
// larger than supported by the CBOR format. We don't want to deal with that right now.
#[cfg(not(any(
    target_pointer_width = "16",
    target_pointer_width = "32",
    target_pointer_width = "64"
)))]
compile_error!("only targets with 16, 32 or 64 bit pointer width are supported");

#[cfg(feature = "alloc")]
extern crate alloc;

pub use embedded_io::Write;

mod bytes;
pub mod collections;
pub mod num;
pub mod primitive;
pub mod string;
pub mod tag;
mod wrapper;

const UNSIGNED: u8 = 0x00;
const SIGNED: u8 = 0x20;
const BYTES: u8 = 0x40;
const TEXT: u8 = 0x60;
const ARRAY: u8 = 0x80;
const MAP: u8 = 0xa0;
const TAGGED: u8 = 0xc0;
const SIMPLE: u8 = 0xe0;
const BREAK: u8 = 0xff;

/// Encode a type implementing [`Encode`] and return the encoded byte vector.
///
/// *Requires feature* `"alloc"`.
#[cfg(feature = "alloc")]
pub fn to_vec<T>(x: &T) -> alloc::vec::Vec<u8>
where
    T: Encode,
{
    let mut buf = alloc::vec::Vec::new();
    let Ok(()) = x.encode(&mut Encoder(&mut buf));
    buf
}

/// Error indicating that the end of input has been reached.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct EndOfInput;

impl core::fmt::Display for EndOfInput {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "end of input")
    }
}

impl core::error::Error for EndOfInput {}

/// Error indicating that the CBOR header (first byte) is invalid or malformed.
///
/// This can happen if the header byte represents a different type than expected, or if the header
/// byte is malformed (e.g., uses a reserved value from the CBOR specification).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct InvalidHeader;

impl core::fmt::Display for InvalidHeader {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "invalid header")
    }
}

impl core::error::Error for InvalidHeader {}

/// A non-allocating CBOR encoder writing encoded bytes to the given [`Write`] sink.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Encoder<W>(pub W);

impl<W: Write> Encoder<W> {
    /// Begin encoding an array with `len` elements.
    pub fn array(&mut self, len: usize) -> Result<(), W::Error> {
        self.type_len(ARRAY, len as u64)
    }

    /// Begin encoding an array of unknown size.
    ///
    /// Use [`Encoder::end`] to terminate the array.
    pub fn begin_array(&mut self) -> Result<(), W::Error> {
        self.put(&[0x9f])
    }

    /// Begin encoding a map with `len` entries.
    pub fn map(&mut self, len: usize) -> Result<(), W::Error> {
        self.type_len(MAP, len as u64)
    }

    /// Begin encoding a map of unknown size.
    ///
    /// Use [`Encoder::end`] to terminate the map.
    pub fn begin_map(&mut self) -> Result<(), W::Error> {
        self.put(&[0xbf])
    }

    // TODO: struct that prevents wrong use
    /// Begin encoding an indefinite number of byte slices.
    ///
    /// Use [`Encoder::end`] to terminate.
    pub fn begin_bytes(&mut self) -> Result<(), W::Error> {
        self.put(&[0x5f])
    }

    // TODO: struct that prevents wrong use
    /// Begin encoding an indefinite number of string slices.
    ///
    /// Use [`Encoder::end`] to terminate.
    pub fn begin_str(&mut self) -> Result<(), W::Error> {
        self.put(&[0x7f])
    }

    /// Terminate an indefinite collection.
    pub fn end(&mut self) -> Result<(), W::Error> {
        self.put(&[0xff])
    }

    /// Write the encoded byte slice.
    fn put(&mut self, b: &[u8]) -> Result<(), W::Error> {
        self.0.write_all(b)
    }

    /// Write type and length information.
    fn type_len(&mut self, t: u8, x: u64) -> Result<(), W::Error> {
        match x {
            0..=0x17 => self.put(&[t | x as u8]),
            0x18..=0xff => self.put(&[t | 24, x as u8]),
            0x100..=0xffff => {
                self.put(&[t | 25])?;
                self.put(&(x as u16).to_be_bytes()[..])
            }
            0x1_0000..=0xffff_ffff => {
                self.put(&[t | 26])?;
                self.put(&(x as u32).to_be_bytes())
            }
            _ => {
                self.put(&[t | 27])?;
                self.put(&x.to_be_bytes()[..])
            }
        }
    }
}

/// A CBOR decoder.
///
/// Decodes the content of the byte slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Decoder<'b>(pub &'b [u8]);

impl<'b> Decoder<'b> {
    /// Decode a definite or indefinite bytestring.
    ///
    /// Returns an iterator the potentially many (if indefinite) byte slices that make up the
    /// bytestring.
    pub fn bytes_iter(&mut self) -> Result<BytesIter<'_, 'b>, primitive::Error> {
        let b = self.peek().map_err(primitive::Error::EndOfInput)?;
        if BYTES != type_of(b) {
            return Err(primitive::Error::InvalidHeader(InvalidHeader));
        }
        let state = if info_of(b) == 31 {
            self.read().expect("was peeked");
            if self.peek() == Ok(BREAK) {
                self.read().expect("was peeked");
                State::Indef(true)
            } else {
                State::Indef(false)
            }
        } else {
            let n = self.length()?;
            State::Def(n)
        };

        Ok(BytesIter {
            decoder: self,
            state,
        })
    }

    /// Decode a definite or indefinite UTF-8 string.
    ///
    /// Returns an iterator the potentially many (if indefinite) string slices that make up the
    /// UTF-8 string.
    pub fn str_iter(&mut self) -> Result<StrIter<'_, 'b>, primitive::Error> {
        let b = self.peek().map_err(primitive::Error::EndOfInput)?;
        if TEXT != type_of(b) {
            return Err(primitive::Error::InvalidHeader(InvalidHeader));
        }
        let state = if info_of(b) == 31 {
            self.read().expect("was peeked");
            if self.peek() == Ok(BREAK) {
                self.read().expect("was peeked");
                State::Indef(true)
            } else {
                State::Indef(false)
            }
        } else {
            let n = self.length()?;
            State::Def(n)
        };

        Ok(StrIter {
            decoder: self,
            state,
        })
    }

    /// Begin decoding an array with a visitor.
    ///
    /// The [`ArrayVisitor`] allows iterating over the elements of different types with the
    /// [`ArrayVisitor::visit`] method.
    pub fn array_visitor(&mut self) -> Result<ArrayVisitor<'_, 'b>, primitive::Error> {
        let b = self.peek()?;
        if ARRAY != type_of(b) {
            return Err(primitive::Error::InvalidHeader(InvalidHeader));
        }
        let state = if info_of(b) == 31 {
            self.read().expect("was peeked");
            if self.peek() == Ok(BREAK) {
                self.read().expect("was peeked");
                State::Indef(true)
            } else {
                State::Indef(false)
            }
        } else {
            let n = self.length()?;
            State::Def(n)
        };
        Ok(ArrayVisitor {
            decoder: self,
            state,
        })
    }

    /// Begin decoding a map with a visitor.
    ///
    /// The [`MapVisitor`] allows iterating over the key-value pairs of different types with the
    /// [`MapVisitor::visit`] method.
    pub fn map_visitor(&mut self) -> Result<MapVisitor<'_, 'b>, primitive::Error> {
        let b = self.peek().map_err(primitive::Error::from)?;
        if MAP != type_of(b) {
            return Err(primitive::Error::InvalidHeader(InvalidHeader));
        }
        let state = if info_of(b) == 31 {
            self.read().expect("was peeked");
            if self.peek() == Ok(BREAK) {
                self.read().expect("was peeked");
                State::Indef(true)
            } else {
                State::Indef(false)
            }
        } else {
            let n = self.length()?;
            State::Def(n)
        };
        Ok(MapVisitor {
            decoder: self,
            state,
        })
    }

    /// Inspect the CBOR type at the current position.
    pub fn datatype(&self) -> Result<Type, EndOfInput> {
        Ok(match self.peek()? {
            UNSIGNED..=0x1b | SIGNED..=0x3b => Type::Int,
            BYTES..=0x5b => Type::Bytes,
            0x5f => Type::BytesIndef,
            TEXT..=0x7b => Type::String,
            0x7f => Type::StringIndef,
            ARRAY..=0x9b => Type::Array,
            0x9f => Type::ArrayIndef,
            MAP..=0xbb => Type::Map,
            0xbf => Type::MapIndef,
            TAGGED..=0xdb => Type::Tag,
            SIMPLE..=0xf3 | 0xf8 => Type::Simple,
            0xf4 | 0xf5 => Type::Bool,
            0xf6 => Type::Null,
            0xf7 => Type::Undefined,
            0xf9..=0xfb => Type::Float,
            BREAK => Type::Break,
            _ => Type::Unknown,
        })
    }

    fn unsigned(&mut self) -> Result<u64, primitive::Error> {
        Ok(match info_of(self.read()?) {
            n @ 0..=0x17 => Ok(u64::from(n)),
            0x18 => self.read().map(u64::from),
            0x19 => self.read_array().map(u16::from_be_bytes).map(u64::from),
            0x1a => self.read_array().map(u32::from_be_bytes).map(u64::from),
            0x1b => self.read_array().map(u64::from_be_bytes),
            _ => return Err(primitive::Error::InvalidHeader(InvalidHeader)),
        }?)
    }

    /// Decode an unsigned length from the decoder. converting from u64 to usize is fine when it is
    /// a length because lengths larger than usize::MAX cannot be represented in memory anyway.
    fn length(&mut self) -> Result<usize, primitive::Error> {
        Ok(self.unsigned()?.try_into().unwrap_or(usize::MAX))
    }

    /// Consume and return the byte at the current position.
    fn read(&mut self) -> Result<u8, EndOfInput> {
        if let Some(b) = self.0.first() {
            self.0 = &self.0[1..];
            return Ok(*b);
        }
        Err(EndOfInput)
    }

    /// Peek to the next byte.
    fn peek(&self) -> Result<u8, EndOfInput> {
        self.0.first().copied().ok_or(EndOfInput)
    }

    /// Consume and return *n* bytes starting at the current position.
    fn read_slice(&mut self, n: usize) -> Result<&'b [u8], EndOfInput> {
        if let Some(b) = self.0.get(..n) {
            self.0 = &self.0[n..];
            return Ok(b);
        }
        Err(EndOfInput)
    }

    /// Consume and return *N* bytes starting at the current position.
    fn read_array<const N: usize>(&mut self) -> Result<[u8; N], EndOfInput> {
        self.read_slice(N).map(|slice| {
            let mut a = [0; N];
            a.copy_from_slice(slice);
            a
        })
    }
}

/// Iterate over the [`Token`]s in the decoder.
///
/// ```
/// use tinycbor::{Decoder, Encoder, Token};
///
/// let input  = [0x83, 0x01, 0x9f, 0x02, 0x03, 0xff, 0x82, 0x04, 0x05];
/// let tokens = Decoder(&input);
/// let expected = &[
///     Token::Array(3),
///     Token::Int(From::from(1)),
///     Token::BeginArray,
///     Token::Int(From::from(2)),
///     Token::Int(From::from(3)),
///     Token::Break,
///     Token::Array(2),
///     Token::Int(From::from(4)),
///     Token::Int(From::from(5))
/// ];
///
/// for (token, expected) in tokens.zip(expected.iter()) {
///     assert_eq!(&token?, expected);
/// }
/// # Ok::<_, Box<dyn core::error::Error>>(())
/// ```
impl<'b> Iterator for Decoder<'b> {
    type Item = Result<Token<'b>, string::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.0.is_empty() {
            return None;
        }
        Some(Token::decode(self))
    }
}

/// Display the CBOR data items left in the decoder.
///
/// ```
/// use tinycbor::Decoder;
///
/// let input  = [0x83, 0x01, 0x9f, 0x02, 0x03, 0xff, 0x82, 0x04, 0x05];
///
/// assert_eq!("[1, [_ 2, 3], [4, 5]]", format!("{}", Decoder(&input)));
/// ```
///
#[cfg(feature = "alloc")]
impl core::fmt::Display for Decoder<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        /// Control stack element.
        enum E {
            N(bool),          // get next token (true => token is required)
            T,                // tag
            A(Option<usize>), // array
            M(Option<usize>), // map
            B,                // indefinite bytes
            D,                // indefinite text
            S(&'static str),  // display string
            X(&'static str),  // display string (unless next token is BREAK)
        }

        let mut iter = self.peekable();
        let mut stack = alloc::vec::Vec::new();

        while iter.peek().is_some() {
            stack.push(E::N(false));
            while let Some(elt) = stack.pop() {
                match elt {
                    E::N(required) => match iter.next() {
                        Some(Ok(Token::Array(n))) => {
                            stack.push(E::A(Some(n)));
                            f.write_str("[")?
                        }
                        Some(Ok(Token::Map(n))) => {
                            stack.push(E::M(Some(n)));
                            f.write_str("{")?
                        }
                        Some(Ok(Token::BeginArray)) => {
                            stack.push(E::A(None));
                            f.write_str("[_ ")?
                        }
                        Some(Ok(Token::BeginMap)) => {
                            stack.push(E::M(None));
                            f.write_str("{_ ")?
                        }
                        Some(Ok(Token::BeginBytes)) => {
                            if let Some(Ok(Token::Break)) = iter.peek() {
                                iter.next();
                                f.write_str("''_")?
                            } else {
                                stack.push(E::B);
                                f.write_str("(_ ")?
                            }
                        }
                        Some(Ok(Token::BeginString)) => {
                            if let Some(Ok(Token::Break)) = iter.peek() {
                                iter.next();
                                f.write_str("\"\"_")?
                            } else {
                                stack.push(E::D);
                                f.write_str("(_ ")?
                            }
                        }
                        Some(Ok(Token::Tag(t))) => {
                            stack.push(E::T);
                            write!(f, "{}(", t)?
                        }
                        Some(Ok(t)) => t.fmt(f)?,
                        Some(Err(e)) => {
                            write!(f, " !!! decoding error: {e}")?;
                            return Ok(());
                        }
                        None => {
                            if required {
                                f.write_str(" !!! decoding error: unexpected end of input")?;
                                return Ok(());
                            } else {
                                continue;
                            }
                        }
                    },
                    E::S(s) => f.write_str(s)?,
                    E::X(s) => match iter.peek() {
                        Some(Ok(Token::Break)) | None => continue,
                        Some(Ok(_)) => f.write_str(s)?,
                        Some(Err(e)) => {
                            write!(f, " !!! decoding error: {e}")?;
                            return Ok(());
                        }
                    },
                    E::T => {
                        stack.push(E::S(")"));
                        stack.push(E::N(true))
                    }
                    E::A(Some(0)) => f.write_str("]")?,
                    E::A(Some(1)) => {
                        stack.push(E::A(Some(0)));
                        stack.push(E::N(true))
                    }
                    E::A(Some(n)) => {
                        stack.push(E::A(Some(n - 1)));
                        stack.push(E::S(", "));
                        stack.push(E::N(true))
                    }
                    E::A(None) => match iter.peek() {
                        None => {
                            f.write_str(" !!! indefinite array not closed")?;
                            return Ok(());
                        }
                        Some(Ok(Token::Break)) => {
                            iter.next();
                            f.write_str("]")?
                        }
                        _ => {
                            stack.push(E::A(None));
                            stack.push(E::X(", "));
                            stack.push(E::N(true))
                        }
                    },
                    E::M(Some(0)) => f.write_str("}")?,
                    E::M(Some(1)) => {
                        stack.push(E::M(Some(0)));
                        stack.push(E::N(true));
                        stack.push(E::S(": "));
                        stack.push(E::N(true))
                    }
                    E::M(Some(n)) => {
                        stack.push(E::M(Some(n - 1)));
                        stack.push(E::S(", "));
                        stack.push(E::N(true));
                        stack.push(E::S(": "));
                        stack.push(E::N(true))
                    }
                    E::M(None) => match iter.peek() {
                        None => {
                            f.write_str(" !!! indefinite map not closed")?;
                            return Ok(());
                        }
                        Some(Ok(Token::Break)) => {
                            iter.next();
                            f.write_str("}")?
                        }
                        _ => {
                            stack.push(E::M(None));
                            stack.push(E::X(", "));
                            stack.push(E::N(true));
                            stack.push(E::S(": "));
                            stack.push(E::N(true))
                        }
                    },
                    E::B => match iter.peek() {
                        None => {
                            f.write_str(" !!! indefinite byte string not closed")?;
                            return Ok(());
                        }
                        Some(Ok(Token::Break)) => {
                            iter.next();
                            f.write_str(")")?
                        }
                        _ => {
                            stack.push(E::B);
                            stack.push(E::X(", "));
                            stack.push(E::N(true))
                        }
                    },
                    E::D => match iter.peek() {
                        None => {
                            f.write_str(" !!! indefinite string not closed")?;
                            return Ok(());
                        }
                        Some(Ok(Token::Break)) => {
                            iter.next();
                            f.write_str(")")?
                        }
                        _ => {
                            stack.push(E::D);
                            stack.push(E::X(", "));
                            stack.push(E::N(true))
                        }
                    },
                }
            }
        }

        Ok(())
    }
}

/// A type that can be encoded to CBOR.
pub trait Encode {
    /// Encode a value of this type using the given `Writer`.
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error>;
}

/// A type that can calculate its own CBOR encoding length.
pub trait CborLen {
    /// Compute the CBOR encoding length in bytes of this value.
    fn cbor_len(&self) -> usize;
}

/// A type that can be decoded from CBOR.
pub trait Decode<'b>: Sized {
    /// The error type returned when decoding fails.
    type Error: core::error::Error + 'static;

    /// Decode a value using the given `Decoder`.
    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error>;
}

/// Get the major type info of the given byte (highest 3 bits).
fn type_of(b: u8) -> u8 {
    b & 0b111_00000
}

/// Get the additionl type info of the given byte (lowest 5 bits).
fn info_of(b: u8) -> u8 {
    b & 0b000_11111
}

/// Iterator state.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum State {
    /// Definite length.
    Def(usize),
    /// Indefinite length. Stores whether the end has been reached.
    Indef(bool),
}

impl From<Option<usize>> for State {
    fn from(val: Option<usize>) -> Self {
        if let Some(n) = val {
            Self::Def(n)
        } else {
            Self::Indef(false)
        }
    }
}

impl State {
    fn remaining(&self) -> Option<usize> {
        match self {
            State::Def(n) => Some(*n),
            State::Indef(done) => done.then_some(0),
        }
    }
}

/// An iterator over byte slices.
///
/// Returned from [`Decoder::bytes_iter`].
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct BytesIter<'a, 'b> {
    decoder: &'a mut Decoder<'b>,
    state: State,
}

impl<'b> Iterator for BytesIter<'_, 'b> {
    type Item = Result<&'b [u8], primitive::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.state {
            State::Indef(false) => {
                let bytes = Decode::decode(self.decoder);
                if let Ok(BREAK) = self.decoder.peek() {
                    self.decoder.read().expect("was peeked");
                    self.state = State::Indef(true);
                }
                Some(bytes)
            }
            State::Def(0) | State::Indef(true) => None,
            State::Def(n) => {
                self.state = State::Def(0);
                Some(self.decoder.read_slice(n).map_err(primitive::Error::from))
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.state {
            State::Def(_) => (1, Some(1)),
            State::Indef(true) => (0, Some(0)),
            State::Indef(false) => (0, None),
        }
    }
}

/// Iterate over string slices.
///
/// Returned from [`Decoder::str_iter`].
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct StrIter<'a, 'b> {
    decoder: &'a mut Decoder<'b>,
    state: State,
}

impl<'b> Iterator for StrIter<'_, 'b> {
    type Item = Result<&'b str, string::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.state {
            State::Indef(false) => {
                let s = Decode::decode(self.decoder);
                if let Ok(BREAK) = self.decoder.peek() {
                    self.decoder.read().expect("was peeked");
                    self.state = State::Indef(true);
                }
                Some(s)
            }
            State::Def(0) | State::Indef(true) => None,
            State::Def(n) => {
                self.state = State::Def(0);
                Some(
                    self.decoder
                        .read_slice(n)
                        .map_err(string::Error::from)
                        .and_then(|slice| core::str::from_utf8(slice).map_err(string::Error::from)),
                )
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.state {
            State::Def(_) => (1, Some(1)),
            State::Indef(true) => (0, Some(0)),
            State::Indef(false) => (0, None),
        }
    }
}

/// A visitor for decoding array elements of different types.
///
/// Returned from [`Decoder::array_visitor`].
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ArrayVisitor<'a, 'b> {
    decoder: &'a mut Decoder<'b>,
    state: State,
}

impl<'b> ArrayVisitor<'_, 'b> {
    /// Visit the next element in the array.
    pub fn visit<T: Decode<'b>>(&mut self) -> Option<Result<T, T::Error>> {
        match self.state {
            State::Indef(false) => {
                let value = T::decode(self.decoder);
                if let Ok(BREAK) = self.decoder.peek() {
                    self.decoder.read().expect("was peeked");
                    self.state = State::Indef(true);
                }
                Some(value)
            }
            State::Indef(true) | State::Def(0) => None,
            State::Def(n) => {
                self.state = State::Def(n - 1);
                Some(T::decode(self.decoder))
            }
        }
    }

    pub fn remaining(&self) -> Option<usize> {
        self.state.remaining()
    }

    pub fn definite(&self) -> bool {
        matches!(self.state, State::Def(_))
    }
}

/// A visitor for decoding map key-value pairs of different types.
///
/// Returned from [`Decoder::map_visitor`].
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct MapVisitor<'a, 'b> {
    decoder: &'a mut Decoder<'b>,
    state: State,
}

impl<'b> MapVisitor<'_, 'b> {
    /// Visit the next key-value pair in the map.
    #[allow(clippy::type_complexity)]
    pub fn visit<K: Decode<'b>, V: Decode<'b>>(
        &mut self,
    ) -> Option<Result<(K, V), collections::map::Error<K::Error, V::Error>>> {
        Some(match self.with_key(|k, d| (k, V::decode(d)))? {
            Ok((k, Ok(v))) => Ok((k, v)),
            Ok((_, Err(v))) => Err(collections::map::Error::Value(v)),
            Err(k) => Err(collections::map::Error::Key(k)),
        })
    }

    /// Visit the next key in the map, applying the given function to decode the value.
    pub fn with_key<K, F, O>(&mut self, f: F) -> Option<Result<O, K::Error>>
    where
        K: Decode<'b>,
        F: FnOnce(K, &mut Decoder<'b>) -> O,
    {
        match self.state {
            State::Indef(false) => {
                let key = K::decode(self.decoder);
                if let Ok(BREAK) = self.decoder.peek() {
                    self.decoder.read().expect("was peeked");
                    self.state = State::Indef(true);
                }
                match key {
                    Ok(k) => Some(Ok(f(k, self.decoder))),
                    Err(e) => Some(Err(e)),
                }
            }
            State::Indef(true) | State::Def(0) => None,
            State::Def(n) => {
                self.state = State::Def(n - 1);
                let key = K::decode(self.decoder);
                match key {
                    Ok(k) => Some(Ok(f(k, self.decoder))),
                    Err(e) => Some(Err(e)),
                }
            }
        }
    }

    pub fn remaining(&self) -> Option<usize> {
        self.state.remaining()
    }

    pub fn definite(&self) -> bool {
        matches!(self.state, State::Def(_))
    }
}

/// CBOR data type.
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub enum Type {
    Bool,
    Null,
    Undefined,
    Int,
    Float,
    Simple,
    Bytes,
    BytesIndef,
    String,
    StringIndef,
    Array,
    ArrayIndef,
    Map,
    MapIndef,
    Tag,
    Break,
    Unknown,
}

impl core::fmt::Display for Type {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Type::Bool => f.write_str("bool"),
            Type::Null => f.write_str("null"),
            Type::Undefined => f.write_str("undefined"),
            Type::Int => f.write_str("int"),
            Type::Float => f.write_str("f64"),
            Type::Simple => f.write_str("simple"),
            Type::Bytes => f.write_str("bytes"),
            Type::BytesIndef => f.write_str("indefinite bytes"),
            Type::String => f.write_str("string"),
            Type::StringIndef => f.write_str("indefinite string"),
            Type::Array => f.write_str("array"),
            Type::ArrayIndef => f.write_str("indefinite array"),
            Type::Map => f.write_str("map"),
            Type::MapIndef => f.write_str("indefinite map"),
            Type::Tag => f.write_str("tag"),
            Type::Break => f.write_str("break"),
            Type::Unknown => write!(f, "<unknown>"),
        }
    }
}

/// Representation of possible CBOR tokens.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Token<'b> {
    Bool(bool),
    Int(num::Int),
    Float(f64),
    Bytes(&'b [u8]),
    String(&'b str),
    Array(usize),
    Map(usize),
    Tag(u64),
    Simple(primitive::Simple),
    Break,
    Null,
    Undefined,
    /// Start of indefinite byte string.
    BeginBytes,
    /// Start of indefinite text string.
    BeginString,
    /// Start of indefinite array.
    BeginArray,
    /// Start of indefinite map.
    BeginMap,
}

/// Pretty print a token.
///
/// Since we only show a single token we can not use diagnostic notation
/// as in the `Display` impl of [`Decoder`]. Instead, the following
/// syntax is used:
///
/// - Numeric values and booleans are displayed as in Rust. Floats are always
///   shown in scientific notation.
/// - Text strings are displayed in double quotes.
/// - Byte strings are displayed in single quotes prefixed with `h` and
///   hex-encoded, e.g. `h'01 02 ef'`.
/// - An array is displayed as `A[n]` where `n` denotes the number of elements.
///   The following `n` tokens are elements of this array.
/// - A map is displayed as `M[n]` where `n` denotes the number of pairs.
///   The following `n` tokens are entries of this map.
/// - Tags are displayed with `T(t)` where `t` is the tag number.
/// - Simple values are displayed as `simple(n)` where `n` denotes the numeric
///   value.
/// - Indefinite items start with:
///
///     * `?B[` for byte strings,
///     * `?S[` for text strings,
///     * `?A[` for arrays,
///     * `?M[` for maps,
///
///   and end with `]` when a `Token::Break` is encountered. All tokens
///   in between belong to the indefinite container.
/// - `Token::Null` is displayed as `null` and `Token::Undefined` as `undefined`.
impl core::fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Token::Bool(b) => write!(f, "{b}"),
            Token::Int(n) => write!(f, "{n}"),
            Token::Float(n) => write!(f, "{n:e}"),
            Token::String(n) => write!(f, "\"{n}\""),
            Token::Array(n) => write!(f, "A[{n}]"),
            Token::Map(n) => write!(f, "M[{n}]"),
            Token::Tag(t) => write!(f, "T({})", t),
            Token::Simple(n) => write!(f, "{n}"),
            Token::Break => f.write_str("]"),
            Token::Null => f.write_str("null"),
            Token::Undefined => f.write_str("undefined"),
            Token::BeginBytes => f.write_str("?B["),
            Token::BeginString => f.write_str("?S["),
            Token::BeginArray => f.write_str("?A["),
            Token::BeginMap => f.write_str("?M["),
            Token::Bytes(b) => {
                f.write_str("h'")?;
                let mut i = b.len();
                for x in *b {
                    if i > 1 {
                        write!(f, "{x:02x} ")?
                    } else {
                        write!(f, "{x:02x}")?
                    }
                    i -= 1;
                }
                f.write_str("'")
            }
        }
    }
}

impl<'b> Decode<'b> for Token<'b> {
    type Error = string::Error;

    fn decode(d: &mut crate::Decoder<'b>) -> Result<Self, Self::Error> {
        Ok(match d.datatype().map_err(primitive::Error::EndOfInput)? {
            Type::Bool => Token::Bool(bool::decode(d)?),
            Type::Int => Token::Int(num::Int::decode(d)?),
            Type::Float => Token::Float(f64::decode(d)?),
            Type::Bytes => Token::Bytes(<&'b [u8]>::decode(d)?),
            Type::String => Token::String(<&'b str>::decode(d)?),
            Type::Tag => Token::Tag(d.unsigned()?),
            Type::Simple => Token::Simple(primitive::Simple::decode(d)?),
            Type::Array => Token::Array(d.array_visitor()?.remaining().expect("known length")),
            Type::Map => Token::Map(d.map_visitor()?.remaining().expect("known length")),
            Type::BytesIndef => {
                d.read().expect("byte was peeked in datatype");
                Token::BeginBytes
            }
            Type::StringIndef => {
                d.read().expect("byte was peeked in datatype");
                Token::BeginString
            }
            Type::ArrayIndef => {
                d.read().expect("byte was peeked in datatype");
                Token::BeginArray
            }
            Type::MapIndef => {
                d.read().expect("byte was peeked in datatype");
                Token::BeginMap
            }
            Type::Null => {
                d.read().expect("byte was peeked in datatype");
                Token::Null
            }
            Type::Undefined => {
                d.read().expect("byte was peeked in datatype");
                Token::Undefined
            }
            Type::Break => {
                d.read().expect("byte was peeked in datatype");
                Token::Break
            }
            Type::Unknown => {
                return Err(string::Error::Malformed(primitive::Error::InvalidHeader(
                    InvalidHeader,
                )));
            }
        })
    }
}

/// Encodes as a tagged byte string, where the content is the CBOR encoding of `T`.
///
/// Uses [`IanaTag::Cbor`][tag::IanaTag::Cbor] as the tag.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Encoded<T: ?Sized>(pub T);

impl<T> Encoded<T> {
    /// Unwrap the inner value.
    pub fn into(self) -> T {
        self.0
    }
}

impl<T> From<T> for Encoded<T> {
    fn from(value: T) -> Self {
        Encoded(value)
    }
}

impl<T: ?Sized> From<&T> for &Encoded<T> {
    fn from(value: &T) -> Self {
        // Safety: `Encoded<T>` is `repr(transparent)` over `T`.
        unsafe { &*(value as *const T as *const Encoded<T>) }
    }
}

impl<T: ?Sized> AsRef<T> for Encoded<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: ?Sized> AsMut<T> for Encoded<T> {
    fn as_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T: ?Sized> core::ops::Deref for Encoded<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: ?Sized> core::ops::DerefMut for Encoded<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: ?Sized + CborLen> CborLen for Encoded<T> {
    fn cbor_len(&self) -> usize {
        let len = self.0.cbor_len();
        (tag::IanaTag::Cbor as u64).cbor_len() + len.cbor_len() + len
    }
}

impl<T: ?Sized + Encode + CborLen> Encode for Encoded<T> {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        e.type_len(TAGGED, tag::IanaTag::Cbor as u64)?;
        e.type_len(BYTES, self.0.cbor_len() as u64)?;
        self.0.encode(e)
    }
}

impl<'b, T: Decode<'b>> Decode<'b> for Encoded<T> {
    type Error = tag::Error<collections::Error<T::Error>>;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        let tag::Tagged(bytes) = tag::Tagged::<&'b [u8], { tag::IanaTag::Cbor as u64 }>::decode(d)
            .map_err(|e| e.map(collections::Error::Malformed))?;

        let mut inner_decoder = Decoder(bytes);
        T::decode(&mut inner_decoder)
            .map(Encoded)
            .map_err(|e| tag::Error::Inner(collections::Error::Element(e)))
    }
}

/// Decodes any CBOR data item, keeping its original encoding.
///
/// This can be useful to skip over unknown data items while preserving their exact encoding.
#[cfg(feature = "alloc")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Any<'a>(&'a [u8]);

#[cfg(feature = "alloc")]
impl<'a> core::ops::Deref for Any<'a> {
    type Target = &'a [u8];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[cfg(feature = "alloc")]
impl<'a> core::convert::AsRef<[u8]> for Any<'a> {
    fn as_ref(&self) -> &[u8] {
        self.0
    }
}

#[cfg(feature = "alloc")]
impl<'a, 'b> Decode<'b> for Any<'a>
where
    'b: 'a,
{
    type Error = string::Error;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        use alloc::{vec, vec::Vec};

        enum Frame {
            Count(usize),
            IndefArray,
            IndefMap,
            IndefBytes,
            IndefString,
        }
        fn top(stack: &[Frame]) -> &Frame {
            stack.last().expect("stack is non-empty")
        }
        fn invalid_header() -> string::Error {
            string::Error::Malformed(primitive::Error::InvalidHeader(InvalidHeader))
        }

        let mut stack: Vec<Frame> = vec![Frame::Count(0)];
        let start = d.0;

        'outer: loop {
            let token = Token::decode(d)?;
            if (matches!(top(&stack), Frame::IndefBytes)
                && !matches!(token, Token::Bytes(_) | Token::Break))
                || (matches!(top(&stack), Frame::IndefString)
                    && !matches!(token, Token::String(_) | Token::Break))
            {
                return Err(invalid_header());
            }

            match token {
                Token::Array(count) => stack.push(Frame::Count(count)),
                Token::Map(count) => stack.push(Frame::Count(count * 2)),

                Token::BeginBytes => stack.push(Frame::IndefBytes),
                Token::BeginString => stack.push(Frame::IndefString),
                Token::BeginArray => stack.push(Frame::IndefArray),
                Token::BeginMap => stack.push(Frame::IndefMap),
                Token::Break if !matches!(top(&stack), Frame::Count(_)) => {
                    stack.pop();
                }
                Token::Break => return Err(invalid_header()),

                _ => {}
            }

            loop {
                match stack.last() {
                    Some(Frame::Count(0)) => {
                        stack.pop();
                    }
                    Some(Frame::Count(n)) => {
                        let n = *n - 1;
                        *stack.last_mut().expect("stack is non-empty") = Frame::Count(n);
                        break;
                    }
                    None => break 'outer,
                    _ => break,
                }
            }
        }

        let end = d.0;
        let len = start.len() - end.len();
        Ok(Any(&start[..len]))
    }
}

#[cfg(feature = "alloc")]
impl Encode for Any<'_> {
    fn encode<W: Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        e.0.write_all(self.0)
    }
}

#[cfg(feature = "alloc")]
impl CborLen for Any<'_> {
    fn cbor_len(&self) -> usize {
        self.0.len()
    }
}

/// Returns `true` if `value.encode() == bytes`, false otherwise.
///
/// Panics when:
/// - The encoded size is greater than `16KB.
/// - The value decoded from `bytes` is not equal to `value`.
/// - `value.cbor_len() != <encoded-len>`.
#[cfg(test)]
fn test<'a, T>(value: T, bytes: &'a [u8]) -> Result<bool, T::Error>
where
    T: Decode<'a> + Encode + CborLen + core::cmp::PartialEq + core::fmt::Debug,
{
    let mut buffer = Vec::new();
    value.encode(&mut Encoder(&mut buffer));
    assert_eq!(
        value.cbor_len(),
        buffer.len(),
        "cbor_len does not match actual length"
    );
    let decoded = T::decode(&mut Decoder(bytes))?;
    assert_eq!(value, decoded, "decoded value does not match original");
    Ok(buffer.as_slice() == bytes)
}

#[cfg(test)]
mod tests {
    use core::num::NonZeroU8;

    use crate::{Any, Decode, Decoder, Encode, Encoder, primitive::Undefined};

    #[test]
    fn any() {
        let mut encoder = Encoder(Vec::new());

        encoder.map(3);
        u32::MAX.encode(&mut encoder);
        "hello world".encode(&mut encoder);
        encoder.array(2);
        true.encode(&mut encoder);
        core::f64::consts::PI.encode(&mut encoder);
        Undefined.encode(&mut encoder);
        encoder.begin_map();
        encoder.begin_str();
        "key".encode(&mut encoder);
        encoder.end();
        encoder.begin_array();
        [3, 1, 4, 1, 5].encode(&mut encoder);
        [3u8, 1, 4, 1, 5].encode(&mut encoder);
        encoder.end();
        encoder.end();
        encoder.begin_bytes();
        encoder.end();

        Any::decode(&mut Decoder(&encoder.0)).unwrap();
    }
}
