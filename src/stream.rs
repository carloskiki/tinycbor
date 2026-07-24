//! Handle streamed or fragmented data.
//!
//! Instead of processing a continuous slice of data with the [`Decoder`] type, this module provides
//! utilities to process data in chunks as it arrives.

use crate::{Decode, Decoder, InvalidHeader, Token, container, string::InvalidUtf8};
use alloc::{vec, vec::Vec};

/// A streaming decoder for any CBOR item.
///
/// as opposed to [`crate::Any`], this type is designed to handle fragmented chunks through the
/// [`feed`](Self::feed) method, but does not implement [`Encode`]/[`Decode`]/[`CborLen`].
///
/// [`Encode`]: crate::Encode
/// [`CborLen`]: crate::CborLen
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Any {
    stack: Vec<Frame>,
    pending: Vec<u8>,
}

impl Default for Any {
    fn default() -> Self {
        Self {
            stack: vec![Frame::Count(0)],
            pending: Vec::new(),
        }
    }
}

impl Any {
    fn token(
        &mut self,
        chunk: &mut Decoder<'_>,
    ) -> Result<StreamToken, container::Error<InvalidUtf8>> {
        if self.pending.is_empty() {
            let bytes = chunk.0;
            return match Token::decode(chunk) {
                Ok(token) => Ok(token.into()),
                Err(error @ container::Error::Malformed(crate::primitive::Error::EndOfInput)) => {
                    self.pending.extend_from_slice(bytes);
                    chunk.0 = &[];
                    Err(error)
                }
                Err(error) => Err(error),
            };
        }

        let pending_len = self.pending.len();
        let incoming = chunk.0;
        self.pending.extend_from_slice(incoming);
        let mut decoder = Decoder(&self.pending);
        match Token::decode(&mut decoder) {
            Ok(token) => {
                let token = token.into();
                let consumed = self.pending.len() - decoder.0.len();
                let incoming_consumed = consumed
                    .checked_sub(pending_len)
                    .expect("incomplete token must consume its buffered prefix");
                chunk.0 = &incoming[incoming_consumed..];
                self.pending.clear();
                Ok(token)
            }
            Err(error) => {
                chunk.0 = &[];
                Err(error)
            }
        }
    }

    /// Ingest a chunk of data.
    ///
    /// If the chunk completes a full CBOR item, returns `Ok(())` and the remaining unprocessed data is
    /// left in the chunk. Otherwise, returns [`crate::primitive::Error::EndOfInput`] (wrapped in
    /// [`crate::container::Error::Malformed`]) to indicate that more data is needed. Any other error
    /// variant indicates a malformed input.
    pub fn feed(&mut self, chunk: &mut Decoder<'_>) -> Result<(), container::Error<InvalidUtf8>> {
        fn top(stack: &[Frame]) -> &Frame {
            stack.last().expect("stack is non-empty")
        }

        loop {
            let token = self.token(chunk)?;
            if (matches!(top(&self.stack), Frame::IndefBytes)
                && !matches!(token, StreamToken::Bytes | StreamToken::Break))
                || (matches!(top(&self.stack), Frame::IndefString)
                    && !matches!(token, StreamToken::String | StreamToken::Break))
            {
                return Err(InvalidHeader.into());
            }

            match token {
                StreamToken::Array(count) => self.stack.push(Frame::Count(count)),
                StreamToken::Map(count) => self.stack.push(Frame::Count(count.saturating_mul(2))),

                StreamToken::BeginBytes => self.stack.push(Frame::IndefBytes),
                StreamToken::BeginString => self.stack.push(Frame::IndefString),
                StreamToken::BeginArray => self.stack.push(Frame::IndefArray),
                StreamToken::BeginMap => self.stack.push(Frame::IndefMap(false)),

                StreamToken::Break
                    if !matches!(top(&self.stack), Frame::Count(_) | Frame::IndefMap(false)) =>
                {
                    self.stack.pop();
                }
                StreamToken::Break => return Err(InvalidHeader.into()),

                StreamToken::Tag => continue,

                _ => {}
            }

            loop {
                match self.stack.last_mut() {
                    Some(Frame::Count(0)) => {
                        self.stack.pop();
                        continue;
                    }
                    None => {
                        return Ok(());
                    }
                    Some(Frame::Count(n)) => {
                        *n -= 1;
                    }
                    Some(Frame::IndefMap(even)) => {
                        *even = !*even;
                    }
                    _ => {}
                }
                break;
            }
        }
    }

    /// Reset the decoder to its initial state.
    pub fn reset(&mut self) {
        self.stack.clear();
        self.stack.push(Frame::Count(0));
        self.pending.clear();
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StreamToken {
    Array(usize),
    Map(usize),
    BeginBytes,
    BeginString,
    BeginArray,
    BeginMap,
    Bytes,
    String,
    Tag,
    Break,
    Item,
}

impl From<Token<'_>> for StreamToken {
    fn from(token: Token<'_>) -> Self {
        match token {
            Token::Array(count) => StreamToken::Array(count),
            Token::Map(count) => StreamToken::Map(count),
            Token::BeginBytes => StreamToken::BeginBytes,
            Token::BeginString => StreamToken::BeginString,
            Token::BeginArray => StreamToken::BeginArray,
            Token::BeginMap => StreamToken::BeginMap,
            Token::Bytes(_) => StreamToken::Bytes,
            Token::String(_) => StreamToken::String,
            Token::Tag(_) => StreamToken::Tag,
            Token::Break => StreamToken::Break,
            _ => StreamToken::Item,
        }
    }
}

/// Stack frame of the streaming decoder.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Frame {
    Count(usize),
    IndefArray,
    IndefMap(bool),
    IndefBytes,
    IndefString,
}

#[cfg(test)]
mod tests {
    use crate::primitive;

    use super::*;

    #[test]
    fn simple() {
        let mut any = Any::default();
        let mut d = Decoder(&[0x83, 0x01]);
        let result = any.feed(&mut d);
        assert!(matches!(
            result,
            Err(container::Error::Malformed(primitive::Error::EndOfInput))
        ));
        let mut d = Decoder(&[0x02, 0x03, 0xff]);
        any.feed(&mut d).unwrap();
        assert_eq!(d.0, &[0xff]);
    }

    #[test]
    fn fragmented_scalar_argument() {
        let mut any = Any::default();
        let result = any.feed(&mut Decoder(&[0x18]));
        assert!(matches!(
            result,
            Err(container::Error::Malformed(primitive::Error::EndOfInput))
        ));

        let mut d = Decoder(&[0xff, 0x00]);
        any.feed(&mut d).unwrap();
        assert_eq!(d.0, &[0x00]);
    }
}
