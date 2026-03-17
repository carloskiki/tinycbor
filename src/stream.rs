//! Handle fragmented or streamed data.
//!
//! Instead of processing a single chunk of data with the [`Decoder`] type, this module provides
//! utilities to process data in chunks as they arrive, which may not constitue a full CBOR object
//! by themselves.

use crate::{Decode, Decoder, InvalidHeader, Token, container, string::InvalidUtf8};
use alloc::{vec, vec::Vec};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Frame {
    Count(usize),
    IndefArray,
    IndefMap,
    IndefBytes,
    IndefString,
}

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
}

impl Default for Any {
    fn default() -> Self {
        Self {
            stack: vec![Frame::Count(0)],
        }
    }
}

impl Any {
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
            let token = Token::decode(chunk)?;
            if (matches!(top(&self.stack), Frame::IndefBytes)
                && !matches!(token, Token::Bytes(_) | Token::Break))
                || (matches!(top(&self.stack), Frame::IndefString)
                    && !matches!(token, Token::String(_) | Token::Break))
            {
                return Err(InvalidHeader.into());
            }

            match token {
                Token::Array(count) => self.stack.push(Frame::Count(count)),
                Token::Map(count) => self.stack.push(Frame::Count(count * 2)),

                Token::BeginBytes => self.stack.push(Frame::IndefBytes),
                Token::BeginString => self.stack.push(Frame::IndefString),
                Token::BeginArray => self.stack.push(Frame::IndefArray),
                Token::BeginMap => self.stack.push(Frame::IndefMap),

                Token::Break if !matches!(top(&self.stack), Frame::Count(_)) => {
                    self.stack.pop();
                }
                Token::Break => return Err(InvalidHeader.into()),

                Token::Tag(_) => continue,

                _ => {}
            }

            loop {
                match self.stack.last_mut() {
                    Some(Frame::Count(0)) => {
                        self.stack.pop();
                    }
                    Some(Frame::Count(n)) => {
                        *n -= 1;
                        break;
                    }
                    None => {
                        return Ok(());
                    }
                    _ => break,
                }
            }
        }
    }

    /// Reset the decoder to its initial state.
    pub fn reset(&mut self) {
        self.stack.clear();
        self.stack.push(Frame::Count(0));
    }
}

#[cfg(test)]
mod tests {
    use crate::primitive;

    use super::*;

    #[test]
    fn smoke() {
        let mut any = Any::default();
        let mut d = Decoder(&[0x83, 0x01]);
        let result = any.feed(&mut d);
        assert!(matches!(result, Err(container::Error::Malformed(primitive::Error::EndOfInput))));
        let mut d = Decoder(&[0x02, 0x03, 0xff]);
        any.feed(&mut d).unwrap();
        assert_eq!(d.0, &[0xff]);
    }
}
