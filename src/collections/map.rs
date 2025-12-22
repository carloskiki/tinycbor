//! Map-like collections.

#[cfg(feature = "alloc")]
use crate::{CborLen, Decode, Decoder, Encode, Encoder};

/// Errors which can occur when decoding a map entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Error<K, V> {
    /// While decoding the key.
    Key(K),
    /// While decoding the value.
    Value(V),
}

impl<K: core::fmt::Display, V: core::fmt::Display> core::fmt::Display for Error<K, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Key(e) => write!(f, "key: {}", e),
            Error::Value(e) => write!(f, "value: {}", e),
        }
    }
}

impl<K, V> core::error::Error for Error<K, V>
where
    K: core::error::Error + 'static,
    V: core::error::Error + 'static,
{
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Error::Key(e) => Some(e),
            Error::Value(e) => Some(e),
        }
    }
}

#[cfg(feature = "std")]
impl<'b, K, V, S> Decode<'b> for std::collections::HashMap<K, V, S>
where
    K: Decode<'b> + Eq + std::hash::Hash,
    V: Decode<'b>,
    S: std::hash::BuildHasher + std::default::Default,
{
    type Error = super::Error<Error<K::Error, V::Error>>;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        let mut m = Self::default();
        let mut visitor = d.map_visitor()?;
        while let Some(pair) = visitor.visit() {
            let (k, v) = pair.map_err(super::Error::Element)?;
            m.insert(k, v);
        }
        Ok(m)
    }
}

#[cfg(feature = "alloc")]
impl<'b, K, V> Decode<'b> for alloc::collections::BTreeMap<K, V>
where
    K: Decode<'b> + Eq + Ord,
    V: Decode<'b>,
{
    type Error = super::Error<Error<K::Error, V::Error>>;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        let mut m = Self::new();
        let mut visitor = d.map_visitor()?;
        while let Some(pair) = visitor.visit() {
            let (k, v) = pair.map_err(super::Error::Element)?;
            m.insert(k, v);
        }
        Ok(m)
    }
}

#[cfg(feature = "alloc")]
macro_rules! encode_map {
    ($($t:ty)*) => {
        $(
            impl<K: Encode, V: Encode> Encode for $t {
                fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
                    e.map(self.len())?;
                    for (k, v) in self {
                        k.encode(e)?;
                        v.encode(e)?;
                    }
                    Ok(())
                }
            }

            impl<K: CborLen, V: CborLen> CborLen for $t {
                fn cbor_len(&self) -> usize {
                    self.len().cbor_len() + self.iter().map(|(k, v)| k.cbor_len() + v.cbor_len()).sum::<usize>()
                }
            }
        )*
    }
}

#[cfg(feature = "alloc")]
encode_map! {
    alloc::collections::BTreeMap<K, V>
}

#[cfg(feature = "std")]
encode_map! {
    std::collections::HashMap<K, V>
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "alloc")]
    use crate::test;

    #[test]
    #[cfg(feature = "alloc")]
    fn btreemap() {
        use alloc::collections::BTreeMap;

        let mut m = BTreeMap::new();
        assert!(test(m.clone(), &[0xa0]).unwrap());

        m.insert(1u32, 2u32);
        m.insert(3u32, 4u32);
        assert!(test(m, &[0xa2, 0x01, 0x02, 0x03, 0x04]).unwrap());
    }

    #[test]
    #[cfg(feature = "std")]
    fn hashmap() {
        use crate::{Decode, Decoder, Encode, Encoder};
        use std::collections::HashMap;

        let m: HashMap<&str, u32> = HashMap::new();
        assert!(test(m, &[0xa0]).unwrap());

        // HashMap doesn't guarantee order, so test roundtrip
        let mut m = HashMap::new();
        m.insert("a", 1u32);
        m.insert("b", 2u32);

        let mut buf = Vec::new();
        m.encode(&mut Encoder(&mut buf)).unwrap();
        let decoded = HashMap::<&str, u32>::decode(&mut Decoder(&buf)).unwrap();
        assert_eq!(decoded, m);
    }
}
