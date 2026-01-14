//! Map-like collections.

use crate::{CborLen, Encode, Encoder};
#[cfg(feature = "alloc")]
use crate::{Decode, Decoder};

/// Possible errors when decoding a map entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Error<K, V> {
    /// Error decoding the key.
    Key(K),
    /// Error decoding the value.
    Value(V),
}

impl<K, V> Error<K, V> {
    /// Map a function on the key and value errors.
    pub fn map<KO, VO>(self, fk: impl FnOnce(K) -> KO, fv: impl FnOnce(V) -> VO) -> Error<KO, VO> {
        match self {
            Error::Key(e) => Error::Key(fk(e)),
            Error::Value(e) => Error::Value(fv(e)),
        }
    }
}

impl<K: core::fmt::Display, V: core::fmt::Display> core::fmt::Display for Error<K, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Key(_) => write!(f, "map key error"),
            Error::Value(_) => write!(f, "map value error"),
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
            let (k, v) = pair.map_err(super::Error::Content)?;
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
            let (k, v) = pair.map_err(super::Error::Content)?;
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

// Sequential maps

#[cfg(feature = "alloc")]
impl<'b, K, V> Decode<'b> for alloc::collections::BinaryHeap<(K, V)>
where
    K: Decode<'b> + Ord,
    V: Decode<'b> + Ord,
{
    type Error = super::Error<Error<K::Error, V::Error>>;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        let mut visitor = d.map_visitor()?;
        let mut v = Self::new();
        while let Some(elem) = visitor.visit() {
            v.push(elem.map_err(super::Error::Content)?);
        }

        Ok(v)
    }
}

#[cfg(feature = "std")]
impl<'b, K, V, S> Decode<'b> for std::collections::HashSet<(K, V), S>
where
    K: Decode<'b> + Eq + std::hash::Hash,
    V: Decode<'b> + Eq + std::hash::Hash,
    S: std::hash::BuildHasher + std::default::Default,
{
    type Error = super::Error<Error<K::Error, V::Error>>;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        let mut visitor = d.map_visitor()?;
        let mut v = Self::default();
        while let Some(elem) = visitor.visit() {
            v.insert(elem.map_err(super::Error::Content)?);
        }

        Ok(v)
    }
}

#[cfg(feature = "alloc")]
impl<'b, K, V> Decode<'b> for alloc::collections::BTreeSet<(K, V)>
where
    K: Decode<'b> + Ord,
    V: Decode<'b> + Ord,
{
    type Error = super::Error<Error<K::Error, V::Error>>;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        let mut visitor = d.map_visitor()?;
        let mut v = Self::new();
        while let Some(elem) = visitor.visit() {
            v.insert(elem.map_err(super::Error::Content)?);
        }
        Ok(v)
    }
}

#[cfg(feature = "alloc")]
macro_rules! decode_sequential {
    ($($t:ty, $push:ident)*) => {
        $(
            impl<'b, K: Decode<'b>, V: Decode<'b>> Decode<'b> for $t {
                type Error = super::Error<Error<K::Error, V::Error>>;

                fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
                    let mut visitor = d.map_visitor()?;
                    let mut v = Self::new();
                    while let Some(x) = visitor.visit() {
                        v.$push(x.map_err(super::Error::Content)?)
                    }
                    Ok(v)
                }
            }
        )*
    }
}

#[cfg(feature = "alloc")]
decode_sequential! {
    alloc::vec::Vec<(K, V)>, push
    alloc::collections::VecDeque<(K, V)>, push_back
    alloc::collections::LinkedList<(K, V)>, push_back
}

macro_rules! encode_sequential {
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
                    let n = self.len();
                    n.cbor_len() + self.iter().map(|(k, v)| k.cbor_len() + v.cbor_len()).sum::<usize>()
                }
            }
        )*
    }
}

#[cfg(feature = "alloc")]
encode_sequential! {
    alloc::vec::Vec<(K, V)>
    alloc::collections::VecDeque<(K, V)>
    alloc::collections::LinkedList<(K, V)>
    alloc::collections::BinaryHeap<(K, V)>
    alloc::collections::BTreeSet<(K, V)>
}

#[cfg(feature = "std")]
encode_sequential! {
    std::collections::HashSet<(K, V)>
}

encode_sequential!([(K, V)]);

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

    #[test]
    #[cfg(feature = "alloc")]
    fn vec() {
        use alloc::vec::Vec;

        let v: Vec<(u32, u32)> = Vec::new();
        assert!(test(v, &[0xa0]).unwrap());

        let v = vec![(10u32, 20u32), (30u32, 40u32), (50u32, 60u32)];

        assert!(
            test(
                v,
                &[
                    0xa3, 0x0a, 0x14, 0x18, 0x1e, 0x18, 0x28, 0x18, 0x32, 0x18, 0x3c
                ]
            )
            .unwrap()
        );
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn vecdeque() {
        use alloc::collections::VecDeque;

        let v: VecDeque<(u32, u32)> = VecDeque::new();
        assert!(test(v, &[0xa0]).unwrap());

        let mut v = VecDeque::new();
        v.push_back((5u32, 10u32));
        assert!(test(v, &[0xa1, 0x05, 0x0a]).unwrap());
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn linkedlist() {
        use alloc::collections::LinkedList;

        let v: LinkedList<(u32, u32)> = LinkedList::new();
        assert!(test(v, &[0xa0]).unwrap());

        let mut v = LinkedList::new();
        v.push_back((100u32, 200u32));
        v.push_back((300u32, 400u32));
        v.push_back((500u32, 600u32));
        v.push_back((700u32, 800u32));

        assert!(
            test(
                v,
                &[
                    0xa4, 0x18, 0x64, 0x18, 0xc8, 0x19, 0x01, 0x2c, 0x19, 0x01, 0x90, 0x19, 0x01,
                    0xf4, 0x19, 0x02, 0x58, 0x19, 0x02, 0xbc, 0x19, 0x03, 0x20
                ]
            )
            .unwrap()
        );
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn binaryheap() {
        use crate::{CborLen, Decode, Encode};
        use alloc::collections::BinaryHeap;

        let cbor = &[0xa4, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
        let expected = &[(1u32, 2u32), (3u32, 4u32), (5u32, 6u32), (7u32, 8u32)];

        {
            let heap = BinaryHeap::<(u32, u32)>::decode(&mut crate::Decoder(cbor)).unwrap();
            let mut buf = Vec::new();
            heap.encode(&mut crate::Encoder(&mut buf)).unwrap();
            assert_eq!(heap.cbor_len(), buf.len());
            assert_eq!(heap.into_sorted_vec(), expected);
        }
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn btreeset() {
        use alloc::collections::BTreeSet;

        let v: BTreeSet<(u32, u32)> = BTreeSet::new();
        assert!(test(v, &[0xa0]).unwrap());

        let mut v = BTreeSet::new();
        v.insert((7u32, 8u32));
        v.insert((9u32, 10u32));
        assert!(test(v, &[0xa2, 0x07, 0x08, 0x09, 0x0a]).unwrap());
    }

    #[test]
    #[cfg(feature = "std")]
    fn hashset() {
        use crate::{Decode, Decoder, Encode, Encoder};
        use std::collections::HashSet;

        let v: HashSet<(u32, u32)> = HashSet::new();
        assert!(test(v, &[0xa0]).unwrap());

        // HashSet doesn't preserve order, so test roundtrip
        let mut v = HashSet::new();
        v.insert((15u32, 25u32));
        v.insert((35u32, 45u32));
        v.insert((55u32, 65u32));

        let mut buf = Vec::new();
        v.encode(&mut Encoder(&mut buf)).unwrap();
        let decoded = HashSet::<(u32, u32)>::decode(&mut Decoder(&buf)).unwrap();
        assert_eq!(decoded, v);
    }
}
