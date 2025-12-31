//! `alloc` and `std` collection support.

use crate::{CborLen, Encode, Encoder, primitive};
#[cfg(feature = "alloc")]
use crate::{Decode, Decoder};

pub mod fixed;
pub mod map;

/// Error that can occur when decoding dynamic containers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Error<E> {
    /// The container header is malformed.
    Malformed(primitive::Error),
    /// While decoding an element within the container.
    Element(E),
}

impl<E> Error<E> {
    /// Map a function on the inner error.
    pub fn map<O>(self, f: impl FnOnce(E) -> O) -> Error<O> {
        match self {
            Error::Malformed(e) => Error::Malformed(e),
            Error::Element(e) => Error::Element(f(e)),
        }
    }
}

impl<E: core::fmt::Display> core::fmt::Display for Error<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Malformed(e) => write!(f, "{e}"),
            Error::Element(e) => write!(f, "container element: {e}"),
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
            Error::Element(e) => Some(e),
        }
    }
}

#[cfg(feature = "alloc")]
impl<'b, T> Decode<'b> for alloc::collections::BinaryHeap<T>
where
    T: Decode<'b> + Ord,
{
    type Error = Error<T::Error>;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        let mut visitor = d.array_visitor()?;
        let mut v = Self::new();
        while let Some(elem) = visitor.visit() {
            v.push(elem.map_err(Error::Element)?);
        }

        Ok(v)
    }
}

#[cfg(feature = "std")]
impl<'b, T, S> Decode<'b> for std::collections::HashSet<T, S>
where
    T: Decode<'b> + Eq + std::hash::Hash,
    S: std::hash::BuildHasher + std::default::Default,
{
    type Error = Error<T::Error>;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        let mut visitor = d.array_visitor()?;
        let mut v = Self::default();
        while let Some(elem) = visitor.visit() {
            v.insert(elem.map_err(Error::Element)?);
        }

        Ok(v)
    }
}

#[cfg(feature = "alloc")]
impl<'b, T> Decode<'b> for alloc::collections::BTreeSet<T>
where
    T: Decode<'b> + Ord,
{
    type Error = Error<T::Error>;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        let mut visitor = d.array_visitor()?;
        let mut v = Self::new();
        while let Some(elem) = visitor.visit() {
            v.insert(elem.map_err(Error::Element)?);
        }
        Ok(v)
    }
}

#[cfg(feature = "alloc")]
macro_rules! decode_sequential {
    ($($t:ty, $push:ident)*) => {
        $(
            impl<'b, T: Decode<'b>> Decode<'b> for $t {
                type Error = Error<T::Error>;

                fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
                    let mut visitor = d.array_visitor()?;
                    let mut v = Self::new();
                    while let Some(x) = visitor.visit() {
                        v.$push(x.map_err(Error::Element)?)
                    }
                    Ok(v)
                }
            }
        )*
    }
}

#[cfg(feature = "alloc")]
decode_sequential! {
    alloc::vec::Vec<T>, push
    alloc::collections::VecDeque<T>, push_back
    alloc::collections::LinkedList<T>, push_back
}

macro_rules! encode_sequential {
    ($($t:ty)*) => {
        $(
            impl<T: Encode> Encode for $t {
                fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
                    e.array(self.len())?;
                    for x in self {
                        x.encode(e)?
                    }
                    Ok(())
                }
            }

            impl<T: CborLen> CborLen for $t {
                fn cbor_len(&self) -> usize {
                    let n = self.len();
                    n.cbor_len() + self.iter().map(|x| x.cbor_len()).sum::<usize>()
                }
            }
        )*
    }
}

#[cfg(feature = "alloc")]
encode_sequential! {
    alloc::vec::Vec<T>
    alloc::collections::VecDeque<T>
    alloc::collections::LinkedList<T>
    alloc::collections::BinaryHeap<T>
    alloc::collections::BTreeSet<T>
}

#[cfg(feature = "std")]
encode_sequential! {
    std::collections::HashSet<T>
}

encode_sequential!([T]);

#[cfg(all(test, feature = "alloc"))]
mod tests {
    use crate::{CborLen, Decode, Decoder, Encode, Encoder, test};

    const EMPTY_ARRAY: &[u8] = &[0x80];
    const EMPTY_INDEF: &[u8] = &[0x9f, 0xff];

    #[cfg(feature = "alloc")]
    fn test_binary_heap<'a, T>(cbor: &'a [u8], expected: &[T])
    where
        T: Decode<'a> + Encode + CborLen + Ord + PartialEq + core::fmt::Debug,
    {
        use alloc::collections::BinaryHeap;

        let heap = BinaryHeap::<T>::decode(&mut Decoder(cbor)).unwrap();
        let mut buf = Vec::new();
        heap.encode(&mut Encoder(&mut buf)).unwrap();
        assert_eq!(heap.cbor_len(), buf.len());
        assert_eq!(heap.into_sorted_vec(), expected);
    }

    #[test]
    fn definite() {
        #[cfg(feature = "alloc")]
        {
            use alloc::{collections::*, string::String, vec::Vec};

            assert!(test::<Vec<&str>>(Vec::new(), EMPTY_ARRAY).unwrap());
            assert!(
                test(
                    vec!["a", "b", "c"],
                    &[0x83, 0x61, 0x61, 0x61, 0x62, 0x61, 0x63]
                )
                .unwrap()
            );

            assert!(test::<VecDeque<String>>(VecDeque::new(), EMPTY_ARRAY).unwrap());
            assert!(
                test(
                    VecDeque::from([String::from("hi"), String::from("yo")]),
                    &[0x82, 0x62, 0x68, 0x69, 0x62, 0x79, 0x6f]
                )
                .unwrap()
            );

            assert!(test::<LinkedList<Option<i32>>>(LinkedList::new(), EMPTY_ARRAY).unwrap());
            assert!(
                test(
                    LinkedList::from([Some(-5), None, Some(10)]),
                    &[0x83, 0x24, 0xf6, 0x0a]
                )
                .unwrap()
            );

            test_binary_heap::<usize>(EMPTY_ARRAY, &[]);
            test_binary_heap::<usize>(
                &[0x83, 0x18, 0x64, 0x18, 0xc8, 0x18, 0x96],
                &[100, 150, 200],
            );

            assert!(test::<BTreeSet<i32>>(BTreeSet::new(), EMPTY_ARRAY).unwrap());
            assert!(
                test(
                    BTreeSet::from([-10, 0, 10, 20]),
                    &[0x84, 0x29, 0x00, 0x0a, 0x14]
                )
                .unwrap()
            );
        }

        #[cfg(feature = "std")]
        {
            use std::collections::HashSet;
            assert!(test::<HashSet<&str>>(HashSet::new(), EMPTY_ARRAY).unwrap());
            test(
                HashSet::from(["foo", "bar"]),
                &[0x82, 0x63, 0x66, 0x6f, 0x6f, 0x63, 0x62, 0x61, 0x72],
            )
            .unwrap();
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn indefinite() {
        use alloc::{collections::*, string::String, vec::Vec};

        assert!(!test::<Vec<&str>>(Vec::new(), EMPTY_INDEF).unwrap());
        assert!(!test(vec!["x", "y"], &[0x9f, 0x61, 0x78, 0x61, 0x79, 0xff]).unwrap());

        assert!(!test::<VecDeque<String>>(VecDeque::new(), EMPTY_INDEF).unwrap());
        assert!(
            !test(
                VecDeque::from([String::from("a")]),
                &[0x9f, 0x61, 0x61, 0xff]
            )
            .unwrap()
        );

        assert!(!test::<LinkedList<Option<i32>>>(LinkedList::new(), EMPTY_INDEF).unwrap());
        assert!(!test(LinkedList::from([Some(1), None]), &[0x9f, 0x01, 0xf6, 0xff]).unwrap());

        test_binary_heap::<usize>(EMPTY_INDEF, &[]);
        test_binary_heap::<usize>(&[0x9f, 0x18, 0x32, 0x18, 0x64, 0xff], &[50, 100]);

        assert!(!test::<BTreeSet<i32>>(BTreeSet::new(), EMPTY_INDEF).unwrap());
        assert!(!test(BTreeSet::from([5, 10]), &[0x9f, 0x05, 0x0a, 0xff]).unwrap());

        #[cfg(feature = "std")]
        {
            use std::collections::HashSet;
            assert!(!test::<HashSet<&str>>(HashSet::new(), EMPTY_INDEF).unwrap());
            assert!(
                !test(
                    HashSet::from(["test"]),
                    &[0x9f, 0x64, 0x74, 0x65, 0x73, 0x74, 0xff]
                )
                .unwrap()
            );
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn nested() {
        use alloc::{string::String, vec};
        assert!(
            test(
                vec![
                    vec![String::from("a")],
                    vec![String::from("b"), String::from("c")]
                ],
                &[0x82, 0x81, 0x61, 0x61, 0x82, 0x61, 0x62, 0x61, 0x63]
            )
            .unwrap()
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn long() {
        use alloc::vec::Vec;
        let mut cbor = vec![0x98, 25];
        for i in 0..25 {
            cbor.push(0x18);
            cbor.push(i);
        }
        assert!(!test((0..25).map(|i| i as usize).collect::<Vec<usize>>(), &cbor).unwrap());
    }
}
