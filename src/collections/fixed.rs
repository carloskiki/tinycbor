//! Fixed length collections and structures.
use core::mem::MaybeUninit;

use crate::{CborLen, Decode, Decoder, Encode};

/// An error that can occur when decoding fixed length structures and collections.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Error<E> {
    /// Not enough elements.
    Missing,
    /// Unexpected surplus elements.
    Surplus,
    /// Either the header or an element caused an error.
    Collection(super::Error<E>),
}

impl<E> Error<E> {
    /// Map a function on the inner error.
    pub fn map<O>(self, f: impl FnOnce(E) -> O) -> Error<O> {
        match self {
            Error::Missing => Error::Missing,
            Error::Surplus => Error::Surplus,
            Error::Collection(e) => Error::Collection(e.map(f)),
        }
    }
}

impl<E: core::fmt::Display> core::fmt::Display for Error<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Missing => write!(f, "missing elements"),
            Error::Surplus => write!(f, "too many elements"),
            Error::Collection(e) => write!(f, "{e}"),
        }
    }
}

impl<E> From<super::Error<E>> for Error<E> {
    fn from(e: super::Error<E>) -> Self {
        Error::Collection(e)
    }
}

impl<E: core::error::Error + 'static> core::error::Error for Error<E> {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Error::Missing => None,
            Error::Surplus => None,
            Error::Collection(e) => Some(e),
        }
    }
}

// Guard to prevent memory leaks in the case of a panic during decoding. This is not
// strictly nessessary as leaks are allowed in the Rust memory safety model, but this is
// nice to have if a dependent decides to catch unwinding panics. Our library won't cause a
// memory leak in that case.
struct Guard<T, const N: usize> {
    data: [MaybeUninit<T>; N],
    initialized: usize,
}

impl<T, const N: usize> Guard<T, N> {
    /// Safety: Caller must ensure that all elements up to `count` are initialized.
    unsafe fn assume_init(mut self) -> [T; N] {
        let data = core::mem::replace(&mut self.data, [const { MaybeUninit::uninit() }; N]);
        // Don't drop the guard anymore, becuase it contains uninitialized elements.
        let _ = core::mem::ManuallyDrop::new(self);

        // Safety: Caller has ensured that all elements are initialized.
        unsafe { data.as_ptr().cast::<[T; N]>().read() }
    }
}

impl<T, const N: usize> Drop for Guard<T, N> {
    fn drop(&mut self) {
        for i in 0..self.initialized {
            // Safety: We only drop initialized elements.
            unsafe { self.data[i].assume_init_drop() };
        }
    }
}

impl<'a, T, const N: usize> Decode<'a> for [T; N]
where
    T: Decode<'a>,
{
    type Error = Error<T::Error>;

    fn decode(d: &mut Decoder<'a>) -> Result<Self, Self::Error> {
        let mut visitor = d.array_visitor().map_err(super::Error::Malformed)?;
        let mut guard = Guard {
            data: [const { MaybeUninit::uninit() }; N],
            initialized: 0,
        };

        for elem in &mut guard.data {
            elem.write(
                visitor
                    .visit::<T>()
                    .ok_or(Error::Missing)?
                    .map_err(super::Error::Element)?,
            );
            guard.initialized += 1;
        }
        // Safety: All elements have been initialized.
        let array = unsafe { guard.assume_init() };

        if visitor.remaining() != Some(0) {
            return Err(Error::Surplus);
        }

        Ok(array)
    }
}

impl<T: Encode, const N: usize> Encode for [T; N] {
    fn encode<W: embedded_io::Write>(&self, e: &mut crate::Encoder<W>) -> Result<(), W::Error> {
        e.array(N)?;
        for item in self {
            item.encode(e)?;
        }
        Ok(())
    }
}

impl<T: CborLen, const N: usize> CborLen for [T; N] {
    fn cbor_len(&self) -> usize {
        N.cbor_len() + self.iter().map(|x| x.cbor_len()).sum::<usize>()
    }
}

// Map encoding

impl<'a, K, V, const N: usize> Decode<'a> for [(K, V); N]
where
    K: Decode<'a>,
    V: Decode<'a>,
{
    type Error = Error<super::map::Error<K::Error, V::Error>>;

    fn decode(d: &mut Decoder<'a>) -> Result<Self, Self::Error> {
        let mut visitor = d.map_visitor().map_err(super::Error::Malformed)?;
        let mut guard = Guard {
            data: [const { MaybeUninit::uninit() }; N],
            initialized: 0,
        };

        for elem in &mut guard.data {
            let v = visitor
                .visit()
                .ok_or(Error::Missing)?
                .map_err(super::Error::Element)?;
            elem.write(v);
            guard.initialized += 1;
        }
        // Safety: All elements have been initialized.
        let array = unsafe { guard.assume_init() };

        if visitor.remaining() != Some(0) {
            return Err(Error::Surplus);
        }
        Ok(array)
    }
}

impl<K: Encode, V: Encode, const N: usize> Encode for [(K, V); N] {
    fn encode<W: embedded_io::Write>(&self, e: &mut crate::Encoder<W>) -> Result<(), W::Error> {
        e.map(N)?;
        for (k, v) in self {
            k.encode(e)?;
            v.encode(e)?;
        }
        Ok(())
    }
}

impl<K: CborLen, V: CborLen, const N: usize> CborLen for [(K, V); N] {
    fn cbor_len(&self) -> usize {
        N.cbor_len()
            + self
                .iter()
                .map(|(k, v)| k.cbor_len() + v.cbor_len())
                .sum::<usize>()
    }
}

#[cfg(test)]
mod tests {
    use crate::{Decode, Decoder, test};

    const EMPTY_ARRAY: &[u8] = &[0x80];

    #[test]
    fn empty() {
        assert!(test::<[isize; 0]>([], EMPTY_ARRAY).unwrap());
        assert!(test::<[i32; 0]>([], EMPTY_ARRAY).unwrap());
    }

    #[test]
    fn small() {
        assert!(test([42u16], &[0x81, 0x18, 0x2a]).unwrap());
        assert!(test([true], &[0x81, 0xf5]).unwrap());
        assert!(test([-1i32], &[0x81, 0x20]).unwrap());

        assert!(test([1usize, 2usize], &[0x82, 0x01, 0x02]).unwrap());
        assert!(test([true, false], &[0x82, 0xf5, 0xf4]).unwrap());

        assert!(test(["a", "b", "c"], &[0x83, 0x61, 0x61, 0x61, 0x62, 0x61, 0x63]).unwrap());
    }

    #[test]
    fn nested() {
        assert!(
            test(
                [[1u64, 2], [3, 4]],
                &[0x82, 0x82, 0x01, 0x02, 0x82, 0x03, 0x04]
            )
            .unwrap()
        );

        assert!(
            test(
                [[[1u64, 2], [3, 4]], [[5, 6], [7, 8]]],
                &[
                    0x82, 0x82, 0x82, 0x01, 0x02, 0x82, 0x03, 0x04, 0x82, 0x82, 0x05, 0x06, 0x82,
                    0x07, 0x08
                ]
            )
            .unwrap()
        );
    }

    #[test]
    fn missing() {
        use super::Error;
        let cbor = &[0x82, 0x01, 0x02];
        let result = <[u16; 3]>::decode(&mut Decoder(cbor));
        assert!(matches!(result, Err(Error::Missing)));
    }

    #[test]
    fn surplus() {
        use super::Error;
        let cbor = &[0x83, 0x01, 0x02, 0x03];
        let result = <[u16; 2]>::decode(&mut Decoder(cbor));
        assert!(matches!(result, Err(Error::Surplus)));
    }

    #[test]
    fn long() {
        let arr: [u32; 25] = core::array::from_fn(|i| i as u32);
        let mut cbor = vec![0x98, 25];
        for i in 0..25 {
            if i < 24 {
                cbor.push(i as u8);
            } else {
                cbor.push(0x18);
                cbor.push(i as u8);
            }
        }

        assert!(test(arr, &cbor).unwrap());
    }

    #[test]
    fn map() {
        assert!(
            test(
                [("a", 1u16), ("b", 2u16)],
                &[0xA2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x02]
            )
            .unwrap()
        );
    }
}
