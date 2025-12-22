use crate::Encoder;
use crate::{CborLen, Decode, Decoder, Encode, primitive};

impl<T: Encode + ?Sized> Encode for &T {
    fn encode<W: embedded_io::Write>(&self, e: &mut crate::Encoder<W>) -> Result<(), W::Error> {
        (*self).encode(e)
    }
}

impl<T: CborLen + ?Sized> CborLen for &T {
    fn cbor_len(&self) -> usize {
        (*self).cbor_len()
    }
}

impl<T: Encode + ?Sized> Encode for &mut T {
    fn encode<W: embedded_io::Write>(&self, e: &mut crate::Encoder<W>) -> Result<(), W::Error> {
        (**self).encode(e)
    }
}

impl<T: CborLen + ?Sized> CborLen for &mut T {
    fn cbor_len(&self) -> usize {
        (**self).cbor_len()
    }
}

#[cfg(feature = "alloc")]
impl<'b, T: Decode<'b>> Decode<'b> for alloc::boxed::Box<T> {
    type Error = T::Error;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, T::Error> {
        T::decode(d).map(alloc::boxed::Box::new)
    }
}

#[cfg(feature = "alloc")]
impl<T: Encode + ?Sized> Encode for alloc::boxed::Box<T> {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        (**self).encode(e)
    }
}

#[cfg(feature = "alloc")]
impl<T: CborLen + ?Sized> CborLen for alloc::boxed::Box<T> {
    fn cbor_len(&self) -> usize {
        (**self).cbor_len()
    }
}

#[cfg(feature = "alloc")]
impl<'a, 'b, T> Decode<'b> for alloc::borrow::Cow<'a, T>
where
    T: alloc::borrow::ToOwned + ?Sized + 'a,
    &'a T: Decode<'b>,
    T::Owned: Decode<'b>,
{
    type Error = <T::Owned as Decode<'b>>::Error;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        if let Ok(borrowed) = <&'a T>::decode(d) {
            return Ok(alloc::borrow::Cow::Borrowed(borrowed));
        }

        Ok(alloc::borrow::Cow::Owned(T::Owned::decode(d)?))
    }
}

#[cfg(feature = "alloc")]
impl<T> Encode for alloc::borrow::Cow<'_, T>
where
    T: Encode + alloc::borrow::ToOwned + ?Sized,
{
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        self.as_ref().encode(e)
    }
}

#[cfg(feature = "alloc")]
impl<T> CborLen for alloc::borrow::Cow<'_, T>
where
    T: CborLen + alloc::borrow::ToOwned + ?Sized,
{
    fn cbor_len(&self) -> usize {
        self.as_ref().cbor_len()
    }
}

impl<'a, T: Decode<'a>> Decode<'a> for Option<T> {
    type Error = T::Error;

    fn decode(d: &mut Decoder<'a>) -> Result<Self, T::Error> {
        if Ok(crate::Type::Null) == d.datatype() {
            d.read().expect("NULL was peeked");
            return Ok(None);
        }
        T::decode(d).map(Some)
    }
}

impl<T: Encode> Encode for Option<T> {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        if let Some(x) = self {
            x.encode(e)?;
        } else {
            primitive::Null.encode(e)?;
        }
        Ok(())
    }
}

impl<T: CborLen> CborLen for Option<T> {
    fn cbor_len(&self) -> usize {
        if let Some(x) = self { x.cbor_len() } else { 1 }
    }
}

impl<'b, T: Decode<'b>> Decode<'b> for core::num::Wrapping<T> {
    type Error = T::Error;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        T::decode(d).map(core::num::Wrapping)
    }
}

impl<T: Encode> Encode for core::num::Wrapping<T> {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        self.0.encode(e)
    }
}

impl<T: CborLen> CborLen for core::num::Wrapping<T> {
    fn cbor_len(&self) -> usize {
        self.0.cbor_len()
    }
}

impl<'b, T: Decode<'b>> Decode<'b> for core::cell::Cell<T> {
    type Error = T::Error;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        T::decode(d).map(core::cell::Cell::new)
    }
}

impl<T: Encode + Copy> Encode for core::cell::Cell<T> {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        self.get().encode(e)
    }
}

impl<T: CborLen + Copy> CborLen for core::cell::Cell<T> {
    fn cbor_len(&self) -> usize {
        self.get().cbor_len()
    }
}

impl<'b, T: Decode<'b>> Decode<'b> for core::cell::RefCell<T> {
    type Error = T::Error;

    fn decode(d: &mut Decoder<'b>) -> Result<Self, Self::Error> {
        T::decode(d).map(core::cell::RefCell::new)
    }
}

impl<T: Encode + ?Sized> Encode for core::cell::RefCell<T> {
    fn encode<W: embedded_io::Write>(&self, e: &mut Encoder<W>) -> Result<(), W::Error> {
        self.borrow().encode(e)
    }
}

impl<T: CborLen + ?Sized> CborLen for core::cell::RefCell<T> {
    fn cbor_len(&self) -> usize {
        self.borrow().cbor_len()
    }
}

#[cfg(test)]
mod tests {
    use crate::test;

    #[test]
    fn option() {
        assert!(test::<Option<u32>>(None, &[0xf6]).unwrap());
        assert!(test::<Option<u32>>(Some(42), &[0x18, 0x2a]).unwrap());
        assert!(test::<Option<i32>>(Some(-100), &[0x38, 0x63]).unwrap());
        assert!(test::<Option<&str>>(None, &[0xf6]).unwrap());
        assert!(
            test::<Option<&str>>(Some("hello"), &[0x65, 0x68, 0x65, 0x6c, 0x6c, 0x6f]).unwrap()
        );

        #[cfg(feature = "alloc")]
        {
            use alloc::string::String;
            assert!(test::<Option<String>>(None, &[0xf6]).unwrap());
            assert!(
                test::<Option<String>>(Some(String::from("test")), &[0x64, 0x74, 0x65, 0x73, 0x74])
                    .unwrap()
            );
        }
    }
}
