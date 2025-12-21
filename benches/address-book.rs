use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use rand::distr::Alphanumeric;
use rand::prelude::*;
use serde::{Deserialize, Serialize};
use std::{borrow::Cow, iter};
use tinycbor_derive::{Decode, Encode};
use tinycbor::{Decode, Encode, Encoder};

#[derive(Debug, Encode, Decode, Serialize, Deserialize)]
struct AddressBook<'a> {
    timestamp: u64,
    #[serde(borrow)]
    entries: Vec<Entry<'a>>,
    #[serde(borrow)]
    style: Option<Style<'a>>,
    rating: Option<f64>,
}

#[derive(Debug, Encode, Decode, Serialize, Deserialize)]
#[cbor(error = "EntryError")]
struct Entry<'a> {
    #[serde(borrow)]
    firstname: Cow<'a, str>,
    #[serde(borrow)]
    lastname: Cow<'a, str>,
    birthday: u32,
    #[serde(borrow)]
    addresses: Vec<Address<'a>>,
}

#[derive(Debug, Encode, Decode, Serialize, Deserialize)]
#[cbor(error = "AddressError")]
struct Address<'a> {
    #[serde(borrow)]
    street: Cow<'a, str>,
    #[serde(borrow)]
    houseno: Cow<'a, str>,
    postcode: u32,
    #[serde(borrow)]
    city: Cow<'a, str>,
    #[serde(borrow)]
    country: Cow<'a, str>,
}

#[derive(Debug, Encode, Decode, Serialize, Deserialize)]
#[cbor(error = "StyleError")]
enum Style<'a> {
    #[n(0)]
    Version1,
    #[n(1)]
    Version2,
    #[n(2)]
    Version3(bool, u64),
    #[n(3)]
    Version4 {
        #[serde(borrow)]
        path: Cow<'a, str>,
        timestamp: u64,
    },
}

fn cbor4ii(c: &mut Criterion) {
    let book = gen_addressbook(16);
    let bytes = cbor4ii::serde::to_vec(Vec::new(), &book).unwrap();
    let mut buf = Vec::with_capacity(32 * 1024);

    c.bench_with_input(BenchmarkId::new("encode/cbor4ii", ""), &book, |b, book| {
        buf.clear();
        b.iter(|| {
            cbor4ii::serde::to_writer(&mut buf, book).unwrap()
        });
    });

    c.bench_with_input(BenchmarkId::new("decode/cbor4ii", ""), &bytes, |b, bytes| {
        b.iter(|| {
            cbor4ii::serde::from_slice::<AddressBook>(bytes).unwrap()
        });
    });
}

fn tinycbor(c: &mut Criterion) {
    let book = gen_addressbook(16);
    let bytes = tinycbor::to_vec(&book);
    let mut buf = Vec::with_capacity(32 * 1024);

    c.bench_with_input(BenchmarkId::new("encode/tinycbor", ""), &book, |b, book| {
        buf.clear();
        b.iter(|| {
            let Ok(()) = book.encode(&mut Encoder(&mut buf));
        });
    });
    c.bench_with_input(BenchmarkId::new("decode/tinycbor", ""), &bytes, |b, bytes| {
        b.iter(|| {
            let mut d = tinycbor::Decoder(bytes);
            AddressBook::decode(&mut d).unwrap();
        });
    });
}

fn gen_addressbook(n: usize) -> AddressBook<'static> {
    fn gen_string(g: &mut ThreadRng) -> Cow<'static, str> {
        Cow::Owned(
            iter::repeat_with(|| char::from(g.sample(Alphanumeric)))
                .take(128)
                .collect(),
        )
    }

    fn gen_address(g: &mut ThreadRng) -> Address<'static> {
        Address {
            street: gen_string(g),
            houseno: gen_string(g),
            postcode: g.random(),
            city: gen_string(g),
            country: gen_string(g),
        }
    }

    fn gen_style(g: &mut ThreadRng) -> Option<Style<'static>> {
        let s = match g.random_range(0..5) {
            0 => return None,
            1 => Style::Version1,
            2 => Style::Version2,
            3 => Style::Version3(g.random(), g.random()),
            4 => Style::Version4 {
                path: gen_string(g),
                timestamp: g.random(),
            },
            _ => unreachable!(),
        };
        Some(s)
    }

    fn gen_entry(g: &mut ThreadRng, n: usize) -> Entry<'static> {
        Entry {
            firstname: gen_string(g),
            lastname: gen_string(g),
            birthday: g.random(),
            addresses: {
                let mut v = Vec::with_capacity(n);
                for _ in 0..n {
                    v.push(gen_address(g))
                }
                v
            },
        }
    }

    let mut g = rand::rng();

    AddressBook {
        timestamp: g.random(),
        entries: {
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(gen_entry(&mut g, n))
            }
            v
        },
        style: gen_style(&mut g),
        rating: if g.random() {
            Some(g.random_range(-2342.42342..234423.2342))
        } else {
            None
        },
    }
}

criterion_group!(benches, cbor4ii, tinycbor);
criterion_main!(benches);
