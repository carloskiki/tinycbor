use tinycbor::{CborLen as _, Decode as _, Decoder};

#[test]
fn f32_nan_patterns_use_binary16() {
    let values = [
        f32::NAN,
        f32::from_bits(0xffc0_0000),
        f32::from_bits(0x7f80_0001),
        f32::from_bits(0x7fff_ffff),
    ];

    for value in values {
        assert_eq!(value.cbor_len(), 3);

        let encoded = tinycbor::to_vec(&value);
        assert_eq!(encoded.len(), 3);
        assert_eq!(encoded[0], 0xf9);
        assert!(f32::decode(&mut Decoder(&encoded)).unwrap().is_nan());
    }
}
