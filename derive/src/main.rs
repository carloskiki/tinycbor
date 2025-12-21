use tinycbor::{Decoder, Token, to_vec};
use tinycbor_derive::{Decode, Encode};

#[derive(Encode, Decode, PartialEq)]
#[cbor(map)]
struct Account {
    #[n(0)]
    email: String,
    #[n(1)]
    username: Option<String>,
    #[n(2)]
    password_hash: [u8; 32],
}

fn main() {
    let encoded = to_vec(&Account {
        email: "me@yahoo.com".to_string(),
        username: None,
        password_hash: [0u8; 32],
    });
    let tokens = Decoder(&encoded).collect::<Result<Vec<_>, _>>().unwrap();

    assert_eq!(
        tokens,
        vec![
            Token::Map(2),
            Token::Int(0u8.into()),
            Token::String("me@yahoo.com"),
            Token::Int(2u8.into()),
            Token::Bytes(&[0u8; 32]),
        ]
    );
}
