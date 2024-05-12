# Anythingy

[![Rust](https://github.com/wutterfly/anything/actions/workflows/rust.yml/badge.svg)](https://github.com/wutterfly/anything/actions/workflows/rust.yml)

**This is a work-in-progess project and not for production use.**

*Thingy: a [..] thing whose name one has forgotten, does not know, or does not wish to mention.* [from Oxford Languages]

A library for dynamic typing. It's main feature is the *Thing* type, that works similar to *Box\<dyn Any\>*, but can be sized at compile time while falling back to boxing the value, if it's too big.


## Example


```rust
use anything::Thing;
fn main() {
    let number_thing: Thing<24> = Thing::new(42u64);
    let string_thing: Thing<24> = Thing::new(String::from("Hello there"));
    let bytes_thing: Thing<24> = Thing::new(Vec::from(b"so uncivilized"));

    let number = number_thing.get::<u64>();
    assert_eq!(number, 42);

    let string = string_thing.get::<String>();
    assert_eq!(&string, "Hello there");

    let bytes = bytes_thing.get::<Vec<u8>>();
    assert_eq!(&bytes, b"so uncivilized");
  }
```


## Licence
This project is licensed under the [MIT license](./LICENSE).