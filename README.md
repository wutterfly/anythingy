# Anything

**This is a work-in-progess project and not for production use.**

A library for dynamic typing. It's main feature is the *Thing* type, that works similar to *Box\<dyn Any\>*, but can be sized at compile time while falling back to boxing the value, if it's too big.


## Example


```rust
use anything::Thing;
fn main() {
    let number_thing: Thing<24> = Thing::new(42u64);
    let sting_thing: Thing<24> = Thing::new(String::from("Hello there"));
    let bytes_thing: Thing<24> = Thing::new(Vec::from(b"so uncivilized"));

    let number = number_thing.get::<u64>();
    assert_eq!(number, 42);

    let string = sting_thing.get::<String>();
    assert_eq!(&string, "Hello there");

    let bytes = bytes_thing.get::<Vec<u8>>();
    assert_eq!(&bytes, b"so uncivilized");
  }
```


## Licence
This project is licensed under the [MIT license](./LICENSE).