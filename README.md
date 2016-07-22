rust-modinverse
===============
Small library for finding the modular multiplicative inverses. Also has an implementation of the extended Euclidean algorithm built in.

`egcd`
------
Implementation of the [extended Euclidean algorithm](https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm).

The first argument should be smaller than the second. This is checked with an `assert!()`.

```rust
use modinverse::egcd;

let smaller = 3;
let larger = 26;
let (g, x, y) = egcd(smaller, larger);

assert_eq!(g, 1); // Greatest common denominator
assert_eq!(x, 9); // Bézout coefficient x
assert_eq!(y, -1); // Bézout coefficient y
assert_eq!((smaller * x) + (larger * y), g); // Make sure it all works out according to plan
```

`modinverse`
------------
Function to calculate the [modular multiplicative inverse](https://en.wikipedia.org/wiki/Modular_multiplicative_inverse) of an integer *a* modulo *m*.

A modular multiplicative inverse may not exist. If that is the case, this function will return `None`. Otherwise, the inverse will be returned wrapped up in a `Some`.

```rust
use modinverse::modinverse;

let does_exist = modinverse(3, 26);
let does_not_exist = modinverse(4, 32);

match does_exist {
  Some(i) => assert_eq!(i, 9),
  None => panic!("modinverse() didn't work as expected"),
}

match does_not_exist {
  Some(i) => panic!("modinverse() found an inverse when it shouldn't have"),
  None => {},
}
```
