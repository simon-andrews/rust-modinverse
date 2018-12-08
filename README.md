rust-modinverse
===============
Small library for finding the modular multiplicative inverses. Also has an implementation of the extended Euclidean algorithm built in.

`modinverse`
------------
Calculates the [modular multiplicative
inverse](https://en.wikipedia.org/wiki/Modular_multiplicative_inverse) *x* of
an integer *a* such that *ax* ≡ 1 (mod *m*).

Such an integer may not exist. If so, this function will return `None`.
Otherwise, the inverse will be returned wrapped up in a `Some`.

```rust
use modinverse::modinverse;

let does_exist = modinverse(3, 26);
let does_not_exist = modinverse(4, 32);

match does_exist {
    Some(x) => assert_eq!(x, 9),
    None => panic!("modinverse() didn't work as expected"),
}

match does_not_exist {
   Some(x) => panic!("modinverse() found an inverse when it shouldn't have"),
   None => {},
}
```

`egcd`
------
Finds the greatest common denominator of two integers *a* and *b*, and two
integers *x* and *y* such that *ax* + *by* is the greatest common denominator
of *a* and *b* (Bézout coefficients).

This function is an implementation of the [extended Euclidean
algorithm](https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm).

```rust
use modinverse::egcd;

let a = 26;
let b = 3;
let (g, x, y) = egcd(a, b);

assert_eq!(g, 1);
assert_eq!(x, -1);
assert_eq!(y, 9);
assert_eq!((a * x) + (b * y), g);
```
