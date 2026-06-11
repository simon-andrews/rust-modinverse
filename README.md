rust-modinverse
===============

Small `no_std` library for computing [modular multiplicative
inverses](https://en.wikipedia.org/wiki/Modular_multiplicative_inverse). Also exposes an
[extended Euclidean](https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm) primitive.

Every fixed-width path (`u8`–`u128`, `i8`–`i128`, `usize`, `isize`) is mechanically verified,
end to end: the Rust is extracted to Lean 4 (Charon + Aeneas) and, for each width, the
extracted `modinverse` is proved to never error and to be sound, canonically bounded, complete,
and failing exactly when no inverse exists. What "correct" means is pinned down by the
human-maintained spec in [`proof/ModInverse.lean`](proof/ModInverse.lean); the trusted gate in
[`proof/Gate.lean`](proof/Gate.lean) holds the build to those statements and audits the axioms
every certificate depends on. The `bigint` paths and the free `egcd` are covered by tests
(exhaustive over small moduli, plus near-`T::MAX`/`T::MIN` regressions) rather than proof.

The `ModInverse` trait
----------------------

`ModInverse` is implemented for every built-in integer type — `i8`–`i128`, `u8`–`u128`,
`isize`, `usize` — and (behind the `bigint` feature) for `num_bigint::BigInt` and
`num_bigint::BigUint`.

```rust
use modinverse::modinverse;

assert_eq!(modinverse(3, 26), Some(9));
assert_eq!(modinverse(4, 32), None);

// Works on unsigned types too:
assert_eq!(modinverse(3u64, 26u64), Some(9));

// Negative modulus is canonicalized to [0, |m|):
assert_eq!(modinverse(3i32, -26), Some(9));
```

`egcd`
------

Free function returning `(gcd(a, b), x, y)` such that `ax + by = gcd(a, b)` (Bézout
coefficients).

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

For fixed-width signed types, `egcd` is not safe at or near `T::MIN`: intermediates like
`T::MIN / -1` overflow. The crate's own `ModInverse` impls dodge this by widening one step
first. If you call `egcd` directly, stay away from `T::MIN`.

Features
--------

- **`bigint`** — enables `ModInverse` for `num_bigint::BigInt` and `num_bigint::BigUint`.

`no_std`
--------

The crate is `#![no_std]` with no allocator requirement. The `bigint` feature pulls in
`num-bigint` (with its default features off), which itself requires `alloc`.
