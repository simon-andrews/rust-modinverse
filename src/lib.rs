//! Small library for finding the modular multiplicative inverses. Also has an implementation of
//! the extended Euclidean algorithm built in.

extern crate num_integer;

use num_integer::Integer;

/// Implementation of the [extended Euclidean
/// algorithm](https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm).
///
/// The first argument should be smaller than the second. This is checked with an `assert!()`.
///
/// ```
/// use modinverse::egcd;
///
/// let smaller = 3;
/// let larger = 26;
/// let (g, x, y) = egcd(smaller, larger);
///
/// assert_eq!(g, 1); // Greatest common denominator
/// assert_eq!(x, 9); // Bézout coefficient x
/// assert_eq!(y, -1); // Bézout coefficient y
/// assert_eq!((smaller * x) + (larger * y), g); // Make sure it all works out according to plan
/// ```
pub fn egcd<T: Copy + Integer>(a: T, b: T) -> (T, T, T) {
    assert!(a < b);
    if a == T::zero() {
        return (b, T::zero(), T::one());
    }
    else {
        let (g, x, y) = egcd(b % a, a);
        return (g, y - (b / a) * x, x);
    }
}

/// Function to calculate the [modular multiplicative
/// inverse](https://en.wikipedia.org/wiki/Modular_multiplicative_inverse) of an integer *a* modulo
/// *m*.
///
/// A modular multiplicative inverse may not exist. If that is the case, this function will return
/// `None`. Otherwise, the inverse will be returned wrapped up in a `Some`.
///
/// ```
/// use modinverse::modinverse;
///
/// let does_exist = modinverse(3, 26);
/// let does_not_exist = modinverse(4, 32);
///
/// match does_exist {
///   Some(i) => assert_eq!(i, 9),
///   None => panic!("modinverse() didn't work as expected"),
/// }
///
/// match does_not_exist {
///   Some(i) => panic!("modinverse() found an inverse when it shouldn't have"),
///   None => {},
/// }
pub fn modinverse<T: Copy + Integer>(a: T, m: T) -> Option<T> {
    let (g, x, _) = egcd(a, m);
    if g != T::one() {
        return None;
    }
    else {
        return Some(x % m);
    }
}
