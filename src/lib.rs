//! Small library for finding the modular multiplicative inverses. Also has an implementation of
//! the extended Euclidean algorithm built in.

extern crate num_integer;

use num_integer::Integer;

/// Finds the greatest common denominator of two integers *a* and *b*, and two
/// integers *x* and *y* such that *ax* + *by* is the greatest common
/// denominator of *a* and *b* (Bézout coefficients).
///
/// This function is an implementation of the [extended Euclidean
/// algorithm](https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm).
///
///
/// ```
/// use modinverse::egcd;
///
/// let a = 26;
/// let b = 3;
/// let (g, x, y) = egcd(a, b);
///
/// assert_eq!(g, 1);
/// assert_eq!(x, -1);
/// assert_eq!(y, 9);
/// assert_eq!((a * x) + (b * y), g);
/// ```
pub fn egcd<T: Clone + Integer>(a: T, b: T) -> (T, T, T) {
    if a.is_zero() {
        (b, T::zero(), T::one())
    } else {
        let (g, x, y) = egcd(b.clone() % a.clone(), a.clone());
        (g, y - (b / a) * x.clone(), x)
    }
}

/// Calculates the floor modulus. This is identical to the remainder for unsigned integers, but is
/// different for signed values; see https://en.wikipedia.org/wiki/Modulo_operation and
/// https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/divmodnote-letter.pdf.
///
/// ```
/// use modinverse::mod_floor;
///
/// assert_eq!(mod_floor(5, 3), 2);
/// assert_eq!(mod_floor(-5, 3), 1);
/// assert_eq!(mod_floor(5, -3), -1);
/// assert_eq!(mod_floor(-5, -3), -2);
pub fn mod_floor<T: Clone + Integer>(a: T, m: T) -> T {
    (a % m.clone() + m.clone()) % m
}

/// Calculates the [modular multiplicative
/// inverse](https://en.wikipedia.org/wiki/Modular_multiplicative_inverse) *x*
/// of an integer *a* such that *ax* ≡ 1 (mod *m*).
///
/// Such an integer may not exist. If so, this function will return `None`.
/// Otherwise, the inverse will be returned wrapped up in a `Some`.
///
/// ```
/// use modinverse::modinverse;
///
/// let does_exist = modinverse(3, 26);
/// let does_not_exist = modinverse(4, 32);
///
/// match does_exist {
///   Some(x) => assert_eq!(x, 9),
///   None => panic!("modinverse() didn't work as expected"),
/// }
///
/// match does_not_exist {
///   Some(x) => panic!("modinverse() found an inverse when it shouldn't have"),
///   None => {},
/// }
pub fn modinverse<T: Clone + Integer>(a: T, m: T) -> Option<T> {
    let (g, x, _) = egcd(a, m.clone());
    if !g.is_one() {
        None
    } else {
        Some(mod_floor(x, m))
    }
}
