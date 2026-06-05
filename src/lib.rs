//! Small library for finding the modular multiplicative inverses. Also has an implementation of
//! the extended Euclidean algorithm built in.

#![no_std]

use num_integer::Integer;
use num_traits::Signed;

/// Finds the greatest common denominator of two integers *a* and *b*, and two
/// integers *x* and *y* such that *ax* + *by* is the greatest common
/// denominator of *a* and *b* (Bézout coefficients).
///
/// This function is a transcription of Wikipedia's iterative pseudocode for the
/// [extended Euclidean
/// algorithm](https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm#Pseudocode).
///
/// The recursive version is more elegant but blows the stack on adversarial
/// BigInt inputs.
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
pub fn egcd<T: Clone + Integer + Signed>(a: T, b: T) -> (T, T, T) {
    let (mut old_r, mut r) = (a, b);
    let (mut old_s, mut s) = (T::one(), T::zero());
    let (mut old_t, mut t) = (T::zero(), T::one());
    while !r.is_zero() {
        let q = old_r.clone() / r.clone();
        let new_r = old_r - q.clone() * r.clone();
        (old_r, r) = (r, new_r);
        let new_s = old_s - q.clone() * s.clone();
        (old_s, s) = (s, new_s);
        let new_t = old_t - q * t.clone();
        (old_t, t) = (t, new_t);
    }
    (old_r, old_s, old_t)
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
/// ```
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
/// ```
pub fn modinverse<T: Clone + Integer + Signed>(a: T, m: T) -> Option<T> {
    let a = mod_floor(a, m.clone());
    let (g, x, _) = egcd(a, m.clone());
    if !g.is_one() {
        None
    } else {
        Some(mod_floor(x, m))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    #[test]
    fn modinverse_basic() {
        assert_eq!(modinverse(3, 26), Some(9));
        assert_eq!(modinverse(4, 32), None);
    }

    #[test]
    fn modinverse_negative_a() {
        // -3 ≡ 23 (mod 26), and 23 * 17 ≡ 1 (mod 26)
        assert_eq!(modinverse(-3, 26), Some(17));
    }

    #[test]
    fn modinverse_a_larger_than_m() {
        assert_eq!(modinverse(29, 26), Some(9));
    }

    #[test]
    fn modinverse_bigint() {
        let a = BigInt::from(3);
        let m = BigInt::from(26);
        assert_eq!(modinverse(a, m), Some(BigInt::from(9)));
    }

    #[test]
    fn egcd_iterative_no_stack_overflow_on_fibonacci_bigints() {
        // egcd's recursive form blew the stack on adversarial Fibonacci-style BigInt inputs.
        // This locks in the iterative rewrite: 2000 Fibonacci levels would overflow most stacks
        // in the recursive form but is trivial iteratively.
        let (mut a, mut b) = (BigInt::from(1), BigInt::from(1));
        for _ in 0..2000 {
            let next = &a + &b;
            a = core::mem::replace(&mut b, next);
        }
        let (g, _, _) = egcd(a, b);
        assert_eq!(g, BigInt::from(1)); // consecutive Fibonaccis are coprime
    }
}
