//! Small library for finding the modular multiplicative inverses. Also has an implementation of
//! the extended Euclidean algorithm built in.
//!
//! The [`ModInverse`] trait is implemented for every built-in integer type: `i8`–`i128`,
//! `u8`–`u128`, `isize`, `usize`. Every fixed-width type runs the *same* algorithm: a
//! per-step-reduced extended Euclidean inverse over the type's unsigned representation, which
//! never forms a negative intermediate and so never overflows. Each width supplies a `mul_mod`
//! computing `(a * b) % m` without overflow — widths up to `u64` form the product in the
//! next-wider type, while `u128` uses a Russian-peasant routine because it has no wider type to
//! widen into. Signed types canonicalize their input into `[0, |m|)`, delegate to the unsigned
//! core (handling `T::MIN` losslessly), then cast the in-range result back. `isize`/`usize`
//! dispatch to the matching fixed-width impl at compile time.
//!
//! With the `bigint` feature enabled, [`ModInverse`] is also implemented for
//! [`num_bigint::BigInt`] and [`num_bigint::BigUint`] — the de facto arbitrary-precision integer
//! types in the Rust ecosystem. It's gated behind a feature so users who don't need it don't
//! pay the `num-bigint` compile cost.
//!
//! Running one algorithm across every width is deliberate: it lets a single Lean 4 proof (stated
//! over `ℕ`) certify the whole fixed-width surface by per-width refinement, rather than a separate
//! proof per algorithm. The `bigint` paths run the generic helpers below and are not part of the
//! Lean development.

#![no_std]

use num_integer::Integer;
use num_traits::Signed;

/// Finds the greatest common denominator of two integers *a* and *b*, and two
/// integers *x* and *y* such that *ax* + *by* is the greatest common
/// denominator of *a* and *b* (Bézout coefficients).
///
/// This function is a transcription of Wikipedia's iterative pseudocode for the [extended Euclidean
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
///
/// # Overflow on fixed-width signed types
///
/// For fixed-width signed types, `egcd` is *not* safe to call with inputs at or very close
/// to `T::MIN`. Intermediate values like `T::MIN / -1` or `T::MIN - x` can overflow and
/// trap under overflow checks. The `i8`–`i64` trait impls avoid this by widening one step before
/// calling `egcd`.
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

/// Modular multiplicative inverse via the textbook [extended Euclidean
/// algorithm](https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm), for signed types
/// where the modulus may be negative. Returns the inverse of *a* mod *m* in the canonical range
/// `[0, |m|)` when it exists, or `None` otherwise (when `gcd(a, m) ≠ 1`, or when `m == 0`).
///
/// This is the path the `BigInt` impl uses directly. It's faster than the unsigned
/// per-step-reduced variant on arbitrary-precision types because each loop iteration does one
/// full-width multiplication instead of `O(log b)` modular additions, but it carries a `T::MIN`
/// panic footgun on fixed-width types — see below. The fixed-width impls therefore do *not* use
/// it; they run the monomorphic unsigned core instead.
///
/// # Panics
///
/// Panics if `m == T::MIN` for a fixed-width signed type, because `|T::MIN|` is not
/// representable in `T` and the internal `m.abs()` overflows. Widen one step before calling.
/// `a == T::MIN` is fine — the algorithm reduces `a` mod `|m|` without ever forming `|a|`.
/// Arbitrary-precision types (e.g. `BigInt`) are unaffected, which is why this is kept only for
/// the `bigint` feature.
#[cfg(feature = "bigint")]
pub(crate) fn modinverse_via_egcd_signed<T: Clone + Integer + Signed>(a: T, m: T) -> Option<T> {
    if m.is_zero() {
        return None;
    }
    let m_abs = m.abs();
    let a_reduced = a.mod_floor(&m_abs);
    let (g, x, _) = egcd(a_reduced, m_abs.clone());
    if g.is_one() {
        Some(x.mod_floor(&m_abs))
    } else {
        None
    }
}

/// Computes the inverse of *a* mod *m* using a per-step-reduced extended Euclidean algorithm
/// that never produces a negative intermediate, so `T` doesn't need to be `Signed`. **Never
/// overflows** provided the supplied `mul_mod` doesn't. `m` must be positive (or zero / one,
/// which short-circuit).
///
/// The caller supplies the modular multiplication function `mul_mod(a, b, m) → (a * b) mod m`.
/// The sole in-crate caller is the `BigUint` impl, which plugs in plain `(q * s).mod_floor(m)`
/// because arbitrary-precision multiplication can't overflow. (The fixed-width `u8`–`u128` impls
/// run monomorphic copies of this same algorithm — see `modinverse_core!` — rather than going
/// through this generic, closure-taking version, which Charon/Aeneas cannot lower.)
///
/// The supplied closure is trusted to satisfy `mul_mod(a, b, m) == (a * b) mod m` and to return
/// a value in `[0, m)`. Violating either may cause infinite loops or wrong answers; debug
/// builds will trigger `debug_assert!` on the upper-bound violation.
#[cfg(feature = "bigint")]
pub(crate) fn modinverse_via_egcd_with<T, F>(a: T, m: T, mul_mod: F) -> Option<T>
where
    T: Clone + Integer,
    F: Fn(T, T, &T) -> T,
{
    // Reject m <= 0 (no inverse for m == 0; algorithm assumes positive m). The `m < T::zero()`
    // branch is dead for unsigned `T` and triggered for negative signed moduli — that case
    // routes through `modinverse_via_egcd_signed` instead, which canonicalizes the modulus.
    if m <= T::zero() {
        return None;
    }
    if m.is_one() {
        return Some(T::zero());
    }
    let (mut r, mut r_next) = (m.clone(), a.mod_floor(&m));
    let (mut s, mut s_next) = (T::zero(), T::one());
    while !r_next.is_zero() {
        debug_assert!(s < m && s_next < m);
        let (q, rem) = r.div_rem(&r_next);
        let qs = mul_mod(q, s_next.clone(), &m);
        debug_assert!(qs < m);
        (r, r_next) = (r_next, rem);
        (s, s_next) = (s_next, sub_mod_unsigned(s, qs, &m));
    }
    if r.is_one() {
        Some(s)
    } else {
        None
    }
}

// The `(m - b) + a` arm in the else branch stays below `m`, so it can't overflow on fixed-width
// types where `m + a` would. Used only by the generic `bigint` path; the monomorphic cores inline
// the same `if a >= b { a - b } else { (m - b) + a }` shape directly.
#[cfg(feature = "bigint")]
fn sub_mod_unsigned<T: Clone + Integer>(a: T, b: T, m: &T) -> T {
    if a >= b {
        a - b
    } else {
        (m.clone() - b) + a
    }
}

/// Trait for types that support [modular multiplicative
/// inverse](https://en.wikipedia.org/wiki/Modular_multiplicative_inverse) computation.
///
/// `self.modinverse(m)` returns the inverse *x* of `self` modulo *m* such that
/// `self * x ≡ 1 (mod m)`, in the canonical range `[0, |m|)`. Returns `None` if no inverse exists
/// (i.e. `gcd(self, m) ≠ 1`) or if `m == 0`. By convention `modinverse(_, 1) == Some(0)` because
/// every element is congruent to 0 mod 1.
///
/// The trait takes `self` (and `modulus`) by value. For `Copy` types — every primitive integer —
/// this is free. For owning types like [`num_bigint::BigInt`], callers may need an explicit
/// `.clone()` if they want to keep the original. This mirrors [`num_traits::Inv`] and similar
/// arithmetic traits.
pub trait ModInverse: Sized {
    fn modinverse(self, modulus: Self) -> Option<Self>;
}

/// Free-function form of [`ModInverse::modinverse`].
///
/// ```
/// use modinverse::modinverse;
///
/// assert_eq!(modinverse(3, 26), Some(9));
/// assert_eq!(modinverse(4, 32), None);
/// ```
pub fn modinverse<T: ModInverse>(a: T, m: T) -> Option<T> {
    a.modinverse(m)
}

// ---------------------------------------------------------------------------
// Fixed-width integers: one algorithm for every width.
//
// Every fixed-width type runs the same per-step-reduced extended Euclidean inverse over its
// *unsigned* representation. The only per-width detail is `mul_mod(a, b, m) = (a * b) % m`:
// widths up to `u64` form the full product in the next-wider type; `u128` has no wider type and
// uses the Russian-peasant routine `mul_mod_u128`. Each core is monomorphic and free of generics,
// closures, and external traits, so it lowers cleanly through Charon/Aeneas for verification.
// ---------------------------------------------------------------------------

// `(a * b) % m` for narrow widths: widen to the next type so the product can't overflow.
fn mul_mod_u8(a: u8, b: u8, m: u8) -> u8 {
    ((a as u16 * b as u16) % m as u16) as u8
}
fn mul_mod_u16(a: u16, b: u16, m: u16) -> u16 {
    ((a as u32 * b as u32) % m as u32) as u16
}
fn mul_mod_u32(a: u32, b: u32, m: u32) -> u32 {
    ((a as u64 * b as u64) % m as u64) as u32
}
fn mul_mod_u64(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

// The per-step-reduced extended Euclidean inverse, monomorphized per unsigned width. `mul_mod` is
// a free function (not a closure) so the expansion stays first-order. Mirrors the generic
// `modinverse_via_egcd_with`; the certified algorithm in proof/ModInverse.lean is this one.
macro_rules! modinverse_core {
    ($name:ident, $t:ty, $mul_mod:ident) => {
        fn $name(a: $t, m: $t) -> Option<$t> {
            if m == 0 {
                return None;
            }
            if m == 1 {
                return Some(0);
            }
            let (mut r, mut r_next) = (m, a % m);
            let (mut s, mut s_next): ($t, $t) = (0, 1);
            while r_next != 0 {
                let q = r / r_next;
                let rem = r % r_next;
                let qs = $mul_mod(q, s_next, m);
                (r, r_next) = (r_next, rem);
                let s_new = if s >= qs { s - qs } else { (m - qs) + s };
                (s, s_next) = (s_next, s_new);
            }
            if r == 1 {
                Some(s)
            } else {
                None
            }
        }
    };
}

modinverse_core!(modinverse_u8, u8, mul_mod_u8);
modinverse_core!(modinverse_u16, u16, mul_mod_u16);
modinverse_core!(modinverse_u32, u32, mul_mod_u32);
modinverse_core!(modinverse_u64, u64, mul_mod_u64);
modinverse_core!(modinverse_u128, u128, mul_mod_u128);

// Unsigned impls call their core directly.
macro_rules! impl_modinverse_unsigned {
    ($t:ty, $core:ident) => {
        impl ModInverse for $t {
            fn modinverse(self, m: Self) -> Option<Self> {
                $core(self, m)
            }
        }
    };
}

impl_modinverse_unsigned!(u8, modinverse_u8);
impl_modinverse_unsigned!(u16, modinverse_u16);
impl_modinverse_unsigned!(u32, modinverse_u32);
impl_modinverse_unsigned!(u64, modinverse_u64);
impl_modinverse_unsigned!(u128, modinverse_u128);

// Signed impls canonicalize `self` into `[0, |m|)` over the unsigned type, run the unsigned core,
// and cast the in-range result back. This is panic-free even at `T::MIN`: `unsigned_abs()` never
// overflows, and any returned inverse lies in `[0, |m|)` and is coprime to `|m|`. When
// `m == T::MIN`, `|m| = 2^(N-1)` does not fit in `T`, but it is excluded by the strict upper
// bound and could never be coprime anyway, so the cast back is lossless even then.
macro_rules! impl_modinverse_signed {
    ($t:ty, $ut:ty, $core:ident) => {
        impl ModInverse for $t {
            fn modinverse(self, m: Self) -> Option<Self> {
                if m == 0 {
                    return None;
                }
                let m_abs: $ut = m.unsigned_abs();
                let a_abs = self.unsigned_abs() % m_abs;
                let a_u = if self < 0 && a_abs != 0 { m_abs - a_abs } else { a_abs };
                $core(a_u, m_abs).map(|x| x as $t)
            }
        }
    };
}

impl_modinverse_signed!(i8, u8, modinverse_u8);
impl_modinverse_signed!(i16, u16, modinverse_u16);
impl_modinverse_signed!(i32, u32, modinverse_u32);
impl_modinverse_signed!(i64, u64, modinverse_u64);
impl_modinverse_signed!(i128, u128, modinverse_u128);

// Russian-peasant modular multiplication: computes (a * b) mod m without overflow, even when
// `a` and `b` are full u128 values. `u128` has no wider type to widen the product into.
fn mul_mod_u128(mut a: u128, mut b: u128, m: u128) -> u128 {
    a %= m;
    let mut result = 0u128;
    while b > 0 {
        if b & 1 == 1 {
            result = add_mod_u128(result, a, m);
        }
        a = add_mod_u128(a, a, m);
        b >>= 1;
    }
    result
}

// Computes (a + b) mod m without overflow, assuming a, b < m.
fn add_mod_u128(a: u128, b: u128, m: u128) -> u128 {
    let room = m - a;
    if b < room {
        a + b
    } else {
        b - room
    }
}

// ---------------------------------------------------------------------------
// usize / isize: dispatch by pointer width.
// ---------------------------------------------------------------------------

#[cfg(not(any(
    target_pointer_width = "16",
    target_pointer_width = "32",
    target_pointer_width = "64"
)))]
compile_error!(
    "modinverse: unsupported `target_pointer_width`. Only 16, 32, and 64-bit pointer targets \
     have `ModInverse` impls for `usize`/`isize`."
);

#[cfg(target_pointer_width = "16")]
impl ModInverse for usize {
    fn modinverse(self, m: Self) -> Option<Self> {
        (self as u16).modinverse(m as u16).map(|x| x as usize)
    }
}
#[cfg(target_pointer_width = "32")]
impl ModInverse for usize {
    fn modinverse(self, m: Self) -> Option<Self> {
        (self as u32).modinverse(m as u32).map(|x| x as usize)
    }
}
#[cfg(target_pointer_width = "64")]
impl ModInverse for usize {
    fn modinverse(self, m: Self) -> Option<Self> {
        (self as u64).modinverse(m as u64).map(|x| x as usize)
    }
}

#[cfg(target_pointer_width = "16")]
impl ModInverse for isize {
    fn modinverse(self, m: Self) -> Option<Self> {
        (self as i16).modinverse(m as i16).map(|x| x as isize)
    }
}
#[cfg(target_pointer_width = "32")]
impl ModInverse for isize {
    fn modinverse(self, m: Self) -> Option<Self> {
        (self as i32).modinverse(m as i32).map(|x| x as isize)
    }
}
#[cfg(target_pointer_width = "64")]
impl ModInverse for isize {
    fn modinverse(self, m: Self) -> Option<Self> {
        (self as i64).modinverse(m as i64).map(|x| x as isize)
    }
}

// ---------------------------------------------------------------------------
// Optional: num_bigint::BigInt / BigUint
// ---------------------------------------------------------------------------

#[cfg(feature = "bigint")]
impl ModInverse for num_bigint::BigInt {
    fn modinverse(self, m: Self) -> Option<Self> {
        modinverse_via_egcd_signed(self, m)
    }
}

// `BigUint` is arbitrary-precision, so plain `(q * s).mod_floor(m)` never overflows. Skip the
// generic doubling-mul that the public default uses for safety on fixed-width types.
#[cfg(feature = "bigint")]
impl ModInverse for num_bigint::BigUint {
    fn modinverse(self, m: Self) -> Option<Self> {
        modinverse_via_egcd_with(self, m, |q, s, m| (q * s).mod_floor(m))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(feature = "bigint")]
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

    #[cfg(feature = "bigint")]
    #[test]
    fn modinverse_biguint() {
        use num_bigint::BigUint;
        assert_eq!(BigUint::from(3u32).modinverse(BigUint::from(26u32)), Some(BigUint::from(9u32)));
        assert_eq!(BigUint::from(4u32).modinverse(BigUint::from(32u32)), None);
    }

    #[cfg(feature = "bigint")]
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

    // `i64::MIN.abs()` overflows; release builds wrap silently and would give a wrong answer
    // rather than panic, so gate the panic assertion on the overflow-checks build.
    #[cfg(all(debug_assertions, feature = "bigint"))]
    #[test]
    #[should_panic]
    fn modinverse_via_egcd_signed_panics_on_t_min() {
        // The documented panic from the `# Panics` block on `modinverse_via_egcd_signed` (kept
        // for the `bigint` path; fixed-width types no longer route through this helper).
        let _ = modinverse_via_egcd_signed(3i64, i64::MIN);
    }

    #[test]
    fn modinverse_handles_t_min() {
        // The signed impls canonicalize to unsigned, so they stay panic-free even at the type's
        // MIN, where `T::MIN.abs()` would overflow. i8::MIN = -128.
        let inv = modinverse(3i8, i8::MIN).unwrap();
        assert_eq!((3i16 * inv as i16).rem_euclid(128), 1);
        // Same at i64::MIN.
        let inv = modinverse(3i64, i64::MIN).unwrap();
        let m_abs = (i64::MIN as i128).unsigned_abs();
        assert_eq!((3u128 * inv as u128) % m_abs, 1);
    }

    #[cfg(feature = "bigint")]
    #[test]
    fn modinverse_bigint() {
        // BigInt impl handles signed inputs and negative moduli.
        assert_eq!(modinverse(BigInt::from(3), BigInt::from(26)), Some(BigInt::from(9)));
        assert_eq!(modinverse(BigInt::from(3), BigInt::from(-26)), Some(BigInt::from(9)));
        assert_eq!(modinverse(BigInt::from(4), BigInt::from(32)), None);
    }

    #[test]
    fn modinverse_unsigned() {
        assert_eq!(modinverse(3u32, 26u32), Some(9));
        assert_eq!(modinverse(4u32, 32u32), None);
        assert_eq!(modinverse(10u64, 13u64), Some(4));
    }

    #[test]
    fn modinverse_unsigned_no_overflow() {
        // Regression for #2: previously panicked with subtract-with-overflow.
        let inv = modinverse(4u64, 2058270774454069813u64).unwrap();
        assert_eq!((inv as u128 * 4) % 2058270774454069813u128, 1);
    }

    #[test]
    fn modinverse_u128_large() {
        let m: u128 = (1u128 << 127) - 1; // Mersenne, prime
        let a: u128 = 12345678901234567890;
        let inv = modinverse(a, m).unwrap();
        assert_eq!(mul_mod_u128(a, inv, m), 1);
    }

    #[test]
    fn modinverse_i128_large_and_negative() {
        let m: i128 = (1i128 << 100) - 39;
        let a: i128 = -98765432109876543210i128;
        let inv = modinverse(a, m).unwrap();
        assert!(inv >= 0 && inv < m);
        let a_mod = ((a % m) + m) % m;
        assert_eq!(mul_mod_u128(a_mod as u128, inv as u128, m as u128), 1);
    }

    #[test]
    fn modinverse_signed_unsigned_agree() {
        for m in -64i64..=64 {
            for a in -64i64..=64 {
                let signed = modinverse(a, m);
                // m == 0 must return None on both signed and unsigned paths.
                if m == 0 {
                    assert_eq!(signed, None);
                    if a >= 0 {
                        assert_eq!(modinverse(a as u64, 0u64), None);
                    }
                    continue;
                }
                // For negative m, the canonical inverse range is [0, |m|), same as for |m|.
                let m_abs = m.unsigned_abs();
                if a >= 0 {
                    let unsigned = modinverse(a as u64, m_abs).map(|x| x as i64);
                    assert_eq!(signed, unsigned, "disagree at a={a}, m={m}");
                }
            }
        }
    }

    #[test]
    fn modinverse_exhaustive_small() {
        for m in 1u32..=64 {
            for a in 0u32..m {
                let inv = modinverse(a, m);
                match inv {
                    Some(x) => {
                        assert!(x < m);
                        // For m == 1, the canonical residue of 1 is 0; every element is its own
                        // inverse in the trivial ring.
                        let expected = if m == 1 { 0 } else { 1 };
                        assert_eq!((a as u64 * x as u64) % m as u64, expected);
                    }
                    None => {
                        assert!(num_integer::gcd(a, m) != 1);
                    }
                }
            }
        }
    }

    #[test]
    fn modinverse_u128_near_max() {
        // m = 2^128 - 159, the largest 128-bit prime. Exercises mul_mod_u128/add_mod_u128 with
        // values filling nearly all 128 bits.
        let m: u128 = u128::MAX - 158;
        let a: u128 = u128::MAX / 3;
        let inv = modinverse(a, m).unwrap();
        assert_eq!(mul_mod_u128(a % m, inv, m), 1);
    }

    #[test]
    fn modinverse_u128_no_inverse() {
        // gcd(6, 9) = 3, so no inverse exists.
        assert_eq!(modinverse(6u128, 9u128), None);
        // Large case where gcd > 1.
        assert_eq!(modinverse(1u128 << 100, 1u128 << 120), None);
    }

    #[test]
    fn modinverse_u128_a_zero() {
        // gcd(0, m) = m ≠ 1 for m > 1, so no inverse.
        assert_eq!(modinverse(0u128, 7u128), None);
        assert_eq!(modinverse(0u128, u128::MAX), None);
    }

    #[test]
    fn modinverse_m_one_is_zero() {
        assert_eq!(modinverse(5i32, 1), Some(0));
        assert_eq!(modinverse(5u32, 1), Some(0));
        assert_eq!(modinverse(5u128, 1), Some(0));
    }

    #[test]
    fn modinverse_m_zero_is_none() {
        assert_eq!(modinverse(5i32, 0), None);
        assert_eq!(modinverse(5u128, 0), None);
        assert_eq!(modinverse(5i128, 0), None);
    }

    // Same caveat as `modinverse_via_egcd_signed_panics_on_t_min`: in release builds the
    // `i32::MIN / -1` overflow wraps silently rather than panicking.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn egcd_panics_at_t_min() {
        // The documented `T::MIN` overflow footgun on `egcd` for fixed-width signed types:
        // `i32::MIN / -1` overflows, trapping under overflow checks.
        let _ = egcd(i32::MIN, -1i32);
    }

    #[test]
    fn modinverse_signed_exhaustive_i32_small() {
        // Mirror of `modinverse_exhaustive_small` for signed `i32`, covering negative `m`
        // (including `i32::MIN`-shaped boundaries scaled to fit the loop). Uses the public trait
        // for both signed and unsigned to ensure the i32 path agrees with ground truth.
        for m in -32i32..=32 {
            for a in -32i32..=32 {
                let inv = modinverse(a, m);
                if m == 0 {
                    assert_eq!(inv, None);
                    continue;
                }
                let m_abs = m.unsigned_abs();
                match inv {
                    Some(x) => {
                        assert!((0..m_abs as i32).contains(&x), "inv {x} out of [0, {m_abs})");
                        let a_canon = a.rem_euclid(m_abs as i32) as u64;
                        let expected = if m_abs == 1 { 0 } else { 1 };
                        assert_eq!((a_canon * x as u64) % m_abs as u64, expected,
                                   "wrong inv at a={a}, m={m}");
                    }
                    None => {
                        let a_canon = a.rem_euclid(m_abs as i32);
                        assert!(num_integer::gcd(a_canon, m_abs as i32) != 1,
                                "missing inverse at a={a}, m={m}");
                    }
                }
            }
        }
    }

    #[test]
    fn modinverse_i128_m_min() {
        // `i128::MIN` modulus is the trickiest signed case: |i128::MIN| = 2^127 doesn't fit
        // back in i128. The impl uses `unsigned_abs` and returns the result in `[0, 2^127)`,
        // which does fit. Verify a coprime input gives a valid inverse.
        let a: i128 = 3;
        let inv = modinverse(a, i128::MIN).unwrap();
        assert!(inv >= 0);
        // Check (a * inv) ≡ 1 (mod 2^127) by computing in u128.
        let m_abs: u128 = 1u128 << 127;
        let prod = mul_mod_u128(a as u128, inv as u128, m_abs);
        assert_eq!(prod, 1);
    }

    #[test]
    fn modinverse_i128_m_min_no_inverse() {
        // Any even `a` shares a factor with `|i128::MIN| = 2^127`, so no inverse.
        assert_eq!(modinverse(4i128, i128::MIN), None);
    }
}
