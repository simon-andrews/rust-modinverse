# src/ — the Rust crate

`lib.rs` is the whole crate. Its module-level doc comment is the authoritative description of
the design; read it before changing anything here. This file records only the constraints that
aren't obvious from the code.

## The one-algorithm-per-width design

Every fixed-width type (`u8`–`u128`, `i8`–`i128`, `usize`/`isize`) runs the **same**
per-step-reduced extended Euclidean inverse over the unsigned representation, which never forms
a negative intermediate and so never overflows. The only per-width detail is `mul_mod`: narrow
widths widen to the next type; `u128` uses the Russian-peasant `mul_mod_u128` because nothing is
wider. Signed types canonicalize into `[0, |m|)` then delegate to the unsigned core.

This uniformity is deliberate — it lets a single Lean proof over `ℕ` certify the whole
fixed-width surface by per-width refinement.

## The hard constraint: keep the cores extractable

`modinverse_core!` expands to **monomorphic** functions free of generics, closures, and external
traits. This is not stylistic: it's what lets Charon/Aeneas lower them to Lean. The generic,
closure-taking `modinverse_via_egcd_with` exists for the `bigint` path precisely because Aeneas
*cannot* lower it. If you touch the fixed-width cores, preserve first-order monomorphic shape, then
re-run `just extract` and `just prove-correctness` — a change here can break the proof.

## What is and isn't verified

- **Verified:** the fixed-width path. The Lean development proves the `u128` model correct and
  proves every width's extracted code refines it.
- **Not verified:** the `bigint` feature paths (`modinverse_via_egcd_signed`,
  `modinverse_via_egcd_with`) and the free `egcd` function. These use the generic helpers and are
  covered only by tests.

## Footguns

- `egcd` and `modinverse_via_egcd_signed` overflow at/near `T::MIN` on fixed-width signed types
  (`T::MIN / -1`, `|T::MIN|`). The fixed-width `ModInverse` impls dodge this by working unsigned;
  the `bigint` paths are immune. Tests pin both the panic (debug) and the correct unsigned-path
  behaviour at `T::MIN`.

## Tests

Inline `#[cfg(test)] mod tests`. Coverage is exhaustive over small moduli plus near-`T::MAX` /
`T::MIN` regression cases. Several tests are gated on `feature = "bigint"` or `debug_assertions`
(the overflow panics only trap under overflow checks).
