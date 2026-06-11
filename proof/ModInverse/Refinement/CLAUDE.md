# proof/ModInverse/Refinement/ — machine-code refinement proofs

These prove the Aeneas-extracted machine code (over `Std.UN`/`Std.IN` in the `Result` monad)
**never errors** and **value-matches** the `ℕ` model `ModInverse.modinverse`. Imported and
audited by `../Refinement.lean`; see [`../CLAUDE.md`](../CLAUDE.md) for where this sits.

## Files

- `Helpers.lean` — the `mul_mod` / `add_mod` primitives. Tagged `@[step]` so the loop proofs pick
  them up automatically.
- `Unsigned.lean` — `modinverse_u8 … u128`, ending in the generic composition lemma
  `composeUnsigned` and the certificates `modinverse_uN_correct`.
- `Signed.lean` — `modinverse_i8 … i128` on the canonicalized input, ending in `composeSigned`
  and `modinverse_iN_correct`. Uses the `Extern` axioms (`unsigned_abs`, `Option.map`).
- `Platform.lean` — `usize` / `isize`, dispatching to the 64-bit width, ending in their
  certificates.

The 14 `modinverse_*_correct` certificates are the binding interface: the trusted `Gate.lean`
re-types them at frozen statements, so their names and types must keep existing verbatim.

## Conventions (Aeneas, not generic Mathlib)

This is the one area that follows Aeneas's proof discipline rather than ordinary Mathlib tactics:

- Specs are weakest-precondition style: `f args ⦃ r => P r ⦄`.
- Drive proofs with the `step` / `step*` tactics; close arithmetic with **`scalar_tac`, never
  `omega`**.
- Each width is a copy of the same script with the type swapped. **`u8` and `i8` are the
  templates** — they carry the real explanation; `u16`–`u128` / `i16`–`i128` are mechanical
  swaps. Read the template, skim the rest, and when editing one width apply the same change across
  all of them.
