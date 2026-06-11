/-
  # Refinement: the Aeneas-extracted machine code refines the ℕ model

  AI-MAINTAINED. This module aggregates the per-layer refinement proofs. Each imported
  file proves that the actual extracted machine code (over `Std.UN`/`Std.IN` in the
  `Result` monad, with overflow/div-by-zero modelled as `fail`) **never errors** and
  **value-matches** the ℕ model `ModInverse.modinverse`, then composes that with
  `ModInverse.isCorrect` into the per-width end-to-end certificates
  `modinverse_*_correct`:

    * `Refinement/Helpers.lean`  — the `mul_mod` / `add_mod` building blocks
    * `Refinement/Unsigned.lean` — `u8 … u128` (+ `composeUnsigned` and the
      unsigned certificates)
    * `Refinement/Signed.lean`   — `i8 … i128` (+ `composeSigned` and the signed
      certificates)
    * `Refinement/Platform.lean` — `usize` / `isize` certificates
    * `Refinement/Egcd.lean`     — the `egcd_u64` certificate (gcd + exact Bézout)

  The certificates are re-typed at frozen statements — and their closures audited
  for unapproved axioms, build-failingly — by the trusted `Gate.lean` at the
  package root.

  Proof style follows Aeneas's skill files: weakest-precondition specs
  `f args ⦃ r => P r ⦄`, the `step`/`step*` tactics, `scalar_tac` (never `omega`).
-/

import ModInverse.Refinement.Helpers
import ModInverse.Refinement.Unsigned
import ModInverse.Refinement.Signed
import ModInverse.Refinement.Platform
import ModInverse.Refinement.Egcd
