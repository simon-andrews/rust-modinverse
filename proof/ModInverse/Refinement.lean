/-
  # Refinement: the Aeneas-extracted machine code refines the ℕ model

  AI-MAINTAINED. This module aggregates the per-layer refinement proofs and runs the
  axiom audit. Each imported file proves that the actual extracted machine code (over
  `Std.UN`/`Std.IN` in the `Result` monad, with overflow/div-by-zero modelled as
  `fail`) **never errors** and **value-matches** the ℕ model `ModInverse.modinverse`:

    * `Refinement/Helpers.lean`  — the `mul_mod` / `add_mod` building blocks
    * `Refinement/Unsigned.lean` — `modinverse_u8 … u128` (+ `modinverse_u128_correct`)
    * `Refinement/Signed.lean`   — `modinverse_i8 … i128` (+ `modinverse_i128_correct`)
    * `Refinement/Platform.lean` — `usize` / `isize`

  Composed with `ModInverse.isCorrect`, this gives end-to-end correctness of the real
  extracted code. Proof style follows Aeneas's skill files: weakest-precondition specs
  `f args ⦃ r => P r ⦄`, the `step`/`step*` tactics, `scalar_tac` (never `omega`).
-/

import ModInverse.Refinement.Helpers
import ModInverse.Refinement.Unsigned
import ModInverse.Refinement.Signed
import ModInverse.Refinement.Platform

/-! ## Axiom audit

  The signed / `usize` / `isize` results add exactly the trusted `ModInverse.Extern`
  specs (`unsigned_abs`, `Option.map`) on top of Lean's standard axioms — and crucially
  **no `sorryAx`**. The unsigned `modinverse_u128_correct` stays clean of even the
  `Extern` axioms (it depends only on `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms Refinement.modinverse_u128_correct
#print axioms Refinement.modinverse_i128_correct
#print axioms Refinement.modinverse_usize_spec
