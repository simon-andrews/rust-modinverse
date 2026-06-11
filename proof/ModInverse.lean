/-
  # `src/lib.rs::modinverse`, specified           ★ HUMAN-MAINTAINED · TRUSTED ★

  This file is the human side of the project and the whole of its trusted surface. It
  defines *what a correct modular inverse is* (`Spec.Correct`) and nothing else — no
  algorithm, no proofs. To judge whether the crate is proven correct, read only this
  file and ask: is this the right notion?

  Everything else is the AI's workspace, generated and maintained by AI (Claude) and
  checked by the Lean kernel:

    * `ModInverse/`   — the model (an `ℕ` transcription of the Rust) and the
                        machine-checked proofs. Organized however the AI sees fit;
                        this file never depends on its shape, so it may be rewritten
                        freely (e.g. by an optimization loop).
    * `../extraction/` — `Machine.lean`, the Aeneas extraction of the real Rust
                        (`charon` + `aeneas`); machine-generated, never hand-edited.

  Correctness is two obligations the AI discharges against this frozen spec — the
  extracted code refines a model, and that model satisfies `Spec.Correct` — composed
  and checked end to end by the kernel. *How* that proof is structured is entirely up
  to the AI.

  The trusted computing base is exactly: this spec, the gate (`Gate.lean`, which
  re-types the final certificates at frozen statements and fails the build on any
  unapproved axiom), Lean's kernel and standard axioms, the Charon/Aeneas pipeline,
  and any postulates for `core`/`std` symbols Aeneas cannot lower (the AI collects
  these in `ModInverse/Extern.lean`). The unsigned path needs none of the last.

  ## The specification: what "correct" means

  Each target below is a field of a `structure` *parameterized by the model* — i.e. it
  states what it means for an arbitrary `ℕ → ℕ → Option ℕ` to be a correct modular
  inverse. Two consequences: a proof cannot weaken a target (the statement lives here,
  not where it is discharged), and adding a field mechanically forces a new proof
  obligation in the AI's workspace.
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq

namespace ModInverse.Spec

/-- What it means for `model` to be a correct modular-inverse function.

    `model a m` returns `some s` (a witness for the inverse of `a` mod `m`) when
    one exists, and `none` otherwise. The four fields pin down its behaviour on
    every input. -/
structure Correct (model : ℕ → ℕ → Option ℕ) : Prop where
  /-- Soundness: a returned witness really is an inverse, `a * s ≡ 1 (mod m)`. -/
  sound : ∀ a m s, model a m = some s → a * s ≡ 1 [MOD m]
  /-- Bound: the witness is the canonical representative in `[0, m)`. -/
  bounded : ∀ a m s, 0 < m → model a m = some s → s < m
  /-- Completeness: an inverse is produced whenever one exists (`gcd a m = 1`). -/
  complete : ∀ a m, 0 < m → Nat.Coprime a m → ∃ s, model a m = some s
  /-- Exact failure: `none` is returned in exactly the no-inverse cases. -/
  failsExactly : ∀ a m, model a m = none ↔ m = 0 ∨ ¬ Nat.Coprime a m

/-- What it means for the overflow-avoiding helpers to compute standard modular
    arithmetic. `addMod`/`mulMod` exist only to dodge `u128` overflow; these
    targets say they nonetheless equal `(a+b) % m` and `(a*b) % m`. -/
structure HelpersCompute (addMod mulMod : ℕ → ℕ → ℕ → ℕ) : Prop where
  /-- `addMod a b m = (a + b) % m`, given both inputs already reduced. -/
  addMod_eq : ∀ a b m, a < m → b < m → 0 < m → addMod a b m = (a + b) % m
  /-- `mulMod a b m = (a * b) % m` for any positive modulus. -/
  mulMod_eq : ∀ a b m, 0 < m → mulMod a b m = (a * b) % m

end ModInverse.Spec
