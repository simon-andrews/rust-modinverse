/-
  # Targets: what "correct" means      ★ HUMAN-MAINTAINED ★

  This is the trusted specification. To review whether the crate is proven
  correct, a human reads *only this file*: do these statements actually capture
  what a modular-inverse routine must do? Everything in `ModInverse/Proofs.lean`
  is machinery to discharge exactly these targets and nothing weaker.

  Each correctness target is a field of a `structure` that is *parameterized by
  the model* — i.e. it states what it means for an arbitrary `ℕ → ℕ → Option ℕ`
  to be a correct modular inverse. Two consequences:

    * The proof file cannot weaken a target: the statement lives here, and the
      proof must produce a term of exactly this type.
    * Adding a field here mechanically forces a new proof obligation there: the
      instance `Spec.Correct modinverse` will not typecheck until every field is
      provided. Nothing can be silently dropped.

  When the model is swapped (e.g. for an Aeneas-extracted `modinverse`), this
  file does not change — the new model just has to satisfy `Spec.Correct`.
-/

import ModInverse.Model
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
