/-
  # The gate: what the proof must always deliver    ★ HUMAN-MAINTAINED · TRUSTED ★

  This file is the enforcement half of the trusted surface (the meaning half is the
  spec in `ModInverse.lean`). It pins down — in trusted vocabulary only: the
  Aeneas-extracted machine code in `../extraction/Machine.lean`, Aeneas's scalar and
  `Result` types, and plain arithmetic — what the AI workspace must always deliver,
  and it **fails the build** if any of it is missing:

    * For each of the 14 public `ModInverse` impls (`u8`–`u128`, `i8`–`i128`,
      `usize`, `isize`), the extracted trait method is a correct modular inverse:
      it never errors, a returned witness really is an inverse and is the canonical
      representative, a witness is returned whenever one exists, and `None` comes
      back in exactly the no-inverse cases. And the extracted `egcd_u64` is a
      correct extended gcd: gcd plus an exact Bézout certificate with the canonical
      first coefficient. The statements (`UnsignedCorrect` / `SignedCorrect` /
      `EgcdU64Correct` below) belong to this file; the workspace must produce terms
      of exactly these types — they cannot be weakened from the outside.

    * Each certificate's axiom closure is inside an explicit allowlist — exactly
      Lean's three standard axioms, for every width: the extraction has no opaque
      symbols, so nothing about the machine code is postulated
      (`ModInverse/Extern.lean` is empty). In particular **no `sorryAx` and no
      rogue `axiom` can hide anywhere in a certificate's proof**: unlike the
      informational `#print axioms`, `#assert_axioms` fails the build.

  The only AI-workspace names this file mentions are the 15 final certificates
  (`Refinement.modinverse_*_correct`, `Refinement.egcd_u64_correct`). Everything
  else — file layout, the model, lemma structure, proof style — remains entirely
  the AI's to rearrange. Renaming a certificate is an interface change and
  requires a human edit here; that is the point.

  Like the spec, this file is frozen: `just trusted-unchanged` checks its hash.
-/

import Lean
import ModInverse
import ModInverse.Refinement

/-! ## The audit command -/

open Lean Elab Command in
/-- `#assert_axioms thm [ax₁, ax₂, …]` **fails the build** unless every axiom in
    `thm`'s closure is one of the listed allowed axioms. -/
elab "#assert_axioms " id:ident " [" allowed:ident,* "]" : command => do
  let declName ← resolveGlobalConstNoOverload id
  let allowedNames ← allowed.getElems.toList.mapM fun a =>
    resolveGlobalConstNoOverload a
  let axioms ← liftCoreM <| collectAxioms declName
  let bad := axioms.filter fun ax => !allowedNames.contains ax
  unless bad.isEmpty do
    throwError "axiom audit failed for '{declName}': disallowed axioms {bad.toList}"

namespace Gate

open Aeneas Aeneas.Std Result
open modinverse

/-! ## The trusted statements

  These mirror the four fields of `ModInverse.Spec.Correct` at the machine level.
  `UnsignedCorrect` reads over `ℕ` (`.val` of an unsigned scalar); `SignedCorrect`
  reads over `ℤ`, with the witness in the canonical range `[0, |m|)`. -/

/-- An extracted unsigned `modinverse` at width `w` is correct: it never errors
    (`⦃ ⦄` asserts every run is `ok`), a returned witness really is an inverse,
    the witness is the canonical representative in `[0, m)`, a witness is produced
    whenever one exists, and `none` is returned in exactly the no-inverse cases. -/
def UnsignedCorrect (w : UScalarTy)
    (f : UScalar w → UScalar w → Result (Option (UScalar w))) : Prop :=
  ∀ a m : UScalar w,
    f a m ⦃ (r : Option (UScalar w)) =>
      (∀ s, r = some s → a.val * s.val ≡ 1 [MOD m.val]) ∧
      (∀ s, r = some s → 0 < m.val → s.val < m.val) ∧
      (0 < m.val → Nat.Coprime a.val m.val → ∃ s, r = some s) ∧
      (r = none ↔ m.val = 0 ∨ ¬ Nat.Coprime a.val m.val) ⦄

/-- An extracted signed `modinverse` at width `w` is correct, over `ℤ`: it never
    errors, a returned witness really is an inverse, the witness is the canonical
    representative in `[0, |m|)`, a witness is produced whenever one exists, and
    `none` is returned in exactly the no-inverse cases. -/
def SignedCorrect (w : IScalarTy)
    (f : IScalar w → IScalar w → Result (Option (IScalar w))) : Prop :=
  ∀ a m : IScalar w,
    f a m ⦃ (r : Option (IScalar w)) =>
      (∀ s, r = some s → a.val * s.val ≡ 1 [ZMOD m.val]) ∧
      (∀ s, r = some s → 0 ≤ s.val ∧ s.val < m.val.natAbs) ∧
      (m.val ≠ 0 → Int.gcd a.val m.val = 1 → ∃ s, r = some s) ∧
      (r = none ↔ m.val = 0 ∨ Int.gcd a.val m.val ≠ 1) ⦄

/-! ## The 15 certificates, anchored

  Each `theorem` below re-types an AI-workspace certificate at this file's trusted
  statement (the two must be definitionally identical or the build fails), then
  `#assert_axioms` pins its axiom closure. -/

/-! ### Unsigned -/

theorem u8_correct : UnsignedCorrect .U8 U8.Insts.ModinverseModInverse.modinverse :=
  Refinement.modinverse_u8_correct
#assert_axioms u8_correct [propext, Classical.choice, Quot.sound]

theorem u16_correct : UnsignedCorrect .U16 U16.Insts.ModinverseModInverse.modinverse :=
  Refinement.modinverse_u16_correct
#assert_axioms u16_correct [propext, Classical.choice, Quot.sound]

theorem u32_correct : UnsignedCorrect .U32 U32.Insts.ModinverseModInverse.modinverse :=
  Refinement.modinverse_u32_correct
#assert_axioms u32_correct [propext, Classical.choice, Quot.sound]

theorem u64_correct : UnsignedCorrect .U64 U64.Insts.ModinverseModInverse.modinverse :=
  Refinement.modinverse_u64_correct
#assert_axioms u64_correct [propext, Classical.choice, Quot.sound]

theorem u128_correct : UnsignedCorrect .U128 U128.Insts.ModinverseModInverse.modinverse :=
  Refinement.modinverse_u128_correct
#assert_axioms u128_correct [propext, Classical.choice, Quot.sound]

/-! ### Signed -/

theorem i8_correct : SignedCorrect .I8 I8.Insts.ModinverseModInverse.modinverse :=
  Refinement.modinverse_i8_correct
#assert_axioms i8_correct [propext, Classical.choice, Quot.sound]

theorem i16_correct : SignedCorrect .I16 I16.Insts.ModinverseModInverse.modinverse :=
  Refinement.modinverse_i16_correct
#assert_axioms i16_correct [propext, Classical.choice, Quot.sound]

theorem i32_correct : SignedCorrect .I32 I32.Insts.ModinverseModInverse.modinverse :=
  Refinement.modinverse_i32_correct
#assert_axioms i32_correct [propext, Classical.choice, Quot.sound]

theorem i64_correct : SignedCorrect .I64 I64.Insts.ModinverseModInverse.modinverse :=
  Refinement.modinverse_i64_correct
#assert_axioms i64_correct [propext, Classical.choice, Quot.sound]

theorem i128_correct : SignedCorrect .I128 I128.Insts.ModinverseModInverse.modinverse :=
  Refinement.modinverse_i128_correct
#assert_axioms i128_correct [propext, Classical.choice, Quot.sound]

/-! ### Platform widths: dispatch to the 64-bit width -/

theorem usize_correct : UnsignedCorrect .Usize Usize.Insts.ModinverseModInverse.modinverse :=
  Refinement.modinverse_usize_correct
#assert_axioms usize_correct [propext, Classical.choice, Quot.sound]

theorem isize_correct : SignedCorrect .Isize Isize.Insts.ModinverseModInverse.modinverse :=
  Refinement.modinverse_isize_correct
#assert_axioms isize_correct [propext, Classical.choice, Quot.sound]

/-! ### Extended gcd -/

/-- The extracted `egcd_u64` is a correct extended gcd: it never errors, its first
    component is `gcd a b`, the two `i128` coefficients certify it exactly over
    `ℤ`, and the first coefficient is the canonical one in `[0, b)`. -/
def EgcdU64Correct (f : U64 → U64 → Result (U64 × I128 × I128)) : Prop :=
  ∀ a b : U64,
    f a b ⦃ (res : U64 × I128 × I128) =>
      res.1.val = Nat.gcd a.val b.val ∧
      (a.val : ℤ) * res.2.1.val + (b.val : ℤ) * res.2.2.val = (res.1.val : ℤ) ∧
      (0 < b.val → 0 ≤ res.2.1.val ∧ res.2.1.val < (b.val : ℤ)) ⦄

theorem egcd_u64_correct : EgcdU64Correct egcd_u64 :=
  Refinement.egcd_u64_correct
#assert_axioms egcd_u64_correct [propext, Classical.choice, Quot.sound]

end Gate
