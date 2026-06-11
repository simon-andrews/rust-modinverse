/-
  # Unsigned refinement: `modinverse_uN` refines `ModInverse.modinverse`

  For each unsigned width there are two theorems:

    * `modinverse_uN_loop.spec` — the machine loop computes exactly the ℕ-model loop
      `ModInverse.loop` on the corresponding state, and never errors.
    * `modinverse_uN.spec` — the whole `modinverse_uN` never errors and value-matches
      `ModInverse.modinverse a.val m.val` (the `Option` structure and the witness agree).

  **Reading guide.** The `u8` pair below is the template; `u16`, `u32`, `u64`, `u128`
  are the *same proof scripts* with the width swapped (and `u128`'s `qs` step uses the
  Russian-peasant `mul_mod_u128` rather than a widening helper — same `@[step]` shape).
  Read `u8` and skim the rest.

  The file ends with `modinverse_u128_correct`: composing `modinverse_u128.spec` with
  `ModInverse.isCorrect` gives the end-to-end correctness of the extracted `u128` code.
-/

import ModInverse.Refinement.Helpers
import ModInverse.Proofs

open Aeneas Aeneas.Std Result
open modinverse

namespace Refinement

/-! ## `u8` — the template -/

/-- **Loop refinement for `modinverse_u8_loop`.** Preconditions match the model
    `State` invariants: `s, s_next < m` (kept reduced) and `0 < m`. -/
@[step]
theorem modinverse_u8_loop.spec (m r r_next s s_next : Std.U8)
    (hm : 0 < m.val) (hs : s.val < m.val) (hsn : s_next.val < m.val) :
    modinverse_u8_loop m r r_next s s_next ⦃ (res : Std.U8 × Std.U8) =>
      (res.1.val, res.2.val)
        = ModInverse.loop hm ⟨r.val, r_next.val, s.val, s_next.val, hs, hsn⟩ ⦄ := by
  unfold modinverse_u8_loop
  by_cases h : r_next = 0#u8
  · -- base case: r_next = 0, loop returns (r, s)
    simp only [h, bne_self_eq_false, Bool.false_eq_true, if_false]
    rw [ModInverse.loop, dif_pos (by simp)]
    simp
  · -- step case: r_next ≠ 0. Body runs one Euclidean step, then recurses; connect to
    -- the model's `loop = loop ∘ step` unfolding via `ModInverse.step`.
    simp only [h, bne_iff_ne, ne_eq, not_false_eq_true, if_true]
    step*
    · -- branch `s ≥ qs`
      rw [res_post]
      conv_rhs => rw [ModInverse.loop, dif_neg (by simp only []; scalar_tac)]
      congr 1
      simp only [ModInverse.step, ModInverse.State.mk.injEq]
      refine ⟨trivial, rem_post, trivial, ?_⟩
      rw [← q_post, ← qs_post]
      simp only [ModInverse.subMod]
      split <;> scalar_tac
    · -- branch `¬ s ≥ qs`
      rw [res_post]
      conv_rhs => rw [ModInverse.loop, dif_neg (by simp only []; scalar_tac)]
      congr 1
      simp only [ModInverse.step, ModInverse.State.mk.injEq]
      refine ⟨trivial, rem_post, trivial, ?_⟩
      rw [← q_post, ← qs_post]
      simp only [ModInverse.subMod]
      split <;> scalar_tac
  termination_by r_next.val
  decreasing_by
    · rw [rem_post]; exact Nat.mod_lt _ (by scalar_tac)
    · rw [rem_post]; exact Nat.mod_lt _ (by scalar_tac)

/-- **Top-level refinement for `modinverse_u8`.** -/
@[step]
theorem modinverse_u8.spec (a m : Std.U8) :
    modinverse_u8 a m ⦃ (r : Option Std.U8) => r.map (·.val) = ModInverse.modinverse a.val m.val ⦄ := by
  unfold modinverse_u8
  step*
  · -- m = 0: model returns `none`
    simp [ModInverse.modinverse]
  · -- m = 1: model returns `some 0`
    simp [ModInverse.modinverse]
  · -- 1 < m, loop gcd = 1: model returns `some s`
    have hlt : 1 < m.val := by scalar_tac
    rw [r_next_post] at r_post
    rw [ModInverse.modinverse, dif_pos hlt, ModInverse.modinverseCore, ← r_post]
    have hr : r.val = 1 := by scalar_tac
    simp [hr]
  · -- 1 < m, loop gcd ≠ 1: model returns `none`
    have hlt : 1 < m.val := by scalar_tac
    rw [r_next_post] at r_post
    rw [ModInverse.modinverse, dif_pos hlt, ModInverse.modinverseCore, ← r_post]
    have hr : r.val ≠ 1 := by scalar_tac
    simp [hr]

/-! ## `u16` (width-copy of `u8`) -/

@[step]
theorem modinverse_u16_loop.spec (m r r_next s s_next : Std.U16)
    (hm : 0 < m.val) (hs : s.val < m.val) (hsn : s_next.val < m.val) :
    modinverse_u16_loop m r r_next s s_next ⦃ (res : Std.U16 × Std.U16) =>
      (res.1.val, res.2.val)
        = ModInverse.loop hm ⟨r.val, r_next.val, s.val, s_next.val, hs, hsn⟩ ⦄ := by
  unfold modinverse_u16_loop
  by_cases h : r_next = 0#u16
  · simp only [h, bne_self_eq_false, Bool.false_eq_true, if_false]
    rw [ModInverse.loop, dif_pos (by simp)]
    simp
  · simp only [h, bne_iff_ne, ne_eq, not_false_eq_true, if_true]
    step*
    · rw [res_post]
      conv_rhs => rw [ModInverse.loop, dif_neg (by simp only []; scalar_tac)]
      congr 1
      simp only [ModInverse.step, ModInverse.State.mk.injEq]
      refine ⟨trivial, rem_post, trivial, ?_⟩
      rw [← q_post, ← qs_post]
      simp only [ModInverse.subMod]
      split <;> scalar_tac
    · rw [res_post]
      conv_rhs => rw [ModInverse.loop, dif_neg (by simp only []; scalar_tac)]
      congr 1
      simp only [ModInverse.step, ModInverse.State.mk.injEq]
      refine ⟨trivial, rem_post, trivial, ?_⟩
      rw [← q_post, ← qs_post]
      simp only [ModInverse.subMod]
      split <;> scalar_tac
  termination_by r_next.val
  decreasing_by
    · rw [rem_post]; exact Nat.mod_lt _ (by scalar_tac)
    · rw [rem_post]; exact Nat.mod_lt _ (by scalar_tac)

@[step]
theorem modinverse_u16.spec (a m : Std.U16) :
    modinverse_u16 a m ⦃ (r : Option Std.U16) => r.map (·.val) = ModInverse.modinverse a.val m.val ⦄ := by
  unfold modinverse_u16
  step*
  · simp [ModInverse.modinverse]
  · simp [ModInverse.modinverse]
  · have hlt : 1 < m.val := by scalar_tac
    rw [r_next_post] at r_post
    rw [ModInverse.modinverse, dif_pos hlt, ModInverse.modinverseCore, ← r_post]
    have hr : r.val = 1 := by scalar_tac
    simp [hr]
  · have hlt : 1 < m.val := by scalar_tac
    rw [r_next_post] at r_post
    rw [ModInverse.modinverse, dif_pos hlt, ModInverse.modinverseCore, ← r_post]
    have hr : r.val ≠ 1 := by scalar_tac
    simp [hr]

/-! ## `u32` (width-copy of `u8`) -/

@[step]
theorem modinverse_u32_loop.spec (m r r_next s s_next : Std.U32)
    (hm : 0 < m.val) (hs : s.val < m.val) (hsn : s_next.val < m.val) :
    modinverse_u32_loop m r r_next s s_next ⦃ (res : Std.U32 × Std.U32) =>
      (res.1.val, res.2.val)
        = ModInverse.loop hm ⟨r.val, r_next.val, s.val, s_next.val, hs, hsn⟩ ⦄ := by
  unfold modinverse_u32_loop
  by_cases h : r_next = 0#u32
  · simp only [h, bne_self_eq_false, Bool.false_eq_true, if_false]
    rw [ModInverse.loop, dif_pos (by simp)]
    simp
  · simp only [h, bne_iff_ne, ne_eq, not_false_eq_true, if_true]
    step*
    · rw [res_post]
      conv_rhs => rw [ModInverse.loop, dif_neg (by simp only []; scalar_tac)]
      congr 1
      simp only [ModInverse.step, ModInverse.State.mk.injEq]
      refine ⟨trivial, rem_post, trivial, ?_⟩
      rw [← q_post, ← qs_post]
      simp only [ModInverse.subMod]
      split <;> scalar_tac
    · rw [res_post]
      conv_rhs => rw [ModInverse.loop, dif_neg (by simp only []; scalar_tac)]
      congr 1
      simp only [ModInverse.step, ModInverse.State.mk.injEq]
      refine ⟨trivial, rem_post, trivial, ?_⟩
      rw [← q_post, ← qs_post]
      simp only [ModInverse.subMod]
      split <;> scalar_tac
  termination_by r_next.val
  decreasing_by
    · rw [rem_post]; exact Nat.mod_lt _ (by scalar_tac)
    · rw [rem_post]; exact Nat.mod_lt _ (by scalar_tac)

@[step]
theorem modinverse_u32.spec (a m : Std.U32) :
    modinverse_u32 a m ⦃ (r : Option Std.U32) => r.map (·.val) = ModInverse.modinverse a.val m.val ⦄ := by
  unfold modinverse_u32
  step*
  · simp [ModInverse.modinverse]
  · simp [ModInverse.modinverse]
  · have hlt : 1 < m.val := by scalar_tac
    rw [r_next_post] at r_post
    rw [ModInverse.modinverse, dif_pos hlt, ModInverse.modinverseCore, ← r_post]
    have hr : r.val = 1 := by scalar_tac
    simp [hr]
  · have hlt : 1 < m.val := by scalar_tac
    rw [r_next_post] at r_post
    rw [ModInverse.modinverse, dif_pos hlt, ModInverse.modinverseCore, ← r_post]
    have hr : r.val ≠ 1 := by scalar_tac
    simp [hr]

/-! ## `u64` (width-copy of `u8`) -/

@[step]
theorem modinverse_u64_loop.spec (m r r_next s s_next : Std.U64)
    (hm : 0 < m.val) (hs : s.val < m.val) (hsn : s_next.val < m.val) :
    modinverse_u64_loop m r r_next s s_next ⦃ (res : Std.U64 × Std.U64) =>
      (res.1.val, res.2.val)
        = ModInverse.loop hm ⟨r.val, r_next.val, s.val, s_next.val, hs, hsn⟩ ⦄ := by
  unfold modinverse_u64_loop
  by_cases h : r_next = 0#u64
  · simp only [h, bne_self_eq_false, Bool.false_eq_true, if_false]
    rw [ModInverse.loop, dif_pos (by simp)]
    simp
  · simp only [h, bne_iff_ne, ne_eq, not_false_eq_true, if_true]
    step*
    · rw [res_post]
      conv_rhs => rw [ModInverse.loop, dif_neg (by simp only []; scalar_tac)]
      congr 1
      simp only [ModInverse.step, ModInverse.State.mk.injEq]
      refine ⟨trivial, rem_post, trivial, ?_⟩
      rw [← q_post, ← qs_post]
      simp only [ModInverse.subMod]
      split <;> scalar_tac
    · rw [res_post]
      conv_rhs => rw [ModInverse.loop, dif_neg (by simp only []; scalar_tac)]
      congr 1
      simp only [ModInverse.step, ModInverse.State.mk.injEq]
      refine ⟨trivial, rem_post, trivial, ?_⟩
      rw [← q_post, ← qs_post]
      simp only [ModInverse.subMod]
      split <;> scalar_tac
  termination_by r_next.val
  decreasing_by
    · rw [rem_post]; exact Nat.mod_lt _ (by scalar_tac)
    · rw [rem_post]; exact Nat.mod_lt _ (by scalar_tac)

@[step]
theorem modinverse_u64.spec (a m : Std.U64) :
    modinverse_u64 a m ⦃ (r : Option Std.U64) => r.map (·.val) = ModInverse.modinverse a.val m.val ⦄ := by
  unfold modinverse_u64
  step*
  · simp [ModInverse.modinverse]
  · simp [ModInverse.modinverse]
  · have hlt : 1 < m.val := by scalar_tac
    rw [r_next_post] at r_post
    rw [ModInverse.modinverse, dif_pos hlt, ModInverse.modinverseCore, ← r_post]
    have hr : r.val = 1 := by scalar_tac
    simp [hr]
  · have hlt : 1 < m.val := by scalar_tac
    rw [r_next_post] at r_post
    rw [ModInverse.modinverse, dif_pos hlt, ModInverse.modinverseCore, ← r_post]
    have hr : r.val ≠ 1 := by scalar_tac
    simp [hr]

/-! ## `u128` (width-copy of `u8`; the `qs` step uses `mul_mod_u128`) -/

@[step]
theorem modinverse_u128_loop.spec (m r r_next s s_next : Std.U128)
    (hm : 0 < m.val) (hs : s.val < m.val) (hsn : s_next.val < m.val) :
    modinverse_u128_loop m r r_next s s_next ⦃ (res : Std.U128 × Std.U128) =>
      (res.1.val, res.2.val)
        = ModInverse.loop hm ⟨r.val, r_next.val, s.val, s_next.val, hs, hsn⟩ ⦄ := by
  unfold modinverse_u128_loop
  by_cases h : r_next = 0#u128
  · simp only [h, bne_self_eq_false, Bool.false_eq_true, if_false]
    rw [ModInverse.loop, dif_pos (by simp)]
    simp
  · simp only [h, bne_iff_ne, ne_eq, not_false_eq_true, if_true]
    step*
    · rw [res_post]
      conv_rhs => rw [ModInverse.loop, dif_neg (by simp only []; scalar_tac)]
      congr 1
      simp only [ModInverse.step, ModInverse.State.mk.injEq]
      refine ⟨trivial, rem_post, trivial, ?_⟩
      rw [← q_post, ← qs_post]
      simp only [ModInverse.subMod]
      split <;> scalar_tac
    · rw [res_post]
      conv_rhs => rw [ModInverse.loop, dif_neg (by simp only []; scalar_tac)]
      congr 1
      simp only [ModInverse.step, ModInverse.State.mk.injEq]
      refine ⟨trivial, rem_post, trivial, ?_⟩
      rw [← q_post, ← qs_post]
      simp only [ModInverse.subMod]
      split <;> scalar_tac
  termination_by r_next.val
  decreasing_by
    · rw [rem_post]; exact Nat.mod_lt _ (by scalar_tac)
    · rw [rem_post]; exact Nat.mod_lt _ (by scalar_tac)

/-- **Top-level refinement for `modinverse_u128`.** Composed with
    `ModInverse.isCorrect`, this is the end-to-end correctness of the extracted code. -/
@[step]
theorem modinverse_u128.spec (a m : Std.U128) :
    modinverse_u128 a m ⦃ (r : Option Std.U128) => r.map (·.val) = ModInverse.modinverse a.val m.val ⦄ := by
  unfold modinverse_u128
  step*
  · simp [ModInverse.modinverse]
  · simp [ModInverse.modinverse]
  · have hlt : 1 < m.val := by scalar_tac
    rw [r_next_post] at r_post
    rw [ModInverse.modinverse, dif_pos hlt, ModInverse.modinverseCore, ← r_post]
    have hr : r.val = 1 := by scalar_tac
    simp [hr]
  · have hlt : 1 < m.val := by scalar_tac
    rw [r_next_post] at r_post
    rw [ModInverse.modinverse, dif_pos hlt, ModInverse.modinverseCore, ← r_post]
    have hr : r.val ≠ 1 := by scalar_tac
    simp [hr]

/-! ## End-to-end correctness of the extracted unsigned machine code

  Composing the per-width refinement (`modinverse_uN.spec`: machine refines the ℕ
  model) with `ModInverse.isCorrect` (the model meets the specification) certifies
  the *actual extracted machine code*, stated over the public trait methods
  (`<uN as ModInverse>::modinverse` in the Rust) with no reference to the model:
  the four clauses of `UnsignedMachineCorrect` transport the four fields of
  `ModInverse.Spec.Correct` to the machine level. One generic composition lemma
  serves every unsigned width (and `usize`, in `Platform.lean`). -/

/-- The machine-level reading of `ModInverse.Spec.Correct` for an extracted
    unsigned `modinverse` at width `w`: it never errors, a returned witness is a
    real inverse and the canonical representative in `[0, m)`, a witness is
    produced whenever one exists, and `none` is returned in exactly the
    no-inverse cases. -/
def UnsignedMachineCorrect (w : UScalarTy)
    (f : UScalar w → UScalar w → Result (Option (UScalar w))) : Prop :=
  ∀ a m : UScalar w,
    f a m ⦃ (r : Option (UScalar w)) =>
      -- sound: a returned witness really is an inverse
      (∀ s, r = some s → a.val * s.val ≡ 1 [MOD m.val]) ∧
      -- bounded: the witness is the canonical representative in `[0, m)`
      (∀ s, r = some s → 0 < m.val → s.val < m.val) ∧
      -- complete: an inverse is produced whenever one exists
      (0 < m.val → Nat.Coprime a.val m.val → ∃ s, r = some s) ∧
      -- fails exactly: `none` in exactly the no-inverse cases
      (r = none ↔ m.val = 0 ∨ ¬ Nat.Coprime a.val m.val) ⦄

/-- Generic composition: any width whose machine code value-matches the ℕ model
    is machine-correct, by `ModInverse.isCorrect`. -/
theorem composeUnsigned {w : UScalarTy}
    {f : UScalar w → UScalar w → Result (Option (UScalar w))}
    (hf : ∀ a m : UScalar w,
      f a m ⦃ (r : Option (UScalar w)) =>
        r.map (·.val) = ModInverse.modinverse a.val m.val ⦄) :
    UnsignedMachineCorrect w f := by
  intro a m
  apply WP.spec_mono (hf a m)
  intro r hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- sound
    intro s hs
    apply ModInverse.isCorrect.sound
    rw [← hr, hs]; rfl
  · -- bounded
    intro s hs hm
    apply ModInverse.isCorrect.bounded _ _ _ hm
    rw [← hr, hs]; rfl
  · -- complete
    intro hm hcop
    obtain ⟨sm, hsm⟩ := ModInverse.isCorrect.complete a.val m.val hm hcop
    rw [hsm] at hr
    cases r with
    | none => simp at hr
    | some s => exact ⟨s, rfl⟩
  · -- fails exactly
    constructor
    · intro hnone
      apply (ModInverse.isCorrect.failsExactly a.val m.val).mp
      rw [hnone] at hr
      simpa using hr.symm
    · intro hcase
      have hmodel := (ModInverse.isCorrect.failsExactly a.val m.val).mpr hcase
      rw [hmodel] at hr
      simpa using hr

/-- **The extracted `<u8 as ModInverse>::modinverse` is a correct modular inverse.** -/
theorem modinverse_u8_correct :
    UnsignedMachineCorrect .U8 U8.Insts.ModinverseModInverse.modinverse :=
  composeUnsigned fun a m => by
    unfold U8.Insts.ModinverseModInverse.modinverse
    exact modinverse_u8.spec a m

/-- **The extracted `<u16 as ModInverse>::modinverse` is a correct modular inverse.** -/
theorem modinverse_u16_correct :
    UnsignedMachineCorrect .U16 U16.Insts.ModinverseModInverse.modinverse :=
  composeUnsigned fun a m => by
    unfold U16.Insts.ModinverseModInverse.modinverse
    exact modinverse_u16.spec a m

/-- **The extracted `<u32 as ModInverse>::modinverse` is a correct modular inverse.** -/
theorem modinverse_u32_correct :
    UnsignedMachineCorrect .U32 U32.Insts.ModinverseModInverse.modinverse :=
  composeUnsigned fun a m => by
    unfold U32.Insts.ModinverseModInverse.modinverse
    exact modinverse_u32.spec a m

/-- **The extracted `<u64 as ModInverse>::modinverse` is a correct modular inverse.** -/
theorem modinverse_u64_correct :
    UnsignedMachineCorrect .U64 U64.Insts.ModinverseModInverse.modinverse :=
  composeUnsigned fun a m => by
    unfold U64.Insts.ModinverseModInverse.modinverse
    exact modinverse_u64.spec a m

/-- **The extracted `<u128 as ModInverse>::modinverse` is a correct modular inverse.** -/
theorem modinverse_u128_correct :
    UnsignedMachineCorrect .U128 U128.Insts.ModinverseModInverse.modinverse :=
  composeUnsigned fun a m => by
    unfold U128.Insts.ModinverseModInverse.modinverse
    exact modinverse_u128.spec a m

end Refinement
