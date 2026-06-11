/-
  # Signed refinement: `modinverse_iN` refines the model on the canonicalized input

  The signed `modinverse` for `iN` (extracted as `IN.Insts.ModinverseModInverse.modinverse`)
  returns `none` when `m = 0`; otherwise it canonicalizes `self` to `a_u ∈ [0, |m|)`
  (`ModInverse.reduceSigned`), runs the *unsigned* core on `(a_u, |m|)`, and casts the
  inverse back via `Option.map`. Each `modinverse_iN_spec` says the machine never errors
  and its `.val` matches `ModInverse.modinverse (reduceSigned self.val |m|) |m|`, lifted
  to `ℤ`.

  The cast back and the `Option.map` go through the trusted specs in `ModInverse.Extern`.

  **Reading guide.** Each width is `signed_tail_iN` (the shared `modinverse_uN` + cast-back
  tail, factoring out the three `a_u` branches' common work) followed by the spec proper.
  The `i8` pair is the template; `i16`–`i128` are the same scripts with the width swapped.
  Read `i8` and skim the rest. The single `hcast_val` lemma serves every width.
-/

import ModInverse.Refinement.Unsigned
import ModInverse.Extern
import ModInverse.Signed

open Aeneas Aeneas.Std Result
open modinverse

namespace Refinement

/-- The unsigned→signed cast back preserves value for inverses `≤ iN::MAX`. One lemma
    for every width (`UScalar.hcast` and its spec are width-generic). -/
private lemma hcast_val {src : UScalarTy} {tgt : IScalarTy} (s : UScalar src)
    (h : (s.val : ℤ) ≤ IScalar.max tgt) : (UScalar.hcast tgt s).val = (s.val : ℤ) := by
  have H := UScalar.hcast_inBounds_spec tgt s (by simpa using h)
  simpa [lift, WP.spec_ok] using H

/-! ## `i8` — the template -/

/-- The shared tail: run `modinverse_u8` on the canonicalized input, then cast back
    through `Option.map`. Factors the `Option.map`/`hcast` reasoning out of the three
    `a_u` branches. -/
private lemma signed_tail_i8 {A : ℤ} (a_u m_abs : Std.U8) (M : ℕ)
    (hM : 0 < M) (hMle : M ≤ 128) (hmabs : m_abs.val = M)
    (hau : a_u.val = ModInverse.reduceSigned A M) :
    (do let o ← modinverse_u8 a_u m_abs
        core.option.Option.map
          ModInverseI8.modinverse.closure.Insts.CoreOpsFunctionFnOnceTupleU8I8 o ())
      ⦃ (r : Option Std.I8) =>
          r.map (·.val) =
            (ModInverse.modinverse (ModInverse.reduceSigned A M) M).map (Int.ofNat ·) ⦄ := by
  step*
  rw [hau, hmabs] at o_post
  cases o with
  | none =>
    rw [ModInverse.Extern.Option_map_none]
    have hmodel : ModInverse.modinverse (ModInverse.reduceSigned A M) M = none := by
      simpa using o_post.symm
    simp [WP.spec_ok, hmodel]
  | some s =>
    rw [ModInverse.Extern.Option_map_some]
    simp only [Option.map_some] at o_post
    have hsM : s.val < M := ModInverse.modinverse_lt _ M s.val hM o_post.symm
    have hb : (s.val : ℤ) ≤ IScalar.max .I8 := by scalar_tac
    rw [← o_post]
    simp [ModInverseI8.modinverse.closure.Insts.CoreOpsFunctionFnOnceTupleU8I8.call_once,
          WP.spec_ok, hcast_val s hb]

@[step]
theorem modinverse_i8_spec (a m : Std.I8) :
    I8.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.I8) =>
      r.map (·.val) =
        (ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs).map
          (Int.ofNat ·) ⦄ := by
  unfold I8.Insts.ModinverseModInverse.modinverse
  step*
  case h1 => simp [ModInverse.modinverse]                 -- m = 0 → none
  case hnz => rw [m_abs_post, Int.natAbs_ne_zero]; scalar_tac  -- side goal: |m| ≠ 0
  -- main case: m ≠ 0
  have hMpos : 0 < (↑m : ℤ).natAbs := Int.natAbs_pos.mpr (by scalar_tac)
  have hMle : (↑m : ℤ).natAbs ≤ 128 :=
    ModInverse.natAbs_le_of_bounds (by scalar_tac) (by scalar_tac)
  have haabs : (↑a_abs : ℕ) = (↑a : ℤ).natAbs % (↑m : ℤ).natAbs := by
    rw [a_abs_post, i_post, m_abs_post]
  split
  · -- a < 0
    split
    · -- |a| % |m| ≠ 0 : a_u = |m| - |a| % |m|
      step
      refine signed_tail_i8 a_u m_abs _ hMpos hMle m_abs_post ?_
      rw [a_u_post1, m_abs_post, haabs]
      exact ModInverse.reduceSigned_eq_neg_pos hMpos (by scalar_tac) (by rw [← haabs]; scalar_tac)
    · -- |a| % |m| = 0 : a_u = 0
      refine signed_tail_i8 a_abs m_abs _ hMpos hMle m_abs_post ?_
      have hz : (↑a : ℤ).natAbs % (↑m : ℤ).natAbs = 0 := by rw [← haabs]; scalar_tac
      rw [haabs, hz]
      exact ModInverse.reduceSigned_eq_neg_zero hMpos hz
  · -- a ≥ 0 : a_u = |a| % |m|
    refine signed_tail_i8 a_abs m_abs _ hMpos hMle m_abs_post ?_
    rw [haabs]
    exact ModInverse.reduceSigned_eq_nonneg hMpos (by scalar_tac)

/-! ## `i16` (width-copy of `i8`) -/

private lemma signed_tail_i16 {A : ℤ} (a_u m_abs : Std.U16) (M : ℕ)
    (hM : 0 < M) (hMle : M ≤ 32768) (hmabs : m_abs.val = M)
    (hau : a_u.val = ModInverse.reduceSigned A M) :
    (do let o ← modinverse_u16 a_u m_abs
        core.option.Option.map
          ModInverseI16.modinverse.closure.Insts.CoreOpsFunctionFnOnceTupleU16I16 o ())
      ⦃ (r : Option Std.I16) =>
          r.map (·.val) =
            (ModInverse.modinverse (ModInverse.reduceSigned A M) M).map (Int.ofNat ·) ⦄ := by
  step*
  rw [hau, hmabs] at o_post
  cases o with
  | none =>
    rw [ModInverse.Extern.Option_map_none]
    have hmodel : ModInverse.modinverse (ModInverse.reduceSigned A M) M = none := by
      simpa using o_post.symm
    simp [WP.spec_ok, hmodel]
  | some s =>
    rw [ModInverse.Extern.Option_map_some]
    simp only [Option.map_some] at o_post
    have hsM : s.val < M := ModInverse.modinverse_lt _ M s.val hM o_post.symm
    have hb : (s.val : ℤ) ≤ IScalar.max .I16 := by scalar_tac
    rw [← o_post]
    simp [ModInverseI16.modinverse.closure.Insts.CoreOpsFunctionFnOnceTupleU16I16.call_once,
          WP.spec_ok, hcast_val s hb]

@[step]
theorem modinverse_i16_spec (a m : Std.I16) :
    I16.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.I16) =>
      r.map (·.val) =
        (ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs).map
          (Int.ofNat ·) ⦄ := by
  unfold I16.Insts.ModinverseModInverse.modinverse
  step*
  case h1 => simp [ModInverse.modinverse]
  case hnz => rw [m_abs_post, Int.natAbs_ne_zero]; scalar_tac
  have hMpos : 0 < (↑m : ℤ).natAbs := Int.natAbs_pos.mpr (by scalar_tac)
  have hMle : (↑m : ℤ).natAbs ≤ 32768 :=
    ModInverse.natAbs_le_of_bounds (by scalar_tac) (by scalar_tac)
  have haabs : (↑a_abs : ℕ) = (↑a : ℤ).natAbs % (↑m : ℤ).natAbs := by
    rw [a_abs_post, i_post, m_abs_post]
  split
  · split
    · step
      refine signed_tail_i16 a_u m_abs _ hMpos hMle m_abs_post ?_
      rw [a_u_post1, m_abs_post, haabs]
      exact ModInverse.reduceSigned_eq_neg_pos hMpos (by scalar_tac) (by rw [← haabs]; scalar_tac)
    · refine signed_tail_i16 a_abs m_abs _ hMpos hMle m_abs_post ?_
      have hz : (↑a : ℤ).natAbs % (↑m : ℤ).natAbs = 0 := by rw [← haabs]; scalar_tac
      rw [haabs, hz]
      exact ModInverse.reduceSigned_eq_neg_zero hMpos hz
  · refine signed_tail_i16 a_abs m_abs _ hMpos hMle m_abs_post ?_
    rw [haabs]
    exact ModInverse.reduceSigned_eq_nonneg hMpos (by scalar_tac)

/-! ## `i32` (width-copy of `i8`) -/

private lemma signed_tail_i32 {A : ℤ} (a_u m_abs : Std.U32) (M : ℕ)
    (hM : 0 < M) (hMle : M ≤ 2147483648) (hmabs : m_abs.val = M)
    (hau : a_u.val = ModInverse.reduceSigned A M) :
    (do let o ← modinverse_u32 a_u m_abs
        core.option.Option.map
          ModInverseI32.modinverse.closure.Insts.CoreOpsFunctionFnOnceTupleU32I32 o ())
      ⦃ (r : Option Std.I32) =>
          r.map (·.val) =
            (ModInverse.modinverse (ModInverse.reduceSigned A M) M).map (Int.ofNat ·) ⦄ := by
  step*
  rw [hau, hmabs] at o_post
  cases o with
  | none =>
    rw [ModInverse.Extern.Option_map_none]
    have hmodel : ModInverse.modinverse (ModInverse.reduceSigned A M) M = none := by
      simpa using o_post.symm
    simp [WP.spec_ok, hmodel]
  | some s =>
    rw [ModInverse.Extern.Option_map_some]
    simp only [Option.map_some] at o_post
    have hsM : s.val < M := ModInverse.modinverse_lt _ M s.val hM o_post.symm
    have hb : (s.val : ℤ) ≤ IScalar.max .I32 := by scalar_tac
    rw [← o_post]
    simp [ModInverseI32.modinverse.closure.Insts.CoreOpsFunctionFnOnceTupleU32I32.call_once,
          WP.spec_ok, hcast_val s hb]

@[step]
theorem modinverse_i32_spec (a m : Std.I32) :
    I32.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.I32) =>
      r.map (·.val) =
        (ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs).map
          (Int.ofNat ·) ⦄ := by
  unfold I32.Insts.ModinverseModInverse.modinverse
  step*
  case h1 => simp [ModInverse.modinverse]
  case hnz => rw [m_abs_post, Int.natAbs_ne_zero]; scalar_tac
  have hMpos : 0 < (↑m : ℤ).natAbs := Int.natAbs_pos.mpr (by scalar_tac)
  have hMle : (↑m : ℤ).natAbs ≤ 2147483648 :=
    ModInverse.natAbs_le_of_bounds (by scalar_tac) (by scalar_tac)
  have haabs : (↑a_abs : ℕ) = (↑a : ℤ).natAbs % (↑m : ℤ).natAbs := by
    rw [a_abs_post, i_post, m_abs_post]
  split
  · split
    · step
      refine signed_tail_i32 a_u m_abs _ hMpos hMle m_abs_post ?_
      rw [a_u_post1, m_abs_post, haabs]
      exact ModInverse.reduceSigned_eq_neg_pos hMpos (by scalar_tac) (by rw [← haabs]; scalar_tac)
    · refine signed_tail_i32 a_abs m_abs _ hMpos hMle m_abs_post ?_
      have hz : (↑a : ℤ).natAbs % (↑m : ℤ).natAbs = 0 := by rw [← haabs]; scalar_tac
      rw [haabs, hz]
      exact ModInverse.reduceSigned_eq_neg_zero hMpos hz
  · refine signed_tail_i32 a_abs m_abs _ hMpos hMle m_abs_post ?_
    rw [haabs]
    exact ModInverse.reduceSigned_eq_nonneg hMpos (by scalar_tac)

/-! ## `i64` (width-copy of `i8`) -/

private lemma signed_tail_i64 {A : ℤ} (a_u m_abs : Std.U64) (M : ℕ)
    (hM : 0 < M) (hMle : M ≤ 9223372036854775808) (hmabs : m_abs.val = M)
    (hau : a_u.val = ModInverse.reduceSigned A M) :
    (do let o ← modinverse_u64 a_u m_abs
        core.option.Option.map
          ModInverseI64.modinverse.closure.Insts.CoreOpsFunctionFnOnceTupleU64I64 o ())
      ⦃ (r : Option Std.I64) =>
          r.map (·.val) =
            (ModInverse.modinverse (ModInverse.reduceSigned A M) M).map (Int.ofNat ·) ⦄ := by
  step*
  rw [hau, hmabs] at o_post
  cases o with
  | none =>
    rw [ModInverse.Extern.Option_map_none]
    have hmodel : ModInverse.modinverse (ModInverse.reduceSigned A M) M = none := by
      simpa using o_post.symm
    simp [WP.spec_ok, hmodel]
  | some s =>
    rw [ModInverse.Extern.Option_map_some]
    simp only [Option.map_some] at o_post
    have hsM : s.val < M := ModInverse.modinverse_lt _ M s.val hM o_post.symm
    have hb : (s.val : ℤ) ≤ IScalar.max .I64 := by scalar_tac
    rw [← o_post]
    simp [ModInverseI64.modinverse.closure.Insts.CoreOpsFunctionFnOnceTupleU64I64.call_once,
          WP.spec_ok, hcast_val s hb]

@[step]
theorem modinverse_i64_spec (a m : Std.I64) :
    I64.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.I64) =>
      r.map (·.val) =
        (ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs).map
          (Int.ofNat ·) ⦄ := by
  unfold I64.Insts.ModinverseModInverse.modinverse
  step*
  case h1 => simp [ModInverse.modinverse]
  case hnz => rw [m_abs_post, Int.natAbs_ne_zero]; scalar_tac
  have hMpos : 0 < (↑m : ℤ).natAbs := Int.natAbs_pos.mpr (by scalar_tac)
  have hMle : (↑m : ℤ).natAbs ≤ 9223372036854775808 :=
    ModInverse.natAbs_le_of_bounds (by scalar_tac) (by scalar_tac)
  have haabs : (↑a_abs : ℕ) = (↑a : ℤ).natAbs % (↑m : ℤ).natAbs := by
    rw [a_abs_post, i_post, m_abs_post]
  split
  · split
    · step
      refine signed_tail_i64 a_u m_abs _ hMpos hMle m_abs_post ?_
      rw [a_u_post1, m_abs_post, haabs]
      exact ModInverse.reduceSigned_eq_neg_pos hMpos (by scalar_tac) (by rw [← haabs]; scalar_tac)
    · refine signed_tail_i64 a_abs m_abs _ hMpos hMle m_abs_post ?_
      have hz : (↑a : ℤ).natAbs % (↑m : ℤ).natAbs = 0 := by rw [← haabs]; scalar_tac
      rw [haabs, hz]
      exact ModInverse.reduceSigned_eq_neg_zero hMpos hz
  · refine signed_tail_i64 a_abs m_abs _ hMpos hMle m_abs_post ?_
    rw [haabs]
    exact ModInverse.reduceSigned_eq_nonneg hMpos (by scalar_tac)

/-! ## `i128` (width-copy of `i8`) -/

private lemma signed_tail_i128 {A : ℤ} (a_u m_abs : Std.U128) (M : ℕ)
    (hM : 0 < M) (hMle : M ≤ 170141183460469231731687303715884105728) (hmabs : m_abs.val = M)
    (hau : a_u.val = ModInverse.reduceSigned A M) :
    (do let o ← modinverse_u128 a_u m_abs
        core.option.Option.map
          ModInverseI128.modinverse.closure.Insts.CoreOpsFunctionFnOnceTupleU128I128 o ())
      ⦃ (r : Option Std.I128) =>
          r.map (·.val) =
            (ModInverse.modinverse (ModInverse.reduceSigned A M) M).map (Int.ofNat ·) ⦄ := by
  step*
  rw [hau, hmabs] at o_post
  cases o with
  | none =>
    rw [ModInverse.Extern.Option_map_none]
    have hmodel : ModInverse.modinverse (ModInverse.reduceSigned A M) M = none := by
      simpa using o_post.symm
    simp [WP.spec_ok, hmodel]
  | some s =>
    rw [ModInverse.Extern.Option_map_some]
    simp only [Option.map_some] at o_post
    have hsM : s.val < M := ModInverse.modinverse_lt _ M s.val hM o_post.symm
    have hb : (s.val : ℤ) ≤ IScalar.max .I128 := by scalar_tac
    rw [← o_post]
    simp [ModInverseI128.modinverse.closure.Insts.CoreOpsFunctionFnOnceTupleU128I128.call_once,
          WP.spec_ok, hcast_val s hb]

@[step]
theorem modinverse_i128_spec (a m : Std.I128) :
    I128.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.I128) =>
      r.map (·.val) =
        (ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs).map
          (Int.ofNat ·) ⦄ := by
  unfold I128.Insts.ModinverseModInverse.modinverse
  step*
  case h1 => simp [ModInverse.modinverse]
  case hnz => rw [m_abs_post, Int.natAbs_ne_zero]; scalar_tac
  have hMpos : 0 < (↑m : ℤ).natAbs := Int.natAbs_pos.mpr (by scalar_tac)
  have hMle : (↑m : ℤ).natAbs ≤ 170141183460469231731687303715884105728 :=
    ModInverse.natAbs_le_of_bounds (by scalar_tac) (by scalar_tac)
  have haabs : (↑a_abs : ℕ) = (↑a : ℤ).natAbs % (↑m : ℤ).natAbs := by
    rw [a_abs_post, i_post, m_abs_post]
  split
  · split
    · step
      refine signed_tail_i128 a_u m_abs _ hMpos hMle m_abs_post ?_
      rw [a_u_post1, m_abs_post, haabs]
      exact ModInverse.reduceSigned_eq_neg_pos hMpos (by scalar_tac) (by rw [← haabs]; scalar_tac)
    · refine signed_tail_i128 a_abs m_abs _ hMpos hMle m_abs_post ?_
      have hz : (↑a : ℤ).natAbs % (↑m : ℤ).natAbs = 0 := by rw [← haabs]; scalar_tac
      rw [haabs, hz]
      exact ModInverse.reduceSigned_eq_neg_zero hMpos hz
  · refine signed_tail_i128 a_abs m_abs _ hMpos hMle m_abs_post ?_
    rw [haabs]
    exact ModInverse.reduceSigned_eq_nonneg hMpos (by scalar_tac)

/-! ## End-to-end correctness of the extracted signed `i128` machine code

  Composing `modinverse_i128_spec` (the machine refines the ℕ model on the canonicalized
  input) with `ModInverse.isCorrect` (the model is a correct inverse) certifies the actual
  extracted signed code, over `ℤ`: for `m ≠ 0`, `modinverse_i128` never errors, any
  returned witness is a genuine inverse in the canonical range `[0, |m|)`, and a witness
  is returned whenever one exists. The other signed widths (`i8`–`i64`, `isize`) compose
  identically. -/

/-- **The extracted signed `modinverse_i128` is a correct modular inverse over `ℤ`.** -/
theorem modinverse_i128_correct (a m : Std.I128) (hm : m.val ≠ 0) :
    I128.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.I128) =>
      -- soundness: a returned witness really is an inverse of `a` modulo `m`
      (∀ s : Std.I128, r = some s → a.val * s.val ≡ 1 [ZMOD m.val]) ∧
      -- bound: the witness is the canonical representative in `[0, |m|)`
      (∀ s : Std.I128, r = some s → 0 ≤ s.val ∧ s.val < m.val.natAbs) ∧
      -- completeness: an inverse is produced whenever one exists
      (Int.gcd a.val m.val = 1 → ∃ s : Std.I128, r = some s) ⦄ := by
  have hM : 0 < m.val.natAbs := Int.natAbs_pos.mpr hm
  apply WP.spec_mono (modinverse_i128_spec a m)
  intro r hr
  refine ⟨?_, ?_, ?_⟩
  · -- soundness
    intro s hs
    subst hs
    simp only [Option.map_some] at hr
    rcases hmod : ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs
      with _ | k
    · rw [hmod] at hr; simp at hr
    · rw [hmod] at hr
      simp only [Option.map_some] at hr
      have hsk : s.val = (k : ℤ) := by simpa using hr
      have hsound := ModInverse.isCorrect.sound _ _ _ hmod
      rw [hsk]
      exact ModInverse.modEq_natAbs_iff.mpr (ModInverse.reduceSigned_sound hM hsound)
  · -- bound
    intro s hs
    subst hs
    simp only [Option.map_some] at hr
    rcases hmod : ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs
      with _ | k
    · rw [hmod] at hr; simp at hr
    · rw [hmod] at hr
      simp only [Option.map_some] at hr
      have hsk : s.val = (k : ℤ) := by simpa using hr
      have hbnd := ModInverse.isCorrect.bounded _ _ _ hM hmod
      exact ⟨by rw [hsk]; positivity, by rw [hsk]; exact_mod_cast hbnd⟩
  · -- completeness
    intro hgcd
    have hcop : Nat.Coprime (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs :=
      ModInverse.coprime_reduceSigned hM hgcd
    obtain ⟨k, hk⟩ :=
      ModInverse.isCorrect.complete (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs hM hcop
    rw [hk] at hr
    simp only [Option.map_some] at hr
    cases r with
    | none => simp at hr
    | some s => exact ⟨s, rfl⟩

end Refinement
