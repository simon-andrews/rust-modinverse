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

/-! ## End-to-end correctness of the extracted signed machine code

  Composing the per-width refinement (`modinverse_iN_spec`: machine refines the ℕ
  model on the canonicalized input) with `ModInverse.isCorrect` certifies the
  *actual extracted signed code*, stated over the public trait methods
  (`<iN as ModInverse>::modinverse` in the Rust) with no reference to the model:
  the four clauses of `SignedMachineCorrect` transport the four fields of
  `ModInverse.Spec.Correct` to the machine level, over `ℤ`, with the witness in
  the canonical range `[0, |m|)`. One generic composition lemma serves every
  signed width (and `isize`, in `Platform.lean`). -/

/-- The machine-level reading of `ModInverse.Spec.Correct` for an extracted
    signed `modinverse` at width `w`, over `ℤ`: it never errors, a returned
    witness is a real inverse and the canonical representative in `[0, |m|)`, a
    witness is produced whenever one exists, and `none` is returned in exactly
    the no-inverse cases. -/
def SignedMachineCorrect (w : IScalarTy)
    (f : IScalar w → IScalar w → Result (Option (IScalar w))) : Prop :=
  ∀ a m : IScalar w,
    f a m ⦃ (r : Option (IScalar w)) =>
      -- sound: a returned witness really is an inverse
      (∀ s, r = some s → a.val * s.val ≡ 1 [ZMOD m.val]) ∧
      -- bounded: the witness is the canonical representative in `[0, |m|)`
      (∀ s, r = some s → 0 ≤ s.val ∧ s.val < m.val.natAbs) ∧
      -- complete: an inverse is produced whenever one exists
      (m.val ≠ 0 → Int.gcd a.val m.val = 1 → ∃ s, r = some s) ∧
      -- fails exactly: `none` in exactly the no-inverse cases
      (r = none ↔ m.val = 0 ∨ Int.gcd a.val m.val ≠ 1) ⦄

/-- Generic composition: any width whose machine code value-matches the ℕ model
    on the canonicalized input is machine-correct, by `ModInverse.isCorrect` and
    the `reduceSigned` bridge lemmas. -/
theorem composeSigned {w : IScalarTy}
    {f : IScalar w → IScalar w → Result (Option (IScalar w))}
    (hf : ∀ a m : IScalar w,
      f a m ⦃ (r : Option (IScalar w)) =>
        r.map (·.val) =
          (ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs)
            m.val.natAbs).map (Int.ofNat ·) ⦄) :
    SignedMachineCorrect w f := by
  intro a m
  apply WP.spec_mono (hf a m)
  intro r hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- sound (`m ≠ 0` is forced: for `m = 0` the model returns `none`)
    intro s hs
    subst hs
    simp only [Option.map_some] at hr
    rcases hmod : ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs
      with _ | k
    · rw [hmod] at hr; simp at hr
    · rcases Nat.eq_zero_or_pos m.val.natAbs with h0 | hM
      · rw [h0] at hmod; simp [ModInverse.modinverse] at hmod
      · rw [hmod] at hr
        simp only [Option.map_some] at hr
        have hsk : s.val = (k : ℤ) := by simpa using hr
        have hsound := ModInverse.isCorrect.sound _ _ _ hmod
        rw [hsk]
        exact ModInverse.modEq_natAbs_iff.mpr (ModInverse.reduceSigned_sound hM hsound)
  · -- bounded
    intro s hs
    subst hs
    simp only [Option.map_some] at hr
    rcases hmod : ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs
      with _ | k
    · rw [hmod] at hr; simp at hr
    · rcases Nat.eq_zero_or_pos m.val.natAbs with h0 | hM
      · rw [h0] at hmod; simp [ModInverse.modinverse] at hmod
      · rw [hmod] at hr
        simp only [Option.map_some] at hr
        have hsk : s.val = (k : ℤ) := by simpa using hr
        have hbnd := ModInverse.isCorrect.bounded _ _ _ hM hmod
        exact ⟨by rw [hsk]; positivity, by rw [hsk]; exact_mod_cast hbnd⟩
  · -- complete
    intro hm hgcd
    have hM : 0 < m.val.natAbs := Int.natAbs_pos.mpr hm
    have hcop : Nat.Coprime (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs :=
      ModInverse.coprime_reduceSigned hM hgcd
    obtain ⟨k, hk⟩ :=
      ModInverse.isCorrect.complete (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs hM hcop
    rw [hk] at hr
    simp only [Option.map_some] at hr
    cases r with
    | none => simp at hr
    | some s => exact ⟨s, rfl⟩
  · -- fails exactly
    constructor
    · intro hnone
      rw [hnone] at hr
      have hmodel :
          ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs
            = none := by
        rcases hmod : ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs)
            m.val.natAbs with _ | k
        · rfl
        · rw [hmod] at hr; simp at hr
      by_cases hm : m.val = 0
      · exact Or.inl hm
      · have hM : 0 < m.val.natAbs := Int.natAbs_pos.mpr hm
        rcases (ModInverse.isCorrect.failsExactly _ _).mp hmodel with h0 | hncop
        · exact absurd h0 hM.ne'
        · exact Or.inr fun hgcd => hncop (ModInverse.coprime_reduceSigned hM hgcd)
    · intro hcase
      have hmodel :
          ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs
            = none := by
        apply (ModInverse.isCorrect.failsExactly _ _).mpr
        by_cases hm : m.val = 0
        · exact Or.inl (by simp [hm])
        · have hM : 0 < m.val.natAbs := Int.natAbs_pos.mpr hm
          rcases hcase with h0 | hgcd
          -- `m = 0` was just excluded, so the gcd branch is the live one
          · exact absurd h0 hm
          · refine Or.inr fun hcop => hgcd ?_
            show a.val.natAbs.gcd m.val.natAbs = 1
            rw [← ModInverse.gcd_reduceSigned hM]
            exact hcop
      rw [hmodel] at hr
      simpa using hr

/-- **The extracted `<i8 as ModInverse>::modinverse` is a correct modular inverse over `ℤ`.** -/
theorem modinverse_i8_correct :
    SignedMachineCorrect .I8 I8.Insts.ModinverseModInverse.modinverse :=
  composeSigned modinverse_i8_spec

/-- **The extracted `<i16 as ModInverse>::modinverse` is a correct modular inverse over `ℤ`.** -/
theorem modinverse_i16_correct :
    SignedMachineCorrect .I16 I16.Insts.ModinverseModInverse.modinverse :=
  composeSigned modinverse_i16_spec

/-- **The extracted `<i32 as ModInverse>::modinverse` is a correct modular inverse over `ℤ`.** -/
theorem modinverse_i32_correct :
    SignedMachineCorrect .I32 I32.Insts.ModinverseModInverse.modinverse :=
  composeSigned modinverse_i32_spec

/-- **The extracted `<i64 as ModInverse>::modinverse` is a correct modular inverse over `ℤ`.** -/
theorem modinverse_i64_correct :
    SignedMachineCorrect .I64 I64.Insts.ModinverseModInverse.modinverse :=
  composeSigned modinverse_i64_spec

/-- **The extracted `<i128 as ModInverse>::modinverse` is a correct modular inverse over `ℤ`.** -/
theorem modinverse_i128_correct :
    SignedMachineCorrect .I128 I128.Insts.ModinverseModInverse.modinverse :=
  composeSigned modinverse_i128_spec

end Refinement
