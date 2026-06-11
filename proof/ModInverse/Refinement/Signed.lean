/-
  # Signed refinement: `modinverse_iN` refines the model on the canonicalized input

  The signed `modinverse` for `iN` (extracted as `IN.Insts.ModinverseModInverse.modinverse`)
  returns `none` when `m = 0`; otherwise it canonicalizes `self` to `a_u ∈ [0, |m|)`
  (`ModInverse.reduceSigned`), runs the *unsigned* core on `(a_u, |m|)`, and casts the
  in-range inverse back. Each `modinverse_iN_spec` says the machine never errors and its
  `.val` matches `ModInverse.modinverse (reduceSigned self.val |m|) |m|`, lifted to `ℤ`.

  Everything in the extraction is ordinary code — `|x|` is a cast plus a wrapping negate
  (`0 - x` in the unsigned type) and the cast back is a `match` — so nothing here rests
  on postulates: the absolute-value computation is verified down to the two's-complement
  bit level in the `neg_abs_uN` lemmas.

  **Reading guide.** Each width is `neg_abs_uN` / `nonneg_abs_uN` / `abs_spec_uN` (the
  extracted `|x|` if-expression computes `x.val.natAbs`), `signed_tail_iN` (the shared
  `modinverse_uN` + cast-back tail), and the spec proper. The `i8` group is the template;
  `i16`–`i128` are the same scripts with the width swapped. Read `i8` and skim the rest.
  The single `hcast_val` lemma serves every width.
-/

import ModInverse.Refinement.Unsigned
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

/-- The cast-then-wrapping-negate computation of `|x|`, negative case: at the bit level,
    `0 - (x as u8)` is `-x = |x|` for `x < 0`, with no overflow even at `MIN`. -/
private lemma neg_abs_u8 (x : Std.I8) (hx : x.val < 0) :
    (core.num.U8.wrapping_sub 0#u8 (IScalar.hcast UScalarTy.U8 x)).val = x.val.natAbs := by
  have h1 : (IScalar.hcast UScalarTy.U8 x).val = x.bv.toNat := by
    show (x.bv.signExtend 8).toNat = x.bv.toNat
    rw [BitVec.signExtend_eq_setWidth_of_le _ (Nat.le_refl _), BitVec.setWidth_eq]
  have h2 : (x.bv.toNat : ℤ) = x.val + 2 ^ 8 := by
    have h := BitVec.toInt_eq_toNat_cond x.bv
    have hval : x.val = x.bv.toInt := rfl
    rw [hval] at hx ⊢
    split at h <;> scalar_tac
  simp only [core.num.U8.wrapping_sub_val_eq, h1]
  norm_num [UScalar.size]
  scalar_tac

/-- `|x|` for nonnegative `x` is the plain cast. -/
private lemma nonneg_abs_u8 (x : Std.I8) (hx : 0 ≤ x.val) :
    (IScalar.hcast UScalarTy.U8 x).val = x.val.natAbs := by
  have H := IScalar.hcast_inBounds_spec UScalarTy.U8 x ⟨hx, by scalar_tac⟩
  have h : ((IScalar.hcast UScalarTy.U8 x).val : ℤ) = x.val := by
    simpa [lift, WP.spec_ok] using H
  scalar_tac

/-- Spec for the whole extracted `|x|` if-expression. -/
private lemma abs_spec_u8 (x : Std.I8) :
    (if x < 0#i8 then do
        let i ← lift (IScalar.hcast UScalarTy.U8 x)
        ok (core.num.U8.wrapping_sub 0#u8 i)
      else ok (IScalar.hcast UScalarTy.U8 x))
      ⦃ (r : Std.U8) => r.val = x.val.natAbs ⦄ := by
  split
  · rename_i hneg
    step*
    rw [i_post]
    exact neg_abs_u8 x (by scalar_tac)
  · rename_i hpos
    simp only [WP.spec_ok]
    exact nonneg_abs_u8 x (by scalar_tac)

/-- The shared tail: run `modinverse_u8` on the canonicalized input, then cast the
    witness back through the extracted `match`. -/
private lemma signed_tail_i8 {A : ℤ} (a_u m_abs : Std.U8) (M : ℕ)
    (hM : 0 < M) (hMle : M ≤ 128) (hmabs : m_abs.val = M)
    (hau : a_u.val = ModInverse.reduceSigned A M) :
    (do
      let o ← modinverse_u8 a_u m_abs
      match o with
      | none => ok none
      | some x => do
        let i ← lift (UScalar.hcast IScalarTy.I8 x)
        ok (some i))
      ⦃ (r : Option Std.I8) =>
          r.map (·.val) =
            (ModInverse.modinverse (ModInverse.reduceSigned A M) M).map (Int.ofNat ·) ⦄ := by
  step*
  · -- the core found no inverse
    rename_i hnone
    subst hnone
    rw [hau, hmabs] at o_post
    simp only [Option.map_none] at o_post ⊢
    rw [← o_post]
    simp
  · -- the core found an inverse; cast it back
    rename_i hsome
    subst hsome
    rw [hau, hmabs] at o_post
    simp only [Option.map_some] at o_post
    have hsM : x.val < M := ModInverse.modinverse_lt _ M x.val hM o_post.symm
    have hb : (x.val : ℤ) ≤ IScalar.max IScalarTy.I8 := by scalar_tac
    rw [i_post, ← o_post]
    simp [hcast_val x hb]

@[step]
theorem modinverse_i8_spec (a m : Std.I8) :
    I8.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.I8) =>
      r.map (·.val) =
        (ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs).map
          (Int.ofNat ·) ⦄ := by
  unfold I8.Insts.ModinverseModInverse.modinverse
  step*
  case h1 => simp [ModInverse.modinverse]                      -- m = 0 → none
  step with abs_spec_u8 as ⟨m_abs, m_abs_post⟩
  step with abs_spec_u8 as ⟨s_abs, s_abs_post⟩
  step as ⟨a_abs, a_abs_post⟩
  case hnz => rw [m_abs_post, Int.natAbs_ne_zero]; scalar_tac  -- side goal: |m| ≠ 0
  have hMpos : 0 < (↑m : ℤ).natAbs := Int.natAbs_pos.mpr (by scalar_tac)
  have hMle : (↑m : ℤ).natAbs ≤ 128 :=
    ModInverse.natAbs_le_of_bounds (by scalar_tac) (by scalar_tac)
  have haabs : (↑a_abs : ℕ) = (↑a : ℤ).natAbs % (↑m : ℤ).natAbs := by
    rw [a_abs_post, s_abs_post, m_abs_post]
  split
  · -- a < 0
    split
    · -- |a| % |m| ≠ 0 : a_u = |m| - |a| % |m|
      step as ⟨a_u, a_u_post⟩
      refine signed_tail_i8 a_u m_abs _ hMpos hMle m_abs_post ?_
      rw [a_u_post, m_abs_post, haabs]
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

/-- The cast-then-wrapping-negate computation of `|x|`, negative case: at the bit level,
    `0 - (x as u16)` is `-x = |x|` for `x < 0`, with no overflow even at `MIN`. -/
private lemma neg_abs_u16 (x : Std.I16) (hx : x.val < 0) :
    (core.num.U16.wrapping_sub 0#u16 (IScalar.hcast UScalarTy.U16 x)).val = x.val.natAbs := by
  have h1 : (IScalar.hcast UScalarTy.U16 x).val = x.bv.toNat := by
    show (x.bv.signExtend 16).toNat = x.bv.toNat
    rw [BitVec.signExtend_eq_setWidth_of_le _ (Nat.le_refl _), BitVec.setWidth_eq]
  have h2 : (x.bv.toNat : ℤ) = x.val + 2 ^ 16 := by
    have h := BitVec.toInt_eq_toNat_cond x.bv
    have hval : x.val = x.bv.toInt := rfl
    rw [hval] at hx ⊢
    split at h <;> scalar_tac
  simp only [core.num.U16.wrapping_sub_val_eq, h1]
  norm_num [UScalar.size]
  scalar_tac

/-- `|x|` for nonnegative `x` is the plain cast. -/
private lemma nonneg_abs_u16 (x : Std.I16) (hx : 0 ≤ x.val) :
    (IScalar.hcast UScalarTy.U16 x).val = x.val.natAbs := by
  have H := IScalar.hcast_inBounds_spec UScalarTy.U16 x ⟨hx, by scalar_tac⟩
  have h : ((IScalar.hcast UScalarTy.U16 x).val : ℤ) = x.val := by
    simpa [lift, WP.spec_ok] using H
  scalar_tac

/-- Spec for the whole extracted `|x|` if-expression. -/
private lemma abs_spec_u16 (x : Std.I16) :
    (if x < 0#i16 then do
        let i ← lift (IScalar.hcast UScalarTy.U16 x)
        ok (core.num.U16.wrapping_sub 0#u16 i)
      else ok (IScalar.hcast UScalarTy.U16 x))
      ⦃ (r : Std.U16) => r.val = x.val.natAbs ⦄ := by
  split
  · rename_i hneg
    step*
    rw [i_post]
    exact neg_abs_u16 x (by scalar_tac)
  · rename_i hpos
    simp only [WP.spec_ok]
    exact nonneg_abs_u16 x (by scalar_tac)

/-- The shared tail: run `modinverse_u16` on the canonicalized input, then cast the
    witness back through the extracted `match`. -/
private lemma signed_tail_i16 {A : ℤ} (a_u m_abs : Std.U16) (M : ℕ)
    (hM : 0 < M) (hMle : M ≤ 32768) (hmabs : m_abs.val = M)
    (hau : a_u.val = ModInverse.reduceSigned A M) :
    (do
      let o ← modinverse_u16 a_u m_abs
      match o with
      | none => ok none
      | some x => do
        let i ← lift (UScalar.hcast IScalarTy.I16 x)
        ok (some i))
      ⦃ (r : Option Std.I16) =>
          r.map (·.val) =
            (ModInverse.modinverse (ModInverse.reduceSigned A M) M).map (Int.ofNat ·) ⦄ := by
  step*
  · -- the core found no inverse
    rename_i hnone
    subst hnone
    rw [hau, hmabs] at o_post
    simp only [Option.map_none] at o_post ⊢
    rw [← o_post]
    simp
  · -- the core found an inverse; cast it back
    rename_i hsome
    subst hsome
    rw [hau, hmabs] at o_post
    simp only [Option.map_some] at o_post
    have hsM : x.val < M := ModInverse.modinverse_lt _ M x.val hM o_post.symm
    have hb : (x.val : ℤ) ≤ IScalar.max IScalarTy.I16 := by scalar_tac
    rw [i_post, ← o_post]
    simp [hcast_val x hb]

@[step]
theorem modinverse_i16_spec (a m : Std.I16) :
    I16.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.I16) =>
      r.map (·.val) =
        (ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs).map
          (Int.ofNat ·) ⦄ := by
  unfold I16.Insts.ModinverseModInverse.modinverse
  step*
  case h1 => simp [ModInverse.modinverse]                      -- m = 0 → none
  step with abs_spec_u16 as ⟨m_abs, m_abs_post⟩
  step with abs_spec_u16 as ⟨s_abs, s_abs_post⟩
  step as ⟨a_abs, a_abs_post⟩
  case hnz => rw [m_abs_post, Int.natAbs_ne_zero]; scalar_tac  -- side goal: |m| ≠ 0
  have hMpos : 0 < (↑m : ℤ).natAbs := Int.natAbs_pos.mpr (by scalar_tac)
  have hMle : (↑m : ℤ).natAbs ≤ 32768 :=
    ModInverse.natAbs_le_of_bounds (by scalar_tac) (by scalar_tac)
  have haabs : (↑a_abs : ℕ) = (↑a : ℤ).natAbs % (↑m : ℤ).natAbs := by
    rw [a_abs_post, s_abs_post, m_abs_post]
  split
  · -- a < 0
    split
    · -- |a| % |m| ≠ 0 : a_u = |m| - |a| % |m|
      step as ⟨a_u, a_u_post⟩
      refine signed_tail_i16 a_u m_abs _ hMpos hMle m_abs_post ?_
      rw [a_u_post, m_abs_post, haabs]
      exact ModInverse.reduceSigned_eq_neg_pos hMpos (by scalar_tac) (by rw [← haabs]; scalar_tac)
    · -- |a| % |m| = 0 : a_u = 0
      refine signed_tail_i16 a_abs m_abs _ hMpos hMle m_abs_post ?_
      have hz : (↑a : ℤ).natAbs % (↑m : ℤ).natAbs = 0 := by rw [← haabs]; scalar_tac
      rw [haabs, hz]
      exact ModInverse.reduceSigned_eq_neg_zero hMpos hz
  · -- a ≥ 0 : a_u = |a| % |m|
    refine signed_tail_i16 a_abs m_abs _ hMpos hMle m_abs_post ?_
    rw [haabs]
    exact ModInverse.reduceSigned_eq_nonneg hMpos (by scalar_tac)

/-! ## `i32` (width-copy of `i8`) -/

/-- The cast-then-wrapping-negate computation of `|x|`, negative case: at the bit level,
    `0 - (x as u32)` is `-x = |x|` for `x < 0`, with no overflow even at `MIN`. -/
private lemma neg_abs_u32 (x : Std.I32) (hx : x.val < 0) :
    (core.num.U32.wrapping_sub 0#u32 (IScalar.hcast UScalarTy.U32 x)).val = x.val.natAbs := by
  have h1 : (IScalar.hcast UScalarTy.U32 x).val = x.bv.toNat := by
    show (x.bv.signExtend 32).toNat = x.bv.toNat
    rw [BitVec.signExtend_eq_setWidth_of_le _ (Nat.le_refl _), BitVec.setWidth_eq]
  have h2 : (x.bv.toNat : ℤ) = x.val + 2 ^ 32 := by
    have h := BitVec.toInt_eq_toNat_cond x.bv
    have hval : x.val = x.bv.toInt := rfl
    rw [hval] at hx ⊢
    split at h <;> scalar_tac
  simp only [core.num.U32.wrapping_sub_val_eq, h1]
  norm_num [UScalar.size]
  scalar_tac

/-- `|x|` for nonnegative `x` is the plain cast. -/
private lemma nonneg_abs_u32 (x : Std.I32) (hx : 0 ≤ x.val) :
    (IScalar.hcast UScalarTy.U32 x).val = x.val.natAbs := by
  have H := IScalar.hcast_inBounds_spec UScalarTy.U32 x ⟨hx, by scalar_tac⟩
  have h : ((IScalar.hcast UScalarTy.U32 x).val : ℤ) = x.val := by
    simpa [lift, WP.spec_ok] using H
  scalar_tac

/-- Spec for the whole extracted `|x|` if-expression. -/
private lemma abs_spec_u32 (x : Std.I32) :
    (if x < 0#i32 then do
        let i ← lift (IScalar.hcast UScalarTy.U32 x)
        ok (core.num.U32.wrapping_sub 0#u32 i)
      else ok (IScalar.hcast UScalarTy.U32 x))
      ⦃ (r : Std.U32) => r.val = x.val.natAbs ⦄ := by
  split
  · rename_i hneg
    step*
    rw [i_post]
    exact neg_abs_u32 x (by scalar_tac)
  · rename_i hpos
    simp only [WP.spec_ok]
    exact nonneg_abs_u32 x (by scalar_tac)

/-- The shared tail: run `modinverse_u32` on the canonicalized input, then cast the
    witness back through the extracted `match`. -/
private lemma signed_tail_i32 {A : ℤ} (a_u m_abs : Std.U32) (M : ℕ)
    (hM : 0 < M) (hMle : M ≤ 2147483648) (hmabs : m_abs.val = M)
    (hau : a_u.val = ModInverse.reduceSigned A M) :
    (do
      let o ← modinverse_u32 a_u m_abs
      match o with
      | none => ok none
      | some x => do
        let i ← lift (UScalar.hcast IScalarTy.I32 x)
        ok (some i))
      ⦃ (r : Option Std.I32) =>
          r.map (·.val) =
            (ModInverse.modinverse (ModInverse.reduceSigned A M) M).map (Int.ofNat ·) ⦄ := by
  step*
  · -- the core found no inverse
    rename_i hnone
    subst hnone
    rw [hau, hmabs] at o_post
    simp only [Option.map_none] at o_post ⊢
    rw [← o_post]
    simp
  · -- the core found an inverse; cast it back
    rename_i hsome
    subst hsome
    rw [hau, hmabs] at o_post
    simp only [Option.map_some] at o_post
    have hsM : x.val < M := ModInverse.modinverse_lt _ M x.val hM o_post.symm
    have hb : (x.val : ℤ) ≤ IScalar.max IScalarTy.I32 := by scalar_tac
    rw [i_post, ← o_post]
    simp [hcast_val x hb]

@[step]
theorem modinverse_i32_spec (a m : Std.I32) :
    I32.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.I32) =>
      r.map (·.val) =
        (ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs).map
          (Int.ofNat ·) ⦄ := by
  unfold I32.Insts.ModinverseModInverse.modinverse
  step*
  case h1 => simp [ModInverse.modinverse]                      -- m = 0 → none
  step with abs_spec_u32 as ⟨m_abs, m_abs_post⟩
  step with abs_spec_u32 as ⟨s_abs, s_abs_post⟩
  step as ⟨a_abs, a_abs_post⟩
  case hnz => rw [m_abs_post, Int.natAbs_ne_zero]; scalar_tac  -- side goal: |m| ≠ 0
  have hMpos : 0 < (↑m : ℤ).natAbs := Int.natAbs_pos.mpr (by scalar_tac)
  have hMle : (↑m : ℤ).natAbs ≤ 2147483648 :=
    ModInverse.natAbs_le_of_bounds (by scalar_tac) (by scalar_tac)
  have haabs : (↑a_abs : ℕ) = (↑a : ℤ).natAbs % (↑m : ℤ).natAbs := by
    rw [a_abs_post, s_abs_post, m_abs_post]
  split
  · -- a < 0
    split
    · -- |a| % |m| ≠ 0 : a_u = |m| - |a| % |m|
      step as ⟨a_u, a_u_post⟩
      refine signed_tail_i32 a_u m_abs _ hMpos hMle m_abs_post ?_
      rw [a_u_post, m_abs_post, haabs]
      exact ModInverse.reduceSigned_eq_neg_pos hMpos (by scalar_tac) (by rw [← haabs]; scalar_tac)
    · -- |a| % |m| = 0 : a_u = 0
      refine signed_tail_i32 a_abs m_abs _ hMpos hMle m_abs_post ?_
      have hz : (↑a : ℤ).natAbs % (↑m : ℤ).natAbs = 0 := by rw [← haabs]; scalar_tac
      rw [haabs, hz]
      exact ModInverse.reduceSigned_eq_neg_zero hMpos hz
  · -- a ≥ 0 : a_u = |a| % |m|
    refine signed_tail_i32 a_abs m_abs _ hMpos hMle m_abs_post ?_
    rw [haabs]
    exact ModInverse.reduceSigned_eq_nonneg hMpos (by scalar_tac)

/-! ## `i64` (width-copy of `i8`) -/

/-- The cast-then-wrapping-negate computation of `|x|`, negative case: at the bit level,
    `0 - (x as u64)` is `-x = |x|` for `x < 0`, with no overflow even at `MIN`. -/
private lemma neg_abs_u64 (x : Std.I64) (hx : x.val < 0) :
    (core.num.U64.wrapping_sub 0#u64 (IScalar.hcast UScalarTy.U64 x)).val = x.val.natAbs := by
  have h1 : (IScalar.hcast UScalarTy.U64 x).val = x.bv.toNat := by
    show (x.bv.signExtend 64).toNat = x.bv.toNat
    rw [BitVec.signExtend_eq_setWidth_of_le _ (Nat.le_refl _), BitVec.setWidth_eq]
  have h2 : (x.bv.toNat : ℤ) = x.val + 2 ^ 64 := by
    have h := BitVec.toInt_eq_toNat_cond x.bv
    have hval : x.val = x.bv.toInt := rfl
    rw [hval] at hx ⊢
    split at h <;> scalar_tac
  simp only [core.num.U64.wrapping_sub_val_eq, h1]
  norm_num [UScalar.size]
  scalar_tac

/-- `|x|` for nonnegative `x` is the plain cast. -/
private lemma nonneg_abs_u64 (x : Std.I64) (hx : 0 ≤ x.val) :
    (IScalar.hcast UScalarTy.U64 x).val = x.val.natAbs := by
  have H := IScalar.hcast_inBounds_spec UScalarTy.U64 x ⟨hx, by scalar_tac⟩
  have h : ((IScalar.hcast UScalarTy.U64 x).val : ℤ) = x.val := by
    simpa [lift, WP.spec_ok] using H
  scalar_tac

/-- Spec for the whole extracted `|x|` if-expression. -/
private lemma abs_spec_u64 (x : Std.I64) :
    (if x < 0#i64 then do
        let i ← lift (IScalar.hcast UScalarTy.U64 x)
        ok (core.num.U64.wrapping_sub 0#u64 i)
      else ok (IScalar.hcast UScalarTy.U64 x))
      ⦃ (r : Std.U64) => r.val = x.val.natAbs ⦄ := by
  split
  · rename_i hneg
    step*
    rw [i_post]
    exact neg_abs_u64 x (by scalar_tac)
  · rename_i hpos
    simp only [WP.spec_ok]
    exact nonneg_abs_u64 x (by scalar_tac)

/-- The shared tail: run `modinverse_u64` on the canonicalized input, then cast the
    witness back through the extracted `match`. -/
private lemma signed_tail_i64 {A : ℤ} (a_u m_abs : Std.U64) (M : ℕ)
    (hM : 0 < M) (hMle : M ≤ 9223372036854775808) (hmabs : m_abs.val = M)
    (hau : a_u.val = ModInverse.reduceSigned A M) :
    (do
      let o ← modinverse_u64 a_u m_abs
      match o with
      | none => ok none
      | some x => do
        let i ← lift (UScalar.hcast IScalarTy.I64 x)
        ok (some i))
      ⦃ (r : Option Std.I64) =>
          r.map (·.val) =
            (ModInverse.modinverse (ModInverse.reduceSigned A M) M).map (Int.ofNat ·) ⦄ := by
  step*
  · -- the core found no inverse
    rename_i hnone
    subst hnone
    rw [hau, hmabs] at o_post
    simp only [Option.map_none] at o_post ⊢
    rw [← o_post]
    simp
  · -- the core found an inverse; cast it back
    rename_i hsome
    subst hsome
    rw [hau, hmabs] at o_post
    simp only [Option.map_some] at o_post
    have hsM : x.val < M := ModInverse.modinverse_lt _ M x.val hM o_post.symm
    have hb : (x.val : ℤ) ≤ IScalar.max IScalarTy.I64 := by scalar_tac
    rw [i_post, ← o_post]
    simp [hcast_val x hb]

@[step]
theorem modinverse_i64_spec (a m : Std.I64) :
    I64.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.I64) =>
      r.map (·.val) =
        (ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs).map
          (Int.ofNat ·) ⦄ := by
  unfold I64.Insts.ModinverseModInverse.modinverse
  step*
  case h1 => simp [ModInverse.modinverse]                      -- m = 0 → none
  step with abs_spec_u64 as ⟨m_abs, m_abs_post⟩
  step with abs_spec_u64 as ⟨s_abs, s_abs_post⟩
  step as ⟨a_abs, a_abs_post⟩
  case hnz => rw [m_abs_post, Int.natAbs_ne_zero]; scalar_tac  -- side goal: |m| ≠ 0
  have hMpos : 0 < (↑m : ℤ).natAbs := Int.natAbs_pos.mpr (by scalar_tac)
  have hMle : (↑m : ℤ).natAbs ≤ 9223372036854775808 :=
    ModInverse.natAbs_le_of_bounds (by scalar_tac) (by scalar_tac)
  have haabs : (↑a_abs : ℕ) = (↑a : ℤ).natAbs % (↑m : ℤ).natAbs := by
    rw [a_abs_post, s_abs_post, m_abs_post]
  split
  · -- a < 0
    split
    · -- |a| % |m| ≠ 0 : a_u = |m| - |a| % |m|
      step as ⟨a_u, a_u_post⟩
      refine signed_tail_i64 a_u m_abs _ hMpos hMle m_abs_post ?_
      rw [a_u_post, m_abs_post, haabs]
      exact ModInverse.reduceSigned_eq_neg_pos hMpos (by scalar_tac) (by rw [← haabs]; scalar_tac)
    · -- |a| % |m| = 0 : a_u = 0
      refine signed_tail_i64 a_abs m_abs _ hMpos hMle m_abs_post ?_
      have hz : (↑a : ℤ).natAbs % (↑m : ℤ).natAbs = 0 := by rw [← haabs]; scalar_tac
      rw [haabs, hz]
      exact ModInverse.reduceSigned_eq_neg_zero hMpos hz
  · -- a ≥ 0 : a_u = |a| % |m|
    refine signed_tail_i64 a_abs m_abs _ hMpos hMle m_abs_post ?_
    rw [haabs]
    exact ModInverse.reduceSigned_eq_nonneg hMpos (by scalar_tac)

/-! ## `i128` (width-copy of `i8`) -/

/-- The cast-then-wrapping-negate computation of `|x|`, negative case: at the bit level,
    `0 - (x as u128)` is `-x = |x|` for `x < 0`, with no overflow even at `MIN`. -/
private lemma neg_abs_u128 (x : Std.I128) (hx : x.val < 0) :
    (core.num.U128.wrapping_sub 0#u128 (IScalar.hcast UScalarTy.U128 x)).val = x.val.natAbs := by
  have h1 : (IScalar.hcast UScalarTy.U128 x).val = x.bv.toNat := by
    show (x.bv.signExtend 128).toNat = x.bv.toNat
    rw [BitVec.signExtend_eq_setWidth_of_le _ (Nat.le_refl _), BitVec.setWidth_eq]
  have h2 : (x.bv.toNat : ℤ) = x.val + 2 ^ 128 := by
    have h := BitVec.toInt_eq_toNat_cond x.bv
    have hval : x.val = x.bv.toInt := rfl
    rw [hval] at hx ⊢
    split at h <;> scalar_tac
  simp only [core.num.U128.wrapping_sub_val_eq, h1]
  norm_num [UScalar.size]
  scalar_tac

/-- `|x|` for nonnegative `x` is the plain cast. -/
private lemma nonneg_abs_u128 (x : Std.I128) (hx : 0 ≤ x.val) :
    (IScalar.hcast UScalarTy.U128 x).val = x.val.natAbs := by
  have H := IScalar.hcast_inBounds_spec UScalarTy.U128 x ⟨hx, by scalar_tac⟩
  have h : ((IScalar.hcast UScalarTy.U128 x).val : ℤ) = x.val := by
    simpa [lift, WP.spec_ok] using H
  scalar_tac

/-- Spec for the whole extracted `|x|` if-expression. -/
private lemma abs_spec_u128 (x : Std.I128) :
    (if x < 0#i128 then do
        let i ← lift (IScalar.hcast UScalarTy.U128 x)
        ok (core.num.U128.wrapping_sub 0#u128 i)
      else ok (IScalar.hcast UScalarTy.U128 x))
      ⦃ (r : Std.U128) => r.val = x.val.natAbs ⦄ := by
  split
  · rename_i hneg
    step*
    rw [i_post]
    exact neg_abs_u128 x (by scalar_tac)
  · rename_i hpos
    simp only [WP.spec_ok]
    exact nonneg_abs_u128 x (by scalar_tac)

/-- The shared tail: run `modinverse_u128` on the canonicalized input, then cast the
    witness back through the extracted `match`. -/
private lemma signed_tail_i128 {A : ℤ} (a_u m_abs : Std.U128) (M : ℕ)
    (hM : 0 < M) (hMle : M ≤ 170141183460469231731687303715884105728) (hmabs : m_abs.val = M)
    (hau : a_u.val = ModInverse.reduceSigned A M) :
    (do
      let o ← modinverse_u128 a_u m_abs
      match o with
      | none => ok none
      | some x => do
        let i ← lift (UScalar.hcast IScalarTy.I128 x)
        ok (some i))
      ⦃ (r : Option Std.I128) =>
          r.map (·.val) =
            (ModInverse.modinverse (ModInverse.reduceSigned A M) M).map (Int.ofNat ·) ⦄ := by
  step*
  · -- the core found no inverse
    rename_i hnone
    subst hnone
    rw [hau, hmabs] at o_post
    simp only [Option.map_none] at o_post ⊢
    rw [← o_post]
    simp
  · -- the core found an inverse; cast it back
    rename_i hsome
    subst hsome
    rw [hau, hmabs] at o_post
    simp only [Option.map_some] at o_post
    have hsM : x.val < M := ModInverse.modinverse_lt _ M x.val hM o_post.symm
    have hb : (x.val : ℤ) ≤ IScalar.max IScalarTy.I128 := by scalar_tac
    rw [i_post, ← o_post]
    simp [hcast_val x hb]

@[step]
theorem modinverse_i128_spec (a m : Std.I128) :
    I128.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.I128) =>
      r.map (·.val) =
        (ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs).map
          (Int.ofNat ·) ⦄ := by
  unfold I128.Insts.ModinverseModInverse.modinverse
  step*
  case h1 => simp [ModInverse.modinverse]                      -- m = 0 → none
  step with abs_spec_u128 as ⟨m_abs, m_abs_post⟩
  step with abs_spec_u128 as ⟨s_abs, s_abs_post⟩
  step as ⟨a_abs, a_abs_post⟩
  case hnz => rw [m_abs_post, Int.natAbs_ne_zero]; scalar_tac  -- side goal: |m| ≠ 0
  have hMpos : 0 < (↑m : ℤ).natAbs := Int.natAbs_pos.mpr (by scalar_tac)
  have hMle : (↑m : ℤ).natAbs ≤ 170141183460469231731687303715884105728 :=
    ModInverse.natAbs_le_of_bounds (by scalar_tac) (by scalar_tac)
  have haabs : (↑a_abs : ℕ) = (↑a : ℤ).natAbs % (↑m : ℤ).natAbs := by
    rw [a_abs_post, s_abs_post, m_abs_post]
  split
  · -- a < 0
    split
    · -- |a| % |m| ≠ 0 : a_u = |m| - |a| % |m|
      step as ⟨a_u, a_u_post⟩
      refine signed_tail_i128 a_u m_abs _ hMpos hMle m_abs_post ?_
      rw [a_u_post, m_abs_post, haabs]
      exact ModInverse.reduceSigned_eq_neg_pos hMpos (by scalar_tac) (by rw [← haabs]; scalar_tac)
    · -- |a| % |m| = 0 : a_u = 0
      refine signed_tail_i128 a_abs m_abs _ hMpos hMle m_abs_post ?_
      have hz : (↑a : ℤ).natAbs % (↑m : ℤ).natAbs = 0 := by rw [← haabs]; scalar_tac
      rw [haabs, hz]
      exact ModInverse.reduceSigned_eq_neg_zero hMpos hz
  · -- a ≥ 0 : a_u = |a| % |m|
    refine signed_tail_i128 a_abs m_abs _ hMpos hMle m_abs_post ?_
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
