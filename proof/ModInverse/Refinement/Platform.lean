/-
  # Platform refinement: `usize` / `isize` dispatch to the 64-bit width

  On every supported target (`System.Platform.numBits ∈ {32, 64}`) `usize`/`isize`
  fit in `u64`/`i64`, so the impls cast to the 64-bit type, run that width's
  `modinverse`, and rebuild the result with a `match`, casting back. Both casts
  preserve `.val` (the value-preservation uses `numBits ≤ 64`); nothing here rests
  on postulates.

    * `usize` uses the unsigned `u64` core directly (so its spec is ℕ-valued, like the
      unsigned widths).
    * `isize` reuses the signed `i64` refinement (so its spec is ℤ-valued, like the
      signed widths, on the canonicalized input).
-/

import ModInverse.Refinement.Signed

open Aeneas Aeneas.Std Result
open modinverse

namespace Refinement

private lemma numBits_le_64 : System.Platform.numBits ≤ 64 := by
  cases System.Platform.numBits_eq <;> simp [*]

/-! ## `usize` (dispatches to the unsigned `u64` core) -/

private lemma ucast_usize_val (a : Std.Usize) : (UScalar.cast .U64 a).val = a.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq .U64 a
    (by simp)

private lemma cast_back_usize_val {s : Std.U64} (h : s.val < 2 ^ System.Platform.numBits) :
    (UScalar.cast .Usize s).val = s.val :=
  UScalar.cast_val_mod_pow_of_inBounds_eq .Usize s (by simpa [Usize.numBits] using h)

@[step]
theorem modinverse_usize_spec (a m : Std.Usize) :
    Usize.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.Usize) =>
      r.map (·.val) = ModInverse.modinverse a.val m.val ⦄ := by
  unfold Usize.Insts.ModinverseModInverse.modinverse U64.Insts.ModinverseModInverse.modinverse
  step*
  · -- the core found no inverse
    rename_i hnone
    subst hnone
    rw [i_post, i1_post, ucast_usize_val, ucast_usize_val] at o_post
    simpa using o_post
  · -- the core found an inverse; cast it back
    rename_i hsome
    subst hsome
    rw [i_post, i1_post, ucast_usize_val, ucast_usize_val] at o_post
    simp only [Option.map_some] at o_post
    have hm0 : 0 < m.val := by
      by_contra h
      rw [show m.val = 0 by scalar_tac] at o_post
      simp [ModInverse.modinverse] at o_post
    have hsM : x.val < m.val := ModInverse.modinverse_lt _ m.val x.val hm0 o_post.symm
    have hb : x.val < 2 ^ System.Platform.numBits := by scalar_tac
    rw [i2_post, ← o_post]
    simp [cast_back_usize_val hb]

/-! ## `isize` (dispatches to the signed `i64` refinement) -/

private lemma icast_isize_val (a : Std.Isize) : (IScalar.cast .I64 a).val = a.val :=
  IScalar.val_mod_pow_greater_numBits .I64 a
    (by simp)

private lemma cast_back_isize_val {s : Std.I64} (h0 : 0 ≤ s.val)
    (h1 : s.val < 2 ^ (System.Platform.numBits - 1)) :
    (IScalar.cast .Isize s).val = s.val := by
  apply IScalar.val_mod_pow_inBounds .Isize s
  · exact (neg_nonpos.mpr (by positivity)).trans h0
  · exact h1

@[step]
theorem modinverse_isize_spec (a m : Std.Isize) :
    Isize.Insts.ModinverseModInverse.modinverse a m ⦃ (r : Option Std.Isize) =>
      r.map (·.val) =
        (ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs).map
          (Int.ofNat ·) ⦄ := by
  unfold Isize.Insts.ModinverseModInverse.modinverse
  step*
  · -- the i64 path found no inverse
    rename_i hnone
    subst hnone
    rw [i_post, i1_post, icast_isize_val, icast_isize_val] at o_post
    simpa using o_post
  · -- the i64 path found an inverse; cast it back
    rename_i hsome
    subst hsome
    rw [i_post, i1_post, icast_isize_val, icast_isize_val] at o_post
    rcases hmod : ModInverse.modinverse (ModInverse.reduceSigned a.val m.val.natAbs) m.val.natAbs
      with _ | k
    · rw [hmod] at o_post; simp at o_post
    · rw [hmod] at o_post
      simp only [Option.map_some] at o_post
      have hsk : x.val = (k : ℤ) := by simpa using o_post
      have hm0 : 0 < m.val.natAbs := by
        by_contra h
        rw [show m.val.natAbs = 0 by scalar_tac] at hmod
        simp [ModInverse.modinverse] at hmod
      have hkM : k < m.val.natAbs := ModInverse.modinverse_lt _ _ k hm0 hmod
      have h0 : 0 ≤ x.val := by rw [hsk]; positivity
      have hmin : Isize.min = -2 ^ (System.Platform.numBits - 1) := Isize.cMin_bound.2
      have hmax : Isize.max + 1 = 2 ^ (System.Platform.numBits - 1) := Isize.cMax_bound.2
      have hMabs : (m.val.natAbs : ℤ) ≤ 2 ^ (System.Platform.numBits - 1) := by scalar_tac
      have hk : (k : ℤ) < (m.val.natAbs : ℤ) := by exact_mod_cast hkM
      have h1 : x.val < 2 ^ (System.Platform.numBits - 1) := by rw [hsk]; scalar_tac
      rw [i2_post]
      simp [cast_back_isize_val h0 h1, hsk]

/-! ## End-to-end correctness of the extracted platform-width machine code

  Same composition as the fixed widths: `usize` instantiates the unsigned
  composition lemma, `isize` the signed one. -/

/-- **The extracted `<usize as ModInverse>::modinverse` is a correct modular inverse.** -/
theorem modinverse_usize_correct :
    UnsignedMachineCorrect .Usize Usize.Insts.ModinverseModInverse.modinverse :=
  composeUnsigned modinverse_usize_spec

/-- **The extracted `<isize as ModInverse>::modinverse` is a correct modular inverse over `ℤ`.** -/
theorem modinverse_isize_correct :
    SignedMachineCorrect .Isize Isize.Insts.ModinverseModInverse.modinverse :=
  composeSigned modinverse_isize_spec

end Refinement
