/-
  # Egcd refinement: the extracted `egcd_u64` refines the ℕ model

  `egcd_u64` runs the same per-step-reduced loop as `modinverse_u64` (so
  `egcd_u64_loop.spec` is a verbatim copy of that loop's refinement), then derives
  the exact Bézout cofactor `y = (g - a*x) / b` with one `u128` widening. The
  interesting machine obligations are all about that tail: the widening product
  fits, the subtraction can't underflow (`g ∣ a` and `x ≥ 1` give `a*x ≥ g`), the
  division is exact (the loop invariant *is* the divisibility), and the results
  cast into `i128` losslessly.

  `egcd_u64.spec` value-matches `ModInverse.egcd`; composed with
  `ModInverse.isEgcdCorrect` it yields the certificate `egcd_u64_correct`, stated
  with no reference to the model.
-/

import ModInverse.Refinement.Helpers
import ModInverse.Proofs

open Aeneas Aeneas.Std Result
open modinverse

namespace Refinement

/-- Loop refinement: verbatim copy of `modinverse_u64_loop.spec` (the loop bodies
    are identical; only the surrounding function differs). -/
@[step]
theorem egcd_u64_loop.spec (m r r_next s s_next : Std.U64)
    (hm : 0 < m.val) (hs : s.val < m.val) (hsn : s_next.val < m.val) :
    egcd_u64_loop m r r_next s s_next ⦃ (res : Std.U64 × Std.U64) =>
      (res.1.val, res.2.val)
        = ModInverse.loop hm ⟨r.val, r_next.val, s.val, s_next.val, hs, hsn⟩ ⦄ := by
  unfold egcd_u64_loop
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

/-- Unsigned widening casts preserve `.val` (u64 → u128 is always in bounds). -/
private lemma ucast_128_val (x : Std.U64) :
    (UScalar.cast UScalarTy.U128 x).val = x.val := by
  simp

/-- The unsigned→signed cast back preserves value below `i128::MAX`. -/
private lemma hcast_i128_val {src : UScalarTy} (s : UScalar src)
    (h : (s.val : ℤ) ≤ IScalar.max IScalarTy.I128) :
    (UScalar.hcast IScalarTy.I128 s).val = (s.val : ℤ) := by
  have H := UScalar.hcast_inBounds_spec IScalarTy.I128 s (by simpa using h)
  simpa [lift, WP.spec_ok] using H

/-- **Top-level refinement for `egcd_u64`:** never errors and value-matches the
    model componentwise. -/
@[step]
theorem egcd_u64.spec (a b : Std.U64) :
    egcd_u64 a b ⦃ (res : Std.U64 × Std.I128 × Std.I128) =>
      res.1.val = (ModInverse.egcd a.val b.val).1 ∧
      (res.2.1.val : ℤ) = (ModInverse.egcd a.val b.val).2.1 ∧
      (res.2.2.val : ℤ) = (ModInverse.egcd a.val b.val).2.2 ⦄ := by
  unfold egcd_u64
  step*
  · -- b = 0
    simp [ModInverse.egcd]
  · -- b = 1
    simp [ModInverse.egcd]
  · -- s = 0: the certificate is (g, 0, 1), and g = b because b divides it
    rename_i hs0
    subst hs0
    have hb : 1 < b.val := by scalar_tac
    rw [r_next_post] at r_post
    have hr1 : r.val =
        (ModInverse.loop (m := b.val) (by scalar_tac)
          ⟨b.val, a.val % b.val, 0, 1, by scalar_tac, hb⟩).1 := congrArg Prod.fst r_post
    have hs1 : (0 : ℕ) =
        (ModInverse.loop (m := b.val) (by scalar_tac)
          ⟨b.val, a.val % b.val, 0, 1, by scalar_tac, hb⟩).2 := by
      have := congrArg Prod.snd r_post
      simpa using this
    have hgcd := ModInverse.loop_fst_eq_gcd_init (a := a.val) hb
    have hdvd := ModInverse.egcd_loop_dvd a.val b.val hb
    simp only [← hr1, ← hs1, Nat.cast_zero, mul_zero, sub_zero] at hdvd
    have hbdvd : b.val ∣ r.val := by exact_mod_cast hdvd
    have hpb : r.val = b.val :=
      Nat.dvd_antisymm (by rw [hr1, hgcd]; exact Nat.gcd_dvd_right _ _) hbdvd
    rw [ModInverse.egcd_loop_eq a.val b.val hb]
    dsimp only
    refine ⟨hr1, by rw [← hs1]; rfl, ?_⟩
    rw [← hr1, ← hs1, hpb]
    simp only [Nat.cast_zero, mul_zero, sub_zero]
    rw [Int.ediv_self (by exact_mod_cast (Nat.zero_lt_of_lt hb).ne')]
    rfl
  · -- side goal: the subtraction a*s - g can't underflow (g ∣ a and s ≥ 1)
    have hb : 1 < b.val := by scalar_tac
    rw [r_next_post] at r_post
    have hr1 : r.val =
        (ModInverse.loop (m := b.val) (by scalar_tac)
          ⟨b.val, a.val % b.val, 0, 1, by scalar_tac, hb⟩).1 := congrArg Prod.fst r_post
    have hs1 : s.val =
        (ModInverse.loop (m := b.val) (by scalar_tac)
          ⟨b.val, a.val % b.val, 0, 1, by scalar_tac, hb⟩).2 := congrArg Prod.snd r_post
    have hgcd := ModInverse.loop_fst_eq_gcd_init (a := a.val) hb
    have hsne : s.val ≠ 0 := by scalar_tac
    have hane : a.val ≠ 0 := by
      intro ha0
      apply hsne
      rw [hs1, ha0, Nat.zero_mod]
      rw [ModInverse.loop, dif_pos rfl]
    have hra : r.val ≤ a.val := by
      rw [hr1, hgcd]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hane) (Nat.gcd_dvd_left _ _)
    have : r.val ≤ a.val * s.val :=
      le_trans hra (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hsne))
    simp only [i_post, i1_post, i2_post, i3_post, ucast_128_val]
    exact this
  · -- side goal: the negation can't hit i128::MIN (the value is small and nonnegative)
    have hb : 1 < b.val := by scalar_tac
    rw [r_next_post] at r_post
    have hs1 : s.val =
        (ModInverse.loop (m := b.val) (by scalar_tac)
          ⟨b.val, a.val % b.val, 0, 1, by scalar_tac, hb⟩).2 := congrArg Prod.snd r_post
    have hslt : s.val < b.val := by
      rw [hs1]; exact ModInverse.loop_snd_lt _ _
    have h6 : i6.val < 2 ^ 64 := by
      rw [i6_post, i5_post, ucast_128_val]
      apply Nat.div_lt_of_lt_mul
      calc num.val ≤ i2.val := by scalar_tac
        _ = a.val * s.val := by
            rw [i2_post, i_post, i1_post]; simp only [ucast_128_val]
        _ < 2 ^ 64 * b.val := Nat.mul_lt_mul'' (by scalar_tac) hslt
        _ = b.val * 2 ^ 64 := Nat.mul_comm _ _
    have h7 : i7.val = (i6.val : ℤ) := by
      rw [i7_post]; exact hcast_i128_val i6 (by scalar_tac)
    scalar_tac
  · -- the main certificate: componentwise match against the model
    have hb : 1 < b.val := by scalar_tac
    rw [r_next_post] at r_post
    have hr1 : r.val =
        (ModInverse.loop (m := b.val) (by scalar_tac)
          ⟨b.val, a.val % b.val, 0, 1, by scalar_tac, hb⟩).1 := congrArg Prod.fst r_post
    have hs1 : s.val =
        (ModInverse.loop (m := b.val) (by scalar_tac)
          ⟨b.val, a.val % b.val, 0, 1, by scalar_tac, hb⟩).2 := congrArg Prod.snd r_post
    have hgcd := ModInverse.loop_fst_eq_gcd_init (a := a.val) hb
    have hsne : s.val ≠ 0 := by scalar_tac
    have hane : a.val ≠ 0 := by
      intro ha0
      apply hsne
      rw [hs1, ha0, Nat.zero_mod]
      rw [ModInverse.loop, dif_pos rfl]
    have hslt : s.val < b.val := by
      rw [hs1]; exact ModInverse.loop_snd_lt _ _
    have hga : r.val ≤ a.val * s.val := by
      have h1 : r.val ≤ a.val := by
        rw [hr1, hgcd]
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero hane) (Nat.gcd_dvd_left _ _)
      exact le_trans h1 (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hsne))
    -- machine values of the tail computation
    have hnum : num.val = a.val * s.val - r.val := by
      rw [num_post1, i2_post, i_post, i1_post, i3_post]
      simp only [ucast_128_val]
    have h6 : i6.val < 2 ^ 64 := by
      rw [i6_post, i5_post, ucast_128_val]
      apply Nat.div_lt_of_lt_mul
      calc num.val ≤ i2.val := by scalar_tac
        _ = a.val * s.val := by
            rw [i2_post, i_post, i1_post]; simp only [ucast_128_val]
        _ < 2 ^ 64 * b.val := Nat.mul_lt_mul'' (by scalar_tac) hslt
        _ = b.val * 2 ^ 64 := Nat.mul_comm _ _
    -- the loop's congruence gives the exact divisibility
    have hdvd := ModInverse.egcd_loop_dvd a.val b.val hb
    simp only [← hr1, ← hs1] at hdvd
    have hk' : (b.val : ℤ) ∣ (a.val : ℤ) * s.val - r.val := by
      have h := (dvd_neg (α := ℤ)).mpr hdvd
      rw [neg_sub] at h
      exact h
    obtain ⟨k, hk⟩ := hk'
    have hk0 : 0 ≤ k := by
      by_contra hltk
      push Not at hltk
      have hbpos : (0 : ℤ) < (b.val : ℤ) := by exact_mod_cast (by scalar_tac : 0 < b.val)
      have hneg : (b.val : ℤ) * k < 0 := mul_neg_of_pos_of_neg hbpos hltk
      rw [← hk] at hneg
      have hge : (0 : ℤ) ≤ (a.val : ℤ) * s.val - r.val := by
        have h2 : (r.val : ℤ) ≤ (a.val : ℤ) * s.val := by exact_mod_cast hga
        exact sub_nonneg.mpr h2
      exact absurd hneg (not_lt.mpr hge)
    have hNk : a.val * s.val - r.val = b.val * k.toNat := by
      have hkk : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
      have hcast : ((a.val * s.val - r.val : ℕ) : ℤ) = ((b.val * k.toNat : ℕ) : ℤ) := by
        rw [Nat.cast_sub hga]
        push_cast
        rw [hkk]
        exact hk
      exact_mod_cast hcast
    have hdiv : num.val / i5.val = k.toNat := by
      rw [hnum, i5_post, ucast_128_val, hNk]
      exact Nat.mul_div_cancel_left _ (by scalar_tac)
    -- assemble the three components
    rw [ModInverse.egcd_loop_eq a.val b.val hb]
    dsimp only
    refine ⟨hr1, ?_, ?_⟩
    · rw [i4_post, hcast_i128_val s (by scalar_tac)]
      exact_mod_cast hs1
    · rw [i8_post, i7_post, hcast_i128_val i6 (by scalar_tac), i6_post, hdiv,
        Int.toNat_of_nonneg hk0, ← hr1, ← hs1]
      have hrz : (r.val : ℤ) - (a.val : ℤ) * s.val = (b.val : ℤ) * (-k) := by
        linear_combination -hk
      rw [hrz, Int.mul_ediv_cancel_left _ (by exact_mod_cast (by scalar_tac : b.val ≠ 0))]

/-- **The extracted `egcd_u64` is a correct extended gcd**: the first component is
    `gcd a b`, the coefficients certify it exactly over `ℤ`, and `x` is the
    canonical coefficient in `[0, b)`. -/
theorem egcd_u64_correct (a b : Std.U64) :
    egcd_u64 a b ⦃ (res : Std.U64 × Std.I128 × Std.I128) =>
      res.1.val = Nat.gcd a.val b.val ∧
      (a.val : ℤ) * res.2.1.val + (b.val : ℤ) * res.2.2.val = (res.1.val : ℤ) ∧
      (0 < b.val → 0 ≤ res.2.1.val ∧ res.2.1.val < (b.val : ℤ)) ⦄ := by
  apply WP.spec_mono (egcd_u64.spec a b)
  intro res hres
  obtain ⟨h1, h2, h3⟩ := hres
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, ModInverse.isEgcdCorrect.gcd_eq]
  · rw [h2, h3, h1]
    exact ModInverse.isEgcdCorrect.bezout a.val b.val
  · intro hb
    rw [h2]
    exact ModInverse.isEgcdCorrect.xCanonical a.val b.val hb

end Refinement
