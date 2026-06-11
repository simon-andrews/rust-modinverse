/-
  # Signed canonicalization model and arithmetic bridges

  The signed `modinverse` impls (`i8`–`i128`) compute, for `m ≠ 0`,

      a_u = if self < 0 ∧ |self| % |m| ≠ 0 then |m| - |self| % |m| else |self| % |m|

  then call the unsigned core on `(a_u, |m|)` and cast the result back. `a_u` is
  the canonical representative of `self` in `[0, |m|)`. This file defines that
  canonical value `reduceSigned` over `ℤ`, and proves the three branch identities
  the refinement needs (`a_u.val = reduceSigned self.val |m|`), plus the order/
  congruence facts used to derive integer-level correctness.

  Plain `ℕ`/`ℤ` reasoning (Mathlib): this is not an Aeneas refinement file, so the
  Aeneas tactic discipline does not apply here.
-/
import ModInverse
import ModInverse.Proofs
import Mathlib.Tactic

namespace ModInverse

/-- The canonical representative of `a` in `[0, M)` (with `M = |m|`), i.e. the
    reduced input the signed wrappers feed to the unsigned core. -/
def reduceSigned (a : ℤ) (M : ℕ) : ℕ := (a % (M : ℤ)).toNat

/-- `|a| ≤ n` follows from two-sided bounds; used to bound `|m|` by the width. -/
lemma natAbs_le_of_bounds {a : ℤ} {n : ℕ} (h1 : -(n : ℤ) ≤ a) (h2 : a ≤ n) :
    a.natAbs ≤ n := by omega

/-- Two residues below the modulus that are congruent are equal. -/
lemma eq_of_lt_of_modEq {x y M : ℕ} (hx : x < M) (hy : y < M)
    (h : (x : ℤ) ≡ (y : ℤ) [ZMOD M]) : x = y := by
  have h2 : (x : ℤ) % M = (y : ℤ) % M := h
  rw [← Int.natCast_mod, ← Int.natCast_mod] at h2
  have h3 : x % M = y % M := by exact_mod_cast h2
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h3

/-- The canonical value lies in `[0, M)`. -/
lemma reduceSigned_lt {a : ℤ} {M : ℕ} (hM : 0 < M) : reduceSigned a M < M := by
  unfold reduceSigned
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have h1 : 0 ≤ a % (M : ℤ) := Int.emod_nonneg a hMz
  have h2 : a % (M : ℤ) < M := Int.emod_lt_of_pos a (by exact_mod_cast hM)
  omega

/-- The canonical value is congruent to `a` modulo `M`. -/
lemma reduceSigned_modEq {a : ℤ} {M : ℕ} (hM : 0 < M) :
    ((reduceSigned a M : ℕ) : ℤ) ≡ a [ZMOD M] := by
  unfold reduceSigned
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have h1 : 0 ≤ a % (M : ℤ) := Int.emod_nonneg a hMz
  rw [Int.toNat_of_nonneg h1]
  exact Int.mod_modEq a (M : ℤ)

/-- `↑(a.natAbs % M) ≡ a [ZMOD M]` — the modular residue of `|a|` matches `a`'s
    only up to sign, but we only use it in the appropriate branches. -/
private lemma natAbs_mod_modEq_natAbs {a : ℤ} {M : ℕ} :
    ((a.natAbs % M : ℕ) : ℤ) ≡ (a.natAbs : ℤ) [ZMOD M] := by
  rw [Int.natCast_mod]
  exact Int.mod_modEq _ _

/-- Nonnegative input: the reduced value is `|a| % M`. -/
lemma reduceSigned_eq_nonneg {a : ℤ} {M : ℕ} (hM : 0 < M) (h : 0 ≤ a) :
    a.natAbs % M = reduceSigned a M := by
  refine eq_of_lt_of_modEq (Nat.mod_lt _ hM) (reduceSigned_lt hM) ?_
  refine Int.ModEq.trans ?_ (reduceSigned_modEq hM).symm
  calc ((a.natAbs % M : ℕ) : ℤ)
      ≡ (a.natAbs : ℤ) [ZMOD M] := natAbs_mod_modEq_natAbs
    _ = a := Int.natAbs_of_nonneg h

/-- Negative input with nonzero residue: the reduced value is `M - |a| % M`. -/
lemma reduceSigned_eq_neg_pos {a : ℤ} {M : ℕ} (hM : 0 < M) (h : a < 0)
    (hne : a.natAbs % M ≠ 0) : M - a.natAbs % M = reduceSigned a M := by
  have hlt : a.natAbs % M < M := Nat.mod_lt _ hM
  refine eq_of_lt_of_modEq (by omega) (reduceSigned_lt hM) ?_
  refine Int.ModEq.trans ?_ (reduceSigned_modEq hM).symm
  rw [Nat.cast_sub (le_of_lt hlt)]
  have e2 : (a.natAbs : ℤ) = -a := Int.ofNat_natAbs_of_nonpos (le_of_lt h)
  have hM0 : (M : ℤ) ≡ 0 [ZMOD M] := (Int.modEq_zero_iff_dvd).mpr (dvd_refl _)
  calc ((M : ℤ) - (a.natAbs % M : ℕ))
      ≡ (M : ℤ) - (a.natAbs : ℤ) [ZMOD M] := (Int.ModEq.refl _).sub natAbs_mod_modEq_natAbs
    _ = (M : ℤ) + a := by rw [e2]; ring
    _ ≡ 0 + a [ZMOD M] := hM0.add_right a
    _ = a := by ring

/-- Negative input whose residue vanishes (`M ∣ |a|`): the reduced value is `0`. -/
lemma reduceSigned_eq_neg_zero {a : ℤ} {M : ℕ} (hM : 0 < M)
    (hz : a.natAbs % M = 0) : (0 : ℕ) = reduceSigned a M := by
  refine eq_of_lt_of_modEq hM (reduceSigned_lt hM) ?_
  refine Int.ModEq.trans ?_ (reduceSigned_modEq hM).symm
  have hdvd : (M : ℤ) ∣ a :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hz))
  simpa using (Int.modEq_zero_iff_dvd.mpr hdvd).symm

/-! ## Bridges for lifting the ℕ-model's correctness to the signed (`ℤ`) inputs -/

/-- `Nat.ModEq` lifts to `Int.ModEq` along the cast. -/
lemma natModEq_intCast {a b n : ℕ} (h : a ≡ b [MOD n]) :
    (a : ℤ) ≡ (b : ℤ) [ZMOD (n : ℤ)] := by
  show (a : ℤ) % n = (b : ℤ) % n
  rw [← Int.natCast_mod, ← Int.natCast_mod]
  exact_mod_cast h

/-- Congruence modulo `n` is congruence modulo `|n|`; the signed modulus and its
    absolute value give the same notion of inverse. -/
lemma modEq_natAbs_iff {a b n : ℤ} : a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD (n.natAbs : ℤ)] := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, Int.natAbs_dvd]

/-- The canonical representative keeps the gcd with the modulus. -/
lemma gcd_reduceSigned {a : ℤ} {M : ℕ} (hM : 0 < M) :
    Nat.gcd (reduceSigned a M) M = a.natAbs.gcd M := by
  have h1 : ((reduceSigned a M : ℕ) : ℤ) = a % (M : ℤ) := by
    unfold reduceSigned
    exact Int.toNat_of_nonneg (Int.emod_nonneg a (by exact_mod_cast hM.ne'))
  have h2 : Int.gcd ((reduceSigned a M : ℕ) : ℤ) (M : ℤ) = Int.gcd a (M : ℤ) := by
    rw [h1, Int.gcd_emod]
  simpa [Int.gcd, Int.natAbs_natCast] using h2

/-- Completeness transfers: a coprime input has a coprime canonical representative. -/
lemma coprime_reduceSigned {a : ℤ} {M : ℕ} (hM : 0 < M)
    (h : a.natAbs.gcd M = 1) : Nat.Coprime (reduceSigned a M) M := by
  show Nat.gcd (reduceSigned a M) M = 1
  rw [gcd_reduceSigned hM]; exact h

/-- Soundness lifts: a `Nat` inverse of the canonical input is an `Int` inverse of
    the original signed input, modulo `M`. -/
lemma reduceSigned_sound {a : ℤ} {M : ℕ} (hM : 0 < M) {k : ℕ}
    (h : reduceSigned a M * k ≡ 1 [MOD M]) :
    a * (k : ℤ) ≡ 1 [ZMOD (M : ℤ)] := by
  have hc : ((reduceSigned a M : ℕ) : ℤ) * (k : ℤ) ≡ 1 [ZMOD (M : ℤ)] := by
    have hh := natModEq_intCast h
    push_cast at hh
    exact hh
  calc a * (k : ℤ)
      ≡ ((reduceSigned a M : ℕ) : ℤ) * (k : ℤ) [ZMOD (M : ℤ)] :=
        (reduceSigned_modEq hM).symm.mul_right _
    _ ≡ 1 [ZMOD (M : ℤ)] := hc

end ModInverse
