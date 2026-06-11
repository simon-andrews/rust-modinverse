/-
  # Refinement helpers: the `mul_mod` / `add_mod` building blocks

  These are the small arithmetic primitives the inverse loop calls. Each spec says
  the extracted machine routine never errors and computes the obvious thing:

    * `mul_mod_uN` (narrow widths) widens to the next type, multiplies, reduces —
      so it computes `(a * b) % m`.
    * `add_mod_u128` adds two reduced operands mod `m` without overflowing `u128`.
    * `mul_mod_u128` does the same multiply via the Russian-peasant doubling loop
      (`mul_mod_u128_loop`), since `u128` has no wider type to widen into.

  They are tagged `@[step]` so the loop refinements in `Unsigned.lean` pick them up
  automatically.
-/

import Machine
import ModInverse
import ModInverse.Proofs

open Aeneas Aeneas.Std Result
open modinverse  -- the Aeneas-extracted machine code lives in `namespace modinverse`

namespace Refinement

/-! ## Widening multiply-mod for `u8`–`u64`: computes `(a * b) % m` -/

/-- **`mul_mod_u8`** (widening multiply-mod, u8→u16). -/
@[step]
theorem mul_mod_u8.spec (a b m : Std.U8) (hm : 0 < m.val) :
    mul_mod_u8 a b m ⦃ (r : Std.U8) => r.val = a.val * b.val % m.val ⦄ := by
  unfold mul_mod_u8
  step*
  simp only [UScalar.cast_val_eq] at *
  scalar_tac

/-- **`mul_mod_u16`** (widening multiply-mod, u16→u32). -/
@[step]
theorem mul_mod_u16.spec (a b m : Std.U16) (hm : 0 < m.val) :
    mul_mod_u16 a b m ⦃ (r : Std.U16) => r.val = a.val * b.val % m.val ⦄ := by
  unfold mul_mod_u16
  step*
  simp only [UScalar.cast_val_eq] at *
  scalar_tac

/-- **`mul_mod_u32`.**
    Casts to `u64`, multiplies (no overflow since both factors are `< 2^32`), reduces
    mod `m`, casts back. The narrow cast back is lossless because the result
    `(a*b) % m < m ≤ U32.max < 2^32`. -/
@[step]
theorem mul_mod_u32.spec (a b m : Std.U32) (hm : 0 < m.val) :
    mul_mod_u32 a b m ⦃ (r : Std.U32) => r.val = a.val * b.val % m.val ⦄ := by
  unfold mul_mod_u32
  step*
  simp only [UScalar.cast_val_eq] at *
  scalar_tac

/-- **`mul_mod_u64`** (widening multiply-mod, u64→u128). -/
@[step]
theorem mul_mod_u64.spec (a b m : Std.U64) (hm : 0 < m.val) :
    mul_mod_u64 a b m ⦃ (r : Std.U64) => r.val = a.val * b.val % m.val ⦄ := by
  unfold mul_mod_u64
  step*
  simp only [UScalar.cast_val_eq] at *
  scalar_tac

/-! ## `u128` multiply-mod: Russian-peasant doubling (no wider type to widen into) -/

/-- **`add_mod_u128`.** Computes `(a + b) % m` for already-reduced operands `a, b < m`,
    avoiding overflow: `room = m - a`; if `b < room` (i.e. `a + b < m`) return `a + b`,
    else return `b - room = a + b - m`. -/
@[step]
theorem add_mod_u128.spec (a b m : Std.U128) (ha : a.val < m.val) (hb : b.val < m.val) :
    add_mod_u128 a b m ⦃ (r : Std.U128) => r.val = (a.val + b.val) % m.val ⦄ := by
  unfold add_mod_u128
  step*
  · -- branch `b < room`, i.e. `a + b < m`: the result `a + b` is already reduced.
    simp_scalar [*]
  · -- branch `¬ b < room`, i.e. `m ≤ a + b < 2m`: result is `b - (m - a) = a + b - m`.
    -- omega can't reduce `% m` (variable divisor), so peel one `m` off explicitly.
    rw [r_post1, room_post1]
    have hle : m.val ≤ a.val + b.val := by scalar_tac
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by scalar_tac)]
    scalar_tac

/-- **`mul_mod_u128_loop`** (Russian-peasant doubling loop). Mirrors `ModInverse.mulModAux`:
    `b &&& 1` is `b % 2`, `b >>> 1` is `b / 2`, `add_mod_u128` is `addMod`. The
    invariants `a, result < m` keep `add_mod_u128` in range. -/
@[step]
theorem mul_mod_u128_loop.spec (a b m result : Std.U128)
    (hm : 0 < m.val) (ha : a.val < m.val) (hres : result.val < m.val) :
    mul_mod_u128_loop a b m result ⦃ (r : Std.U128) =>
      r.val = ModInverse.mulModAux m.val a.val b.val result.val ⦄ := by
  unfold mul_mod_u128_loop
  by_cases hb : b = 0#u128
  · simp only [hb]
    simp [ModInverse.mulModAux]
  · simp only [gt_iff_lt]
    step*
    have hi : i.val = b.val % 2 := by simp [i_post1, UScalar.val_and, Nat.and_one_is_mod]
    obtain ⟨k, hk⟩ : ∃ k, b.val = k + 1 := ⟨b.val - 1, by scalar_tac⟩
    by_cases hi1 : i = 1#u128
    · -- b odd: accumulate `addMod result a m`
      rw [if_pos hi1]
      step*
      have hodd : (k + 1) % 2 = 1 := by rw [← hk, ← hi]; simp [hi1]
      rw [r_post, hk, ModInverse.mulModAux, if_pos hodd, a1_post, b1_post1, result1_post,
          ModInverse.addMod_eq ha ha hm, ModInverse.addMod_eq hres ha hm]
      congr 1
      rw [← hk]; simp [Nat.shiftRight_eq_div_pow]
    · -- b even: accumulator unchanged
      rw [if_neg hi1]
      step*
      have heven : (k + 1) % 2 ≠ 1 := by rw [← hk, ← hi]; simp; scalar_tac
      rw [r_post, hk, ModInverse.mulModAux, if_neg heven, a1_post, b1_post1,
          ModInverse.addMod_eq ha ha hm]
      congr 1
      rw [← hk]; simp [Nat.shiftRight_eq_div_pow]
  termination_by b.val
  decreasing_by
    · have hb1 : (b1.val : ℕ) = b.val / 2 := by
        rw [b1_post1, Nat.shiftRight_eq_div_pow]; norm_num
      scalar_tac
    · have hb1 : (b1.val : ℕ) = b.val / 2 := by
        rw [b1_post1, Nat.shiftRight_eq_div_pow]; norm_num
      scalar_tac

/-- **`mul_mod_u128`.** Computes `(a * b) % m` via the Russian-peasant loop, reducing
    through `ModInverse.mulMod`. -/
@[step]
theorem mul_mod_u128.spec (a b m : Std.U128) (hm : 0 < m.val) :
    mul_mod_u128 a b m ⦃ (r : Std.U128) => r.val = a.val * b.val % m.val ⦄ := by
  unfold mul_mod_u128
  step*
  -- `r = mulModAux m (a % m) b 0 = mulMod a b m = (a * b) % m`
  rw [r_post, a1_post, ← ModInverse.mulMod_eq hm]
  unfold ModInverse.mulMod
  rw [if_neg (by scalar_tac)]

end Refinement
