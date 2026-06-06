/-
  # Refinement: the Aeneas-extracted machine code refines the ℕ model

  AI-MAINTAINED. This file proves that the Aeneas-extracted `modinverse_uN`
  functions (over `Std.UN` in the `Result` monad — i.e. the actual machine
  semantics, with overflow/division-by-zero modelled as `fail`) refine the
  abstract ℕ algorithm `ModInverse.modinverse`:

    * **never errors** — every `Result` is `ok` (no overflow, no div-by-zero), and
    * **value-matches** — the `.val` of the result equals `ModInverse.modinverse a.val m.val`.

  Composed with `Proofs.isCorrect : Spec.Correct ModInverse.modinverse`, this gives
  end-to-end correctness of the real extracted machine code.

  Proof style follows Aeneas's own skill files (`aeneas-lean-core`,
  `proof-patterns`): weakest-precondition specs `f args ⦃ r => P r ⦄`, the
  `step` / `step*` tactics, `agrind`/`scalar_tac` (never `omega`/`congr`).
-/

import Machine
import ModInverse.Model
import ModInverse.Proofs

open Aeneas Aeneas.Std Result
open modinverse  -- the Aeneas-extracted machine code lives in `namespace modinverse`

namespace Refinement

/-! ## Helper refinements: the per-width `mul_mod` computes `(a * b) % m` -/

/-- **Spec theorem for `modinverse::mul_mod_u32`.**
    Widening multiply-mod: casts to `u64`, multiplies (no overflow since both
    factors are `< 2^32`), reduces mod `m`, casts back. Computes `(a * b) % m`. -/
@[step]
theorem mul_mod_u32.spec (a b m : Std.U32) (hm : 0 < m.val) :
    mul_mod_u32 a b m ⦃ (r : Std.U32) => r.val = a.val * b.val % m.val ⦄ := by
  unfold mul_mod_u32
  step*
  -- Remaining goal: `(cast U32 i4).val = a.val * b.val % m.val`, where the `step*`
  -- hypotheses give `i4.val = ((cast U64 a).val * (cast U64 b).val) % (cast U64 m).val`.
  -- Widening casts (u32→u64) preserve `.val`; the narrow cast back is lossless because
  -- `i4.val = (a*b) % m < m ≤ U32.max < 2^32`.
  simp only [UScalar.cast_val_eq] at *
  scalar_tac

/-- **Spec theorem for `modinverse::mul_mod_u8`** (widening multiply-mod, u8→u16). -/
@[step]
theorem mul_mod_u8.spec (a b m : Std.U8) (hm : 0 < m.val) :
    mul_mod_u8 a b m ⦃ (r : Std.U8) => r.val = a.val * b.val % m.val ⦄ := by
  unfold mul_mod_u8
  step*
  simp only [UScalar.cast_val_eq] at *
  scalar_tac

/-- **Spec theorem for `modinverse::mul_mod_u16`** (widening multiply-mod, u16→u32). -/
@[step]
theorem mul_mod_u16.spec (a b m : Std.U16) (hm : 0 < m.val) :
    mul_mod_u16 a b m ⦃ (r : Std.U16) => r.val = a.val * b.val % m.val ⦄ := by
  unfold mul_mod_u16
  step*
  simp only [UScalar.cast_val_eq] at *
  scalar_tac

/-- **Spec theorem for `modinverse::mul_mod_u64`** (widening multiply-mod, u64→u128). -/
@[step]
theorem mul_mod_u64.spec (a b m : Std.U64) (hm : 0 < m.val) :
    mul_mod_u64 a b m ⦃ (r : Std.U64) => r.val = a.val * b.val % m.val ⦄ := by
  unfold mul_mod_u64
  step*
  simp only [UScalar.cast_val_eq] at *
  scalar_tac

/-! ## `add_mod_u128`: branch-free-ish modular addition of reduced operands -/

/-- **Spec theorem for `modinverse::add_mod_u128`.**
    Computes `(a + b) % m` for already-reduced operands `a, b < m`, avoiding
    overflow: `room = m - a`; if `b < room` (i.e. `a + b < m`) return `a + b`,
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

/-! ## The extended-Euclidean loop refines `ModInverse.loop` (u8 template) -/

/-- **Loop refinement for `modinverse_u8_loop`.** The machine loop over `Std.U8`
    computes exactly the ℕ model loop `ModInverse.loop` on the corresponding state,
    and never errors. Preconditions match the model `State` invariants: `s, s_next < m`
    (kept reduced) and `0 < m`. -/
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

/-! ## Phase 1 contracts: loop-dependent specs (awaiting `-loops-to-rec` re-extraction)

  The statements below are the public refinement contracts. Their *signatures* are
  translation-independent (the top-level function types do not change between the
  fixed-point-combinator and recursive loop translations); their *proofs* are
  written against the recursive loop functions produced by extracting with
  `-loops-to-rec`, which the mature `unfold`/`step*`/`termination_by` proof
  pattern needs.

  Each top-level `modinverse_uN` contract says simultaneously:
    * **no error** — the `Result` is `ok` (no overflow / div-by-zero), and
    * **value match** — `r.map (·.val) = ModInverse.modinverse a.val m.val`, i.e. the
      `Option` structure (none vs some) and the inverse value agree with the ℕ model.
  Composed with `Proofs.isCorrect`, this certifies the extracted machine code. -/

/-- **Loop refinement for `mul_mod_u128_loop`** (Russian-peasant doubling loop).
    Mirrors `ModInverse.mulModAux`: `b &&& 1` is `b % 2`, `b >>> 1` is `b / 2`,
    `add_mod_u128` is `addMod`. The invariants `a, result < m` keep `add_mod_u128`
    in range. -/
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

/-- **Spec for `modinverse::mul_mod_u128`.** Computes `(a * b) % m` via the
    Russian-peasant loop, reducing through `ModInverse.mulMod`. -/
@[step]
theorem mul_mod_u128.spec (a b m : Std.U128) (hm : 0 < m.val) :
    mul_mod_u128 a b m ⦃ (r : Std.U128) => r.val = a.val * b.val % m.val ⦄ := by
  unfold mul_mod_u128
  step*
  -- `r = mulModAux m (a % m) b 0 = mulMod a b m = (a * b) % m`
  rw [r_post, a1_post, ← ModInverse.mulMod_eq hm]
  unfold ModInverse.mulMod
  rw [if_neg (by scalar_tac)]

/-- **Top-level refinement for `modinverse::modinverse_u8`.** -/
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

/-! ## u16/u32/u64: width templates of the u8 loop + top-level proofs above -/

/-- **Loop refinement for `modinverse_u16_loop`.** -/
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

/-- **Top-level refinement for `modinverse::modinverse_u16`.** -/
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

/-- **Loop refinement for `modinverse_u32_loop`.** -/
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

/-- **Top-level refinement for `modinverse::modinverse_u32`.** -/
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

/-- **Loop refinement for `modinverse_u64_loop`.** -/
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

/-- **Top-level refinement for `modinverse::modinverse_u64`.** -/
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

/-- **Loop refinement for `modinverse_u128_loop`** (template of the u8 loop; the
    `qs` step uses `mul_mod_u128` rather than the widening helper). -/
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

/-- **Top-level refinement for `modinverse::modinverse_u128`.**
    Composed with `Proofs.isCorrect : Spec.Correct ModInverse.modinverse`, this is the
    end-to-end correctness theorem for the extracted u128 machine code. -/
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

/-! ## End-to-end correctness of the extracted u128 machine code

  Composing the refinement (`modinverse_u128.spec`: the machine refines the ℕ model)
  with `ModInverse.isCorrect` (the model meets the specification) certifies the
  *actual extracted machine code*: `modinverse_u128` never errors, and whatever it
  returns is a correct modular inverse — sound, bounded, and complete. -/

/-- **The extracted `modinverse_u128` is a correct modular inverse.** -/
theorem modinverse_u128_correct (a m : Std.U128) (hm : 0 < m.val) :
    modinverse_u128 a m ⦃ (r : Option Std.U128) =>
      -- soundness: a returned witness really is an inverse
      (∀ s : Std.U128, r = some s → a.val * s.val ≡ 1 [MOD m.val]) ∧
      -- bound: the witness is the canonical representative in `[0, m)`
      (∀ s : Std.U128, r = some s → s.val < m.val) ∧
      -- completeness: an inverse is produced whenever one exists
      (Nat.Coprime a.val m.val → ∃ s : Std.U128, r = some s) ⦄ := by
  apply WP.spec_mono (modinverse_u128.spec a m)
  intro r hr
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    apply ModInverse.isCorrect.sound
    rw [← hr, hs]; rfl
  · intro s hs
    apply ModInverse.isCorrect.bounded _ _ _ hm
    rw [← hr, hs]; rfl
  · intro hcop
    obtain ⟨sm, hsm⟩ := ModInverse.isCorrect.complete a.val m.val hm hcop
    rw [hsm] at hr
    cases r with
    | none => simp at hr
    | some s => exact ⟨s, rfl⟩

end Refinement
