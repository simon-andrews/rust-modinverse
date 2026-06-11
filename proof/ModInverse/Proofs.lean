/-
  # Proofs: discharging the targets (AI-MAINTAINED)

  Every declaration here exists to satisfy a target in `ModInverse.Spec` (the
  human-maintained spec in the root `ModInverse.lean`). Do not weaken any statement:
  the trusted statements live there, and the certificates at the bottom (`isCorrect`,
  `helpersCompute`) must produce terms of exactly those types. If a proof here is
  incomplete the whole library fails to build — there is no `sorry` and no `axiom`.

  The strategy: run the extended Euclidean algorithm with a loop invariant stated
  in `ZMod m` (so the per-step `% m` reductions become no-ops), then translate
  back to `Nat`-level congruences at the end.
-/

import ModInverse
import ModInverse.Model
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace ModInverse

/-! ## `subMod` in `ZMod m` -/

/-- The whole reason `subMod` exists: in `ZMod m`, it's literally `a - b`. -/
lemma subMod_cast (a b m : ℕ) (hb : b < m) :
    ((subMod a b m : ℕ) : ZMod m) = (a : ZMod m) - (b : ZMod m) := by
  unfold subMod
  split
  case isTrue h =>
    rw [Nat.cast_sub h]
  case isFalse h =>
    have hba : b ≤ m + a := by omega
    rw [Nat.cast_sub hba, Nat.cast_add, ZMod.natCast_self, zero_add]

/-! ## The loop invariant

    At every step, `s` is a modular witness for `r`: `a * s ≡ r (mod m)`, and
    likewise `sNext` for `rNext`. Stated in `ZMod m` so reductions vanish. -/

def Invariant (a m : ℕ) (st : State m) : Prop :=
  ((a : ZMod m) * st.s = (st.r : ZMod m)) ∧
  ((a : ZMod m) * st.sNext = (st.rNext : ZMod m))

/-- Loop entry satisfies the invariant. -/
lemma invariant_init {a m : ℕ} (hm : 1 < m) :
    Invariant a m
      { r := m, rNext := a % m, s := 0, sNext := 1,
        sLt := by omega, sNextLt := hm } := by
  refine ⟨?_, ?_⟩
  · show (a : ZMod m) * (0 : ℕ) = (m : ZMod m)
    simp
  · show (a : ZMod m) * (1 : ℕ) = ((a % m : ℕ) : ZMod m)
    simp [ZMod.natCast_mod]

/-- One iteration preserves the invariant. The heart of the proof. -/
lemma invariant_step {a m : ℕ} (hm : 0 < m) (st : State m)
    (hRNext : st.rNext ≠ 0) (hInv : Invariant a m st) :
    Invariant a m (step hm st hRNext) := by
  obtain ⟨h_s, h_sNext⟩ := hInv
  refine ⟨?_, ?_⟩
  · exact h_sNext
  · set q := st.r / st.rNext
    show (a : ZMod m) * (subMod st.s ((q * st.sNext) % m) m : ℕ)
       = ((st.r % st.rNext : ℕ) : ZMod m)
    have hqs_lt : (q * st.sNext) % m < m := Nat.mod_lt _ hm
    rw [subMod_cast _ _ _ hqs_lt]
    have h_qs_cast : (((q * st.sNext) % m : ℕ) : ZMod m)
                  = q * (st.sNext : ZMod m) := by
      rw [ZMod.natCast_mod]; push_cast; ring
    rw [h_qs_cast]
    have h_lhs : (a : ZMod m) * ((st.s : ZMod m) - q * (st.sNext : ZMod m))
               = (a : ZMod m) * st.s - q * ((a : ZMod m) * st.sNext) := by ring
    rw [h_lhs, h_s, h_sNext]
    have h_div_mod : (st.r : ZMod m)
                   = q * (st.rNext : ZMod m) + ((st.r % st.rNext : ℕ) : ZMod m) := by
      have : st.r = st.r / st.rNext * st.rNext + st.r % st.rNext :=
        (Nat.div_add_mod' st.r st.rNext).symm
      calc (st.r : ZMod m)
          = ((st.r / st.rNext * st.rNext + st.r % st.rNext : ℕ) : ZMod m) := by
            rw [← this]
        _ = q * (st.rNext : ZMod m) + ((st.r % st.rNext : ℕ) : ZMod m) := by
            push_cast; ring
    linear_combination h_div_mod

/-! ## Induction over the loop -/

/-- The invariant holds at the loop's exit. -/
lemma invariant_loop {a m : ℕ} (hm : 0 < m) (st : State m)
    (hInv : Invariant a m st) :
    (a : ZMod m) * (loop hm st).2 = ((loop hm st).1 : ZMod m) := by
  induction st using loop.induct (m := m) hm with
  | case1 _x _alias hZero =>
    rw [loop, dif_pos hZero]
    exact hInv.1
  | case2 x _alias hNZ _decr ih =>
    rw [loop, dif_neg hNZ]
    exact ih (invariant_step hm x hNZ hInv)

/-- The `s` component stays in `[0, m)` throughout the loop. -/
lemma loop_snd_lt {m : ℕ} (hm : 0 < m) (st : State m) :
    (loop hm st).2 < m := by
  induction st using loop.induct (m := m) hm with
  | case1 x _alias hZero =>
    rw [loop, dif_pos hZero]; exact x.sLt
  | case2 _x _alias hNZ _decr ih =>
    rw [loop, dif_neg hNZ]; exact ih

/-- The loop computes `Nat.gcd`. Classical Euclidean termination. -/
lemma loop_fst_eq_gcd {m : ℕ} (hm : 0 < m) (st : State m) :
    (loop hm st).1 = Nat.gcd st.r st.rNext := by
  induction st using loop.induct (m := m) hm with
  | case1 x _alias hZero =>
    rw [loop, dif_pos hZero]
    show x.r = Nat.gcd x.r x.rNext
    rw [show x.rNext = 0 from hZero, Nat.gcd_zero_right]
  | case2 x _alias hNZ _decr ih =>
    rw [loop, dif_neg hNZ, ih]
    show Nat.gcd x.rNext (x.r % x.rNext) = Nat.gcd x.r x.rNext
    rw [Nat.gcd_comm x.rNext (x.r % x.rNext), ← Nat.gcd_rec, Nat.gcd_comm]

/-! ## Correctness of `modinverseCore` (the `1 < m` case) -/

/-- Unfold `modinverseCore` once and expose the loop's output. -/
private lemma modinverseCore_dest (a m : ℕ) (hm : 1 < m) :
    let init : State m :=
      ⟨m, a % m, 0, 1, by omega, hm⟩
    let p := loop (by omega) init
    modinverseCore a m hm = if p.1 = 1 then some p.2 else none := rfl

/-- Soundness for `modinverseCore`. -/
theorem modinverseCore_correct (a m : ℕ) (hm : 1 < m) (s : ℕ)
    (h : modinverseCore a m hm = some s) :
    a * s % m = 1 := by
  set init : State m := ⟨m, a % m, 0, 1, by omega, hm⟩ with hinit
  set p := loop (by omega : 0 < m) init with hp
  have hInvFinal : (a : ZMod m) * (p.2 : ℕ) = ((p.1 : ℕ) : ZMod m) :=
    invariant_loop (by omega) init (invariant_init hm)
  rw [modinverseCore_dest a m hm, ← hinit, ← hp] at h
  split_ifs at h with hgcd
  obtain rfl : p.2 = s := Option.some_inj.mp h
  rw [hgcd, Nat.cast_one] at hInvFinal
  have hCast : ((a * p.2 : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
    push_cast; exact hInvFinal
  rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq, Nat.mod_eq_of_lt hm] at hCast
  exact hCast

/-- Bound for `modinverseCore`: the witness sits in `[0, m)`. -/
theorem modinverseCore_lt (a m : ℕ) (hm : 1 < m) (s : ℕ)
    (h : modinverseCore a m hm = some s) :
    s < m := by
  set init : State m := ⟨m, a % m, 0, 1, by omega, hm⟩ with hinit
  set p := loop (by omega : 0 < m) init with hp
  have hBound : p.2 < m := loop_snd_lt (by omega) init
  rw [modinverseCore_dest a m hm, ← hinit, ← hp] at h
  split_ifs at h
  obtain rfl : p.2 = s := Option.some_inj.mp h
  exact hBound

/-- The loop's first output is `gcd a m`. -/
private lemma loop_fst_eq_gcd_init {a m : ℕ} (hm : 1 < m) :
    (loop (by omega : 0 < m)
       (⟨m, a % m, 0, 1, by omega, hm⟩ : State m)).1 = Nat.gcd a m := by
  rw [loop_fst_eq_gcd]
  show Nat.gcd m (a % m) = Nat.gcd a m
  rw [Nat.gcd_comm m (a % m), ← Nat.gcd_rec, Nat.gcd_comm]

/-- Completeness for `modinverseCore`. -/
theorem modinverseCore_complete (a m : ℕ) (hm : 1 < m)
    (hCoprime : Nat.Coprime a m) :
    ∃ s, modinverseCore a m hm = some s := by
  set init : State m := ⟨m, a % m, 0, 1, by omega, hm⟩ with hinit
  set p := loop (by omega : 0 < m) init with hp
  have hGcd : p.1 = 1 := by rw [hp]; exact (loop_fst_eq_gcd_init hm).trans hCoprime
  refine ⟨p.2, ?_⟩
  rw [modinverseCore_dest a m hm, ← hinit, ← hp, if_pos hGcd]

/-- No false positives for `modinverseCore`. -/
theorem modinverseCore_none_of_not_coprime (a m : ℕ) (hm : 1 < m)
    (hNotCoprime : ¬ Nat.Coprime a m) :
    modinverseCore a m hm = none := by
  set init : State m := ⟨m, a % m, 0, 1, by omega, hm⟩ with hinit
  set p := loop (by omega : 0 < m) init with hp
  have hGcdNe : p.1 ≠ 1 := by
    rw [hp, loop_fst_eq_gcd_init hm]; exact hNotCoprime
  rw [modinverseCore_dest a m hm, ← hinit, ← hp, if_neg hGcdNe]

/-! ## Wrapper-level correctness of `modinverse` (the total function) -/

/-- Soundness. -/
theorem modinverse_correct (a m s : ℕ)
    (h : modinverse a m = some s) :
    a * s ≡ 1 [MOD m] := by
  unfold modinverse at h
  split_ifs at h with hm hm1
  · have hCore := modinverseCore_correct a m hm s h
    rw [Nat.ModEq, Nat.mod_eq_of_lt hm, hCore]
  · subst hm1
    exact Nat.modEq_one

/-- Bound. -/
theorem modinverse_lt (a m s : ℕ) (hm : 0 < m)
    (h : modinverse a m = some s) :
    s < m := by
  unfold modinverse at h
  split_ifs at h with h1 h2
  · exact modinverseCore_lt a m h1 s h
  · subst h2
    have : s = 0 := Option.some_inj.mp h.symm
    omega

/-- Completeness. -/
theorem modinverse_complete (a m : ℕ) (hm : 0 < m)
    (hCoprime : Nat.Coprime a m) :
    ∃ s, modinverse a m = some s := by
  unfold modinverse
  split_ifs with h1 h2
  · exact modinverseCore_complete a m h1 hCoprime
  · exact ⟨0, rfl⟩
  · omega

/-- Exact failure. -/
theorem modinverse_none_iff (a m : ℕ) :
    modinverse a m = none ↔ m = 0 ∨ ¬ Nat.Coprime a m := by
  unfold modinverse
  constructor
  · intro h
    split_ifs at h with h1 h2
    · right
      by_contra hCop
      obtain ⟨s, hs⟩ := modinverseCore_complete a m h1 hCop
      rw [hs] at h
      simp at h
    · left; omega
  · intro h
    split_ifs with h1 h2
    · rcases h with hm0 | hNot
      · omega
      · exact modinverseCore_none_of_not_coprime a m h1 hNot
    · subst h2
      rcases h with hm0 | hNot
      · exact absurd hm0 (by decide)
      · exact absurd (Nat.coprime_one_right a) hNot
    · rfl

/-! ## Correctness of the overflow-avoiding helpers -/

lemma addMod_lt {a b m : ℕ} (ha : a < m) (hb : b < m) (_hm : 0 < m) :
    addMod a b m < m := by
  unfold addMod; split <;> omega

lemma addMod_eq {a b m : ℕ} (ha : a < m) (hb : b < m) (_hm : 0 < m) :
    addMod a b m = (a + b) % m := by
  unfold addMod
  split
  case isTrue h =>
    rw [Nat.mod_eq_of_lt (by omega)]
  case isFalse h =>
    have hge : m ≤ a + b := by omega
    have hlt2 : a + b - m < m := by omega
    have hrw : (a + b) % m = (a + b - m) % m := by
      conv_lhs => rw [show a + b = (a + b - m) + m from by omega]
      exact Nat.add_mod_right _ _
    rw [hrw, Nat.mod_eq_of_lt hlt2]
    omega

lemma mulModAux_lt {m : ℕ} (hm : 0 < m) :
    ∀ (a b acc : ℕ), a < m → acc < m → mulModAux m a b acc < m
  | _, 0,     acc, _,  hacc => by unfold mulModAux; exact hacc
  | a, b + 1, acc, ha, hacc => by
    unfold mulModAux
    refine mulModAux_lt hm _ _ _ (addMod_lt ha ha hm) ?_
    split <;> [exact addMod_lt hacc ha hm; exact hacc]

lemma mulMod_lt {a b m : ℕ} (hm : 0 < m) : mulMod a b m < m := by
  unfold mulMod
  rw [if_neg (by omega)]
  exact mulModAux_lt hm _ _ _ (Nat.mod_lt _ hm) hm

/-- Loop invariant of `mulModAux`: it returns `(acc + a * b) % m`. -/
lemma mulModAux_eq {m : ℕ} (hm : 0 < m) :
    ∀ (a b acc : ℕ), a < m → acc < m →
      mulModAux m a b acc = (acc + a * b) % m
  | _, 0,     acc, _,  hacc => by
    unfold mulModAux
    rw [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hacc]
  | a, b + 1, acc, ha, hacc => by
    unfold mulModAux
    have ha2 : addMod a a m < m := addMod_lt ha ha hm
    set acc' : ℕ :=
      if (b + 1) % 2 = 1 then addMod acc a m else acc with hacc'
    have hacc'_lt : acc' < m := by
      rw [hacc']; split <;> [exact addMod_lt hacc ha hm; exact hacc]
    rw [mulModAux_eq hm _ _ _ ha2 hacc'_lt]
    have h2a : addMod a a m = (2 * a) % m := by
      rw [addMod_eq ha ha hm, two_mul]
    rw [h2a]
    suffices h : acc' + (2 * a % m) * ((b + 1) / 2) ≡ acc + a * (b + 1) [MOD m] by
      exact h
    have h2a_mod : (2 * a) % m ≡ 2 * a [MOD m] := Nat.mod_modEq _ _
    have hmul : (2 * a % m) * ((b + 1) / 2) ≡ 2 * a * ((b + 1) / 2) [MOD m] :=
      h2a_mod.mul_right _
    by_cases hp : (b + 1) % 2 = 1
    · have hacc'_val : acc' = addMod acc a m := by rw [hacc', if_pos hp]
      have h_acc_add : addMod acc a m = (acc + a) % m := addMod_eq hacc ha hm
      have hbsplit : b + 1 = 2 * ((b + 1) / 2) + 1 := by
        have := Nat.div_add_mod (b + 1) 2; omega
      have hacc'_eq : acc' ≡ acc + a [MOD m] := by
        rw [hacc'_val, h_acc_add]; exact Nat.mod_modEq _ _
      calc acc' + (2 * a % m) * ((b + 1) / 2)
          ≡ (acc + a) + 2 * a * ((b + 1) / 2) [MOD m] := hacc'_eq.add hmul
        _ = acc + a * (2 * ((b + 1) / 2) + 1) := by ring
        _ = acc + a * (b + 1) := by rw [← hbsplit]
    · have hacc'_val : acc' = acc := by rw [hacc', if_neg hp]
      have hbsplit : b + 1 = 2 * ((b + 1) / 2) := by
        have := Nat.div_add_mod (b + 1) 2; omega
      calc acc' + (2 * a % m) * ((b + 1) / 2)
          ≡ acc + 2 * a * ((b + 1) / 2) [MOD m] := by
            rw [hacc'_val]; exact Nat.ModEq.rfl.add hmul
        _ = acc + a * (2 * ((b + 1) / 2)) := by ring
        _ = acc + a * (b + 1) := by rw [← hbsplit]

lemma mulMod_eq {a b m : ℕ} (hm : 0 < m) : mulMod a b m = (a * b) % m := by
  unfold mulMod
  rw [if_neg (by omega)]
  rw [mulModAux_eq hm _ _ _ (Nat.mod_lt _ hm) hm, Nat.zero_add,
      Nat.mod_mul_mod]

/-! ## Certificates: every target in `Targets.lean` is discharged

    These instances are the mechanical link to the human-maintained spec. Each
    field below must have exactly the type declared in `ModInverse.Spec`, so the
    proofs cannot drift from the statements. Adding a field to a `Spec` structure
    breaks these until the new obligation is met. -/

/-- `modinverse` satisfies every correctness target. -/
theorem isCorrect : Spec.Correct modinverse where
  sound        := fun a m s h    => modinverse_correct a m s h
  bounded      := fun a m s hm h => modinverse_lt a m s hm h
  complete     := fun a m hm hc  => modinverse_complete a m hm hc
  failsExactly := fun a m        => modinverse_none_iff a m

/-- The helpers compute standard modular arithmetic. -/
theorem helpersCompute : Spec.HelpersCompute addMod mulMod where
  addMod_eq := fun _ _ _ ha hb hm => addMod_eq ha hb hm
  mulMod_eq := fun _ _ _ hm       => mulMod_eq hm

/-! ## Mechanized sanity check (definition-level, not part of the spec)

    A cheap belt-and-braces check that the *definition* computes what it should.
    `native_decide` runs it at proof time. It introduces `Lean.ofReduceBool`, so
    it is kept off the `isCorrect` path: `#print axioms isCorrect` below should
    show only Lean's standard axioms. -/

def sanityCheck (m : ℕ) (hm : 1 < m) : Bool :=
  (List.range m).all fun a =>
    match modinverseCore a m hm with
    | none   => Nat.gcd a m ≠ 1
    | some s => (a * s) % m = 1

example : sanityCheck 26 (by decide) = true := by native_decide
example : sanityCheck 97 (by decide) = true := by native_decide

-- Axiom audit: should report only `propext`, `Classical.choice`, `Quot.sound`
-- (Lean's standard axioms) — in particular, no `sorryAx` and no `ofReduceBool`.
#print axioms isCorrect
#print axioms helpersCompute

end ModInverse
