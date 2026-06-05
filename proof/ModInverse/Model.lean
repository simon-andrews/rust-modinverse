/-
  # Model: the algorithm under verification

  TRANSLATION LAYER. This file defines, in Lean 4 (ℕ), the same algorithm as the
  Rust function `modinverse_u128` in `src/lib.rs`, plus its two overflow-avoiding
  helpers. It contains **definitions only** — no correctness claims. What the
  definitions are *supposed* to satisfy lives in `ModInverse/Targets.lean`
  (human-maintained); the evidence that they do lives in `ModInverse/Proofs.lean`
  (AI-maintained).

  Today this is a hand translation of the Rust, faithful by inspection. The
  intent is to replace it with an Aeneas-generated model (Rust → LLBC → Lean),
  at which point this file becomes machine-generated and the "faithful by
  inspection" caveat is discharged mechanically. Either way the *spec* in
  `Targets.lean` is unchanged: it is stated against whatever `modinverse` is.

  Rust → Lean mapping (one-to-one):

      fn sub_mod_u128(a, b, m)   def subMod
      fn add_mod_u128(a, b, m)   def addMod
      fn mul_mod_u128(a, b, m)   def mulMod  (via mulModAux)
      one loop iteration         def step
      `while r_next != 0 {...}`  def loop  (well-founded recursion on rNext)
      fn modinverse_u128(a, m)   def modinverse

  Rust is `u128`; this model is `ℕ`. The `u128` operations never overflow under
  their documented preconditions, so a `ℕ` model captures the relevant
  semantics. (That no-overflow claim is itself by inspection here; an Aeneas
  model would carry it as a proof obligation instead.)
-/

import Mathlib.Tactic

namespace ModInverse

/-! ## `subMod`: subtraction kept in `[0, m)`. Mirrors Rust `sub_mod_u128`. -/

/-- Lean mirror of Rust `fn sub_mod_u128(a, b, m)`. -/
def subMod (a b m : ℕ) : ℕ :=
  if a ≥ b then a - b else m + a - b

lemma subMod_lt {a b m : ℕ} (ha : a < m) (hb : b < m) : subMod a b m < m := by
  unfold subMod; split <;> omega

/-! ## The inverse algorithm. Mirrors `src/lib.rs::modinverse_u128` line-by-line. -/

/-- Loop state. The two `< m` bounds carry the fact that `s` and `sNext` are
    kept reduced. -/
structure State (m : ℕ) where
  r       : ℕ
  rNext   : ℕ
  s       : ℕ
  sNext   : ℕ
  sLt     : s < m
  sNextLt : sNext < m

/-- One iteration of the Rust loop body. -/
def step {m : ℕ} (hm : 0 < m) (st : State m) (_hRNext : st.rNext ≠ 0) :
    State m :=
  let qs := (st.r / st.rNext * st.sNext) % m
  { r       := st.rNext
    rNext   := st.r % st.rNext
    s       := st.sNext
    sNext   := subMod st.s qs m
    sLt     := st.sNextLt
    sNextLt := subMod_lt st.sLt (Nat.mod_lt _ hm) }

/-- The `while !r_next.is_zero()` loop as well-founded recursion on `rNext`. -/
def loop {m : ℕ} (hm : 0 < m) : State m → ℕ × ℕ
  | st =>
    if h : st.rNext = 0 then
      (st.r, st.s)
    else
      have : (step hm st h).rNext < st.rNext :=
        Nat.mod_lt _ (Nat.pos_of_ne_zero h)
      loop hm (step hm st h)
  termination_by st => st.rNext

/-- The inverse computation when `1 < m`. -/
def modinverseCore (a m : ℕ) (hm : 1 < m) : Option ℕ :=
  let init : State m :=
    { r := m, rNext := a % m, s := 0, sNext := 1,
      sLt := by omega, sNextLt := hm }
  let (gcd, s) := loop (by omega) init
  if gcd = 1 then some s else none

/-- Lean mirror of Rust `pub fn modinverse_u128(a, m) -> Option<u128>`. Handles
    the early returns (`m = 0` → `none`, `m = 1` → `some 0`) and delegates the
    interesting case `1 < m` to `modinverseCore`. -/
def modinverse (a m : ℕ) : Option ℕ :=
  if hm : 1 < m then modinverseCore a m hm
  else if m = 1 then some 0
  else none

/-! ## Overflow-avoiding helpers. Mirror Rust `add_mod_u128` / `mul_mod_u128`. -/

/-- Lean mirror of Rust `fn add_mod_u128(a, b, m)`. The `room` trick avoids
    forming `a + b` directly, which in Rust would overflow `u128`. -/
def addMod (a b m : ℕ) : ℕ :=
  if b < m - a then a + b else b - (m - a)

/-- Russian-peasant inner loop for `mulMod`: accumulates `acc + a*b` mod `m` by
    repeatedly halving `b` and doubling `a` (via `addMod`). -/
def mulModAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0,     acc => acc
  | a, b + 1, acc =>
    let acc' := if (b + 1) % 2 = 1 then addMod acc a m else acc
    mulModAux m (addMod a a m) ((b + 1) / 2) acc'

/-- Lean mirror of Rust `fn mul_mod_u128(a, b, m)`. -/
def mulMod (a b m : ℕ) : ℕ :=
  if m = 0 then 0 else mulModAux m (a % m) b 0

end ModInverse
