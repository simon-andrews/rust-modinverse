/-
  # The algorithm under verification, as an `ℕ` model      ☆ AI-MAINTAINED ☆

  TRANSLATION LAYER. The definitions below are a hand translation of the fixed-width
  modular-inverse code in `src/lib.rs` into Lean over `ℕ`. Their faithfulness is
  **not** taken on inspection: `ModInverse/Refinement/` proves that the Aeneas
  extraction of the real Rust refines this model for every width. So the model is a
  *target* the machine code is matched against — and because that match
  (`code ⊑ model`) and the spec (`model ⊨ Spec.Correct`, in `Proofs.lean`) are both
  machine-checked against the frozen `ModInverse.Spec` in the root, this file may be
  rewritten freely: any version that still discharges both obligations is correct.
  Only the spec is human-owned and trusted.

  Every fixed-width type runs the *same* per-step-reduced extended Euclidean
  algorithm, so one `ℕ` model serves them all. The arithmetic core (`subMod`, `step`,
  `loop`, `modinverse`) is width-independent. `addMod`/`mulMod` model the two
  overflow-avoiding `u128` helpers (narrow widths multiply by widening instead).

  Rust → Lean mapping:

      inline `if a≥b {a-b} else {(m-b)+a}`   def subMod
      fn add_mod_u128(a, b, m)               def addMod
      fn mul_mod_u128(a, b, m)               def mulMod  (via mulModAux)
      one loop iteration                     def step
      `while r_next != 0 {...}`              def loop  (well-founded recursion on rNext)
      `<u128 as ModInverse>::modinverse`     def modinverse

  Rust is fixed-width unsigned; this model is `ℕ`. The unsigned cores never overflow,
  so a `ℕ` model captures the relevant semantics — and that no-overflow fact is
  discharged by the refinement (the machine code is proved never to `fail`), not
  asserted by inspection.
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq

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

/-! ## Extended gcd. Mirror of Rust `pub fn egcd_u64`. -/

/-- Lean mirror of Rust `pub fn egcd_u64(a, b) -> (u64, i128, i128)`: the gcd plus
    an exact Bézout certificate `(x, y)`, with `x` the canonical coefficient in
    `[0, b)` (it is the same `s` the inverse loop tracks) and
    `y = (g - a*x) / b` the determined integer cofactor. Note the `s = 0` case
    needs no special handling here: `b` divides `g` exactly then, so the division
    yields the right `y` (`= 1`) on its own. -/
def egcd (a b : ℕ) : ℕ × ℤ × ℤ :=
  if hb : 1 < b then
    let init : State b :=
      { r := b, rNext := a % b, s := 0, sNext := 1,
        sLt := by omega, sNextLt := hb }
    let p := loop (by omega) init
    (p.1, (p.2 : ℤ), ((p.1 : ℤ) - (a : ℤ) * (p.2 : ℤ)) / (b : ℤ))
  else if b = 1 then (1, 0, 1)
  else (a, 1, 0)

end ModInverse
