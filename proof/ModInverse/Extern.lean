/-
  # Trusted external specs for opaque extraction symbols   ★ TRUSTED — part of the TCB ★

  Charon/Aeneas could not lower two pieces of `core` that the *signed* and
  `usize`/`isize` impls call, so the extraction (`extraction/Machine.lean`) emits
  them as opaque `axiom`s with no definition:

    * `core::num::{iN}::unsigned_abs`  — `Machine.lean:25-53`
    * `core::option::{Option<T>}::map` — `Machine.lean:113`

  Nothing can be *proved* about an opaque axiom, so to verify the signed/`usize`/
  `isize` paths we must *postulate* their behaviour. The axioms below are exactly
  those postulates, and they are the only additions to the trusted base beyond the
  Aeneas pipeline itself. They are deliberately isolated in this one file so the
  TCB stays auditable: `#print axioms` on any signed theorem will surface them.

  POLICY — this is the single home for such postulates. Whenever Charon/Aeneas leaves
  a `core`/`std`/`alloc` symbol opaque (a bare `axiom` in `extraction/Machine.lean`,
  no body), its trusted spec goes *here and only here*. Never postulate one inline in
  a proof or refinement file, and never weaken a real definition into an axiom to make
  a proof go through. Each addition expands the TCB, so for every axiom: (1) state it
  as the faithful Rust semantics with a justifying comment, (2) keep it `@[step]` if
  the refinement should pick it up automatically, and (3) ask the human to add it to
  the affected allowlists in the trusted `Gate.lean` — its `#assert_axioms` audit
  fails the build on any axiom it has not approved, including `sorryAx`.

  The unsigned path (`ModInverse.isCorrect`, `modinverse_u128_correct`) does **not**
  depend on this file and stays clean of these axioms.

  Why each postulate is the faithful Rust semantics:

    * `unsigned_abs x = |x|`, in the unsigned type. For `iN`, `|x| ∈ [0, 2^(N-1)]`,
      which fits the unsigned `uN` (`≤ 2^N - 1`), so it never overflows / `fail`s.
    * `Option::map none f = none` and `Option::map (some x) f = some (f x)`, with
      `f` invoked through the `FnOnce::call_once` of the extracted closure.
-/
import Machine

open Aeneas Aeneas.Std Result
open modinverse

namespace ModInverse.Extern

/-! ## `iN::unsigned_abs` returns the natural absolute value and never fails. -/

@[step]
axiom I8.unsigned_abs_spec (x : Std.I8) :
    core.num.I8.unsigned_abs x ⦃ (r : Std.U8) => r.val = x.val.natAbs ⦄

@[step]
axiom I16.unsigned_abs_spec (x : Std.I16) :
    core.num.I16.unsigned_abs x ⦃ (r : Std.U16) => r.val = x.val.natAbs ⦄

@[step]
axiom I32.unsigned_abs_spec (x : Std.I32) :
    core.num.I32.unsigned_abs x ⦃ (r : Std.U32) => r.val = x.val.natAbs ⦄

@[step]
axiom I64.unsigned_abs_spec (x : Std.I64) :
    core.num.I64.unsigned_abs x ⦃ (r : Std.U64) => r.val = x.val.natAbs ⦄

@[step]
axiom I128.unsigned_abs_spec (x : Std.I128) :
    core.num.I128.unsigned_abs x ⦃ (r : Std.U128) => r.val = x.val.natAbs ⦄

/-! ## `Option::map` maps the inner value through the closure's `call_once`. -/

axiom Option_map_none {T U F : Type} (inst : core.ops.function.FnOnce F T U) (f : F) :
    core.option.Option.map inst (none : Option T) f = ok none

axiom Option_map_some {T U F : Type} (inst : core.ops.function.FnOnce F T U) (f : F) (x : T) :
    core.option.Option.map inst (some x) f = (do let y ← inst.call_once f x; ok (some y))

end ModInverse.Extern
