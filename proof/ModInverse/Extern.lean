/-
  # Trusted external specs for opaque extraction symbols   ★ TRUSTED — part of the TCB ★

  **Currently empty: the extraction contains no opaque symbols.** Every `core` function
  the verified Rust paths call is spelled in a form Charon/Aeneas lowers to real
  definitions (e.g. `|x|` is a cast plus `wrapping_sub`, and `Option` values are
  rebuilt with a `match` rather than `Option::map`), so nothing about the machine code
  is postulated and every certificate depends only on Lean's three standard axioms.

  POLICY — this file is the single designated home for such postulates, should one
  ever become necessary again. Whenever Charon/Aeneas leaves a `core`/`std`/`alloc`
  symbol opaque (a bare `axiom` in `extraction/Machine.lean`, no body), its trusted
  spec goes *here and only here*. Never postulate one inline in a proof or refinement
  file, and never weaken a real definition into an axiom to make a proof go through.
  Each addition expands the TCB, so for every axiom: (1) state it as the faithful Rust
  semantics with a justifying comment, (2) keep it `@[step]` if the refinement should
  pick it up automatically, and (3) ask the human to add it to the affected allowlists
  in the trusted `Gate.lean` — its `#assert_axioms` audit fails the build on any axiom
  it has not approved, including `sorryAx`. Also prefer the alternative that keeps this
  file empty: rewriting the Rust inside the lowerable subset, as was done for
  `unsigned_abs` and `Option::map`.

  (`just no-rogue-axioms` polices that axioms appear nowhere else in the AI workspace;
  this file is hash-pinned by `just trusted-unchanged` like the spec and the gate.)
-/
