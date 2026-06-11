# proof/ — the Lean 4 correctness development

This directory mechanically certifies the crate's fixed-width path. The big-picture map of how
the pieces compose lives in the header comment of `ModInverse.lean` — read it first.

## The human / AI boundary

- **`ModInverse.lean` is human-maintained and trusted — and holds *only the specification*.**
  `ModInverse.Spec.Correct` (what "a correct modular inverse" means) and `HelpersCompute`. No
  algorithm, no proofs. To judge whether the crate is proven correct, read *only* this file: are
  the spec statements the right notion? This is the single immovable anchor — correctness is two
  machine-checked obligations against it (`code ⊑ model`, `model ⊨ Spec.Correct`).
- **`ModInverse/` is AI-written and AI-maintained — including the model.** `Model.lean` is the
  `ℕ` transcription of the Rust; it is a *target*, not trusted (refinement proves the real code
  matches it), so it may be freely rewritten. The rest is the machine-checked proof that the model
  meets the spec and that the extracted machine code refines the model. See
  [`ModInverse/CLAUDE.md`](ModInverse/CLAUDE.md). Do not weaken any spec statement to make a proof
  go through — the statements live in the trusted root.

## Trusted computing base

The proof depends only on Lean's standard axioms plus the postulates in
`ModInverse/Extern.lean` (the `unsigned_abs` / `Option::map` symbols Aeneas left opaque — see
[`../extraction/CLAUDE.md`](../extraction/CLAUDE.md)). The unsigned `u128` result depends on
*none* of the Extern axioms. `ModInverse/Refinement.lean` ends with `#print axioms` calls that
audit this; never let a `sorryAx` appear there.

**`Extern.lean` is the one home for opaque-symbol postulates.** Any `core`/`std`/`alloc` symbol
Charon/Aeneas leaves opaque in `extraction/Machine.lean` gets its trusted spec there and nowhere
else — never inline in a proof, never by weakening a real definition into an axiom. That keeps the
TCB in one auditable place.

## Commands

- `just prove-correctness` (from repo root) — `lake build`. The `lakefile.toml` globs in the
  `ModInverse.*` proof modules explicitly; the root `ModInverse.lean` does not import them, so
  without the glob `lake build` would silently skip every proof.
- `just no-sorry` — there must be no `sorry` anywhere in `proof/`.
- The **lean-lsp MCP** (`.mcp.json`) is the fast way to inspect goals/diagnostics while editing
  proofs — prefer it over repeated `lake build`, which is slow.

## Toolchain

Pinned to `leanprover/lean4:v4.30.0-rc2` with mathlib + Aeneas at matching revisions
(`lean-toolchain`, `lakefile.toml`). The pin is dictated by the Aeneas Lean backend; changing it
means re-pinning all three together.
