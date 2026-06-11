# proof/ — the Lean 4 correctness development

This directory mechanically certifies the crate's fixed-width path. The big-picture map of how
the pieces compose lives in the header comment of `ModInverse.lean` — read it first.

## The human / AI boundary

- **`Gate.lean` is human-maintained and trusted — the enforcement.** It re-types the 14
  end-to-end certificates (`Refinement.modinverse_*_correct`) at frozen statements written in
  trusted vocabulary only (extracted machine code + arithmetic, never the model), and its
  `#assert_axioms` command fails the build if a certificate's axiom closure strays outside an
  explicit allowlist. The only AI-workspace names it pins are those 14 certificates.
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

Every certificate depends on exactly Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`): the extraction has no opaque symbols, so nothing about the
machine code is postulated and `ModInverse/Extern.lean` is empty. It stays as the one
designated home should a future opaque symbol need a trusted spec — see its header for the
policy. `Gate.lean` audits all this mechanically: `#assert_axioms` fails the build on any
axiom outside its per-certificate allowlists, `sorryAx` included.

**`Extern.lean` is the one home for opaque-symbol postulates.** Any `core`/`std`/`alloc` symbol
Charon/Aeneas leaves opaque in `extraction/Machine.lean` gets its trusted spec there and nowhere
else — never inline in a proof, never by weakening a real definition into an axiom. That keeps the
TCB in one auditable place.

## Commands

- `just prove-correctness` (from repo root) — `lake build`. The `lakefile.toml` globs in the
  `ModInverse.*` proof modules explicitly; the root `ModInverse.lean` does not import them, so
  without the glob `lake build` would silently skip every proof.
- `just no-sorry` — there must be no `sorry` anywhere in `proof/`.
- `just no-rogue-axioms` — no `axiom` in the AI workspace outside `ModInverse/Extern.lean`.
- `just trusted-unchanged` — the trusted files (spec, gate, Extern) must match their pinned
  hashes in `proof/trusted.sha256`; a human edit to a trusted file updates the hash with it.
- The **lean-lsp MCP** (`.mcp.json`) is the fast way to inspect goals/diagnostics while editing
  proofs — prefer it over repeated `lake build`, which is slow.

## Toolchain

Pinned to `leanprover/lean4:v4.30.0-rc2` with mathlib + Aeneas at matching revisions
(`lean-toolchain`, `lakefile.toml`). The pin is dictated by the Aeneas Lean backend; changing it
means re-pinning all three together.
