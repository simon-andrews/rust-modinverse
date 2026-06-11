# proof/ModInverse/ — the machine-checked proof (AI-maintained)

Everything here is AI-written and AI-maintained, checked by the Lean kernel. It discharges the
spec in the trusted root `../ModInverse.lean` (see [`../CLAUDE.md`](../CLAUDE.md)) and proves the
extracted machine code refines the model. Each file opens with a header explaining its role; this
is the index.

**You own this directory's structure.** The layout below is the current state, not a mandate —
split, merge, rename, or rethink the proof however works best. The only fixed contracts are the
spec in `../ModInverse.lean`, the gate in `../Gate.lean` (it re-types the 15 certificates —
`Refinement.modinverse_*_correct` and `Refinement.egcd_u64_correct` — at frozen statements and
audits their axiom closures, build-failingly, so those 15 names and types must keep existing),
and the discipline at the bottom (no `sorry`; no axioms outside `Extern.lean`).

The **model itself lives here**, not in the trusted root: `Model.lean` is the `ℕ` transcription of
`src/lib.rs`. It is a *target*, not trusted — refinement proves the real code matches it — so it
may be freely rewritten as long as both obligations below still discharge against the frozen spec.

## Two halves

**Model meets spec** — pure `ℕ`/`ZMod` mathematics:

- `Model.lean` — the algorithm under verification, the `ℕ` translation of the Rust (definitions
  only). The shared target for every width; the `code ⊑ model` half of correctness points at it.
- `Proofs.lean` — the model satisfies `Spec.Correct`. Strategy: a loop invariant stated in
  `ZMod m` (so per-step `% m` reductions vanish), translated back to `Nat` congruences at the end.
  Ends in the certificates `isCorrect : Spec.Correct modinverse`, `helpersCompute`, and
  `isEgcdCorrect : Spec.EgcdCorrect egcd`.
- `Signed.lean` — the `[0, |m|)` canonicalization (`reduceSigned`) the signed wrappers perform,
  plus the ℕ/ℤ bridge lemmas. Plain Mathlib reasoning, not Aeneas.

**Machine code refines model** — over the Aeneas extraction:

- `Refinement/` — every `modinverse_{u,i}N` / `usize` / `isize` never errors and value-matches the
  model, then composes with `isCorrect` into the per-width certificates `modinverse_*_correct`.
  This is the Aeneas-tactic half; it has its own conventions, see
  [`Refinement/CLAUDE.md`](Refinement/CLAUDE.md).
- `Refinement.lean` — aggregates the `Refinement/*` modules.
- `Extern.lean` — **★ TRUSTED ★** the designated home for postulated specs of `core`/`std`
  symbols Aeneas leaves opaque. **Currently empty** — the Rust is written inside the lowerable
  subset, so nothing is postulated. Any future opaque symbol's spec goes here and nowhere else.

Composing refinement (machine refines model) with `isCorrect` (model meets spec) certifies the
real extracted code — that composition is the 14 `modinverse_*_correct` certificates, one per
public `ModInverse` impl, which the trusted `../Gate.lean` re-types and audits.

## Discipline

- **No `sorry`, no new `axiom`.** The only axioms in the whole development are `Extern.lean`'s;
  anything else (especially `sorryAx`) fails the `#assert_axioms` audit in `../Gate.lean`.
- **Certificates are `structure` instances.** Because `Spec.Correct` is a structure, a certificate
  fails to typecheck unless every field is discharged at *exactly* its declared type — proofs
  cannot silently drift from the statements. To add a guarantee, add a `Spec` field in the root;
  the obligation then appears here mechanically.
