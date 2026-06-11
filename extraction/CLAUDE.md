# extraction/ — machine-generated Aeneas output

`Machine.lean` is the Aeneas extraction of the real Rust (`src/lib.rs`). **Never hand-edit it.**
Regenerate with `just extract` (Charon produces `modinverse.llbc`; Aeneas lowers it to Lean).

It models `modinverse_uN` / `modinverse_iN` / `usize` / `isize` over `Std.UN`/`Std.IN` in
Aeneas's `Result` monad, with overflow and division-by-zero modelled as `fail`. The proof imports
it as `import Machine` and proves every routine never `fail`s and value-matches the model — see
[`../proof/CLAUDE.md`](../proof/CLAUDE.md).

Two notes that aren't obvious from the file:

- It is named `Machine.lean` (not `Modinverse.lean` as Aeneas emits) because `Modinverse` collides
  with the `ModInverse` proof root on case-insensitive filesystems (macOS). `just extract` does the
  rename.
- Two `core` symbols Aeneas could not lower (`iN::unsigned_abs`, `Option::map`) appear as opaque
  `axiom`s here. Their trusted behaviour is postulated in `proof/ModInverse/Extern.lean`, which is
  part of the TCB.

It lives outside `proof/` on purpose: its one unused generic-egcd `sorry` must not trip the
`just no-sorry` check, which only scans `proof/`.
