# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A small `no_std` Rust library (`modinverse`) for modular multiplicative inverses and the
extended Euclidean algorithm. Its distinguishing feature is that the fixed-width path is
**mechanically verified**: the Rust is extracted to Lean 4 (via Charon + Aeneas) and proved
to refine a naturals model that is itself proved correct. This is a for-fun / learn-Lean
project — proof depth is the point, not user count.

The repository is two intertwined codebases:

- **`src/`** — the Rust crate. One algorithm runs across every integer width. See
  [`src/CLAUDE.md`](src/CLAUDE.md).
- **`proof/`** — the Lean 4 development that certifies it. See [`proof/CLAUDE.md`](proof/CLAUDE.md).
- **`extraction/`** — the machine-generated bridge between them (Aeneas output). See
  [`extraction/CLAUDE.md`](extraction/CLAUDE.md).

## Progressive disclosure (preference)

CLAUDE.md files live in **every** significant directory, not just here. Keep content where it
belongs and avoid duplication: a higher-level file gives the big picture and links down; a
lower-level file owns the detail for its directory. When you add guidance, put it in the
deepest directory it applies to and reference it from above rather than copying it up.

## Commands

All routine work goes through the `justfile` (run `just` for the list); CI calls the same
recipes, so local and CI behaviour stay identical.

- `just check` — the full Rust gate: `cargo build`, `cargo test`, `cargo clippy -D warnings`,
  `cargo doc`, all with `--all-features`.
- `just prove-correctness` — build the Lean proof (`cd proof && lake build`).
- `just no-sorry` — fail if any `sorry` remains in `proof/`.
- `just extract` — regenerate `extraction/Machine.lean` from the Rust (needs `charon` + `aeneas`
  installed). Only run when `src/lib.rs` changes.

Run a single Rust test: `cargo test --all-features <test_name>` (e.g. `cargo test modinverse_i128_m_min`).
The `bigint` feature gates several tests, so pass `--all-features` (or `--features bigint`) to
exercise them.

## CI

`.github/workflows/ci.yml` runs the Rust and Lean gates on every push/PR; `publish.yml` runs
`cargo publish` on `v*` tags after checking the tag matches `Cargo.toml`. See
[`.github/workflows/CLAUDE.md`](.github/workflows/CLAUDE.md).
