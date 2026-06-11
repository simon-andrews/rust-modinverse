# .github/workflows/ — CI

`ci.yml` runs the Rust gate (`just check`) and the Lean gate (`just prove-correctness` +
`just no-sorry`) on every push and PR. `publish.yml` runs `cargo publish` on `v*` tags after
verifying the tag matches the `Cargo.toml` version.

The workflows deliberately delegate to `justfile` recipes so local and CI runs share one
definition — change the recipe, not the workflow, when adjusting what a check does. The Lean job
uses `leanprover/lean-action` only to install elan and restore the mathlib cache (`build: false`);
the build itself is the justfile recipe.

Step `name:` values capitalize the first word.
