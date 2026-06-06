# List recipes.
default:
    @just --list

# Rust checks, as CI runs them: build, test, lint.
check:
    cargo build --all-features
    cargo test --all-features
    cargo clippy --all-targets --all-features -- -D warnings

# Build the Lean proof.
prove-correctness:
    cd proof && lake build

# Regenerate the extracted Lean (extraction/Machine.lean) from the Rust source.
# aeneas names its output after the crate; rename to the `Machine` module the proof
# imports (it can't be `Modinverse` — that collides with `ModInverse` on macOS).
extract:
    charon cargo --preset=aeneas
    aeneas -backend lean -loops-to-rec -dest extraction modinverse.llbc || true
    mv extraction/Modinverse.lean extraction/Machine.lean

# Fail if any sorry remains in the proof.
no-sorry:
    ! grep -RnE '\bsorry\b' --include='*.lean' --exclude-dir=.lake proof/ | grep -vF '`sorry`'
