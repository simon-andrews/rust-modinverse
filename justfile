# List recipes.
default:
    @just --list

# Rust checks, as CI runs them: build, test, lint, doc.
check:
    cargo build --all-features
    cargo test --all-features
    cargo clippy --all-targets --all-features -- -D warnings
    cargo doc --no-deps --all-features

# Benchmark the fixed-width inverses (the optimization loop's fitness function).
# On macOS, libc in the criterion dep graph links -liconv, which a nix-provided
# linker won't find without being pointed at the SDK's libraries.
bench:
    #!/usr/bin/env bash
    set -euo pipefail
    if [[ "$(uname)" == "Darwin" ]] && command -v xcrun >/dev/null; then
        export RUSTFLAGS="${RUSTFLAGS:-} -L $(xcrun --show-sdk-path)/usr/lib"
    fi
    cargo bench --bench modinverse

# Build the Lean proof.
prove-correctness:
    cd proof && lake build

# Regenerate the extracted Lean (extraction/Machine.lean) from the Rust source.
extract:
    charon cargo --preset=aeneas
    aeneas -backend lean -loops-to-rec -dest extraction modinverse.llbc || true
    mv extraction/Modinverse.lean extraction/Machine.lean

# Fail if any sorry remains in the proof.
no-sorry:
    ! grep -RnE '\bsorry\b' --include='*.lean' --exclude-dir=.lake proof/ | grep -vF '`sorry`'

# Fail if an axiom appears in the AI workspace outside its one designated TCB home,
# Extern.lean. (The trusted root files are covered by trusted-unchanged instead.)
no-rogue-axioms:
    ! grep -RnE '\baxiom\b' --include='*.lean' proof/ModInverse/ | grep -vF '`axiom`' | grep -v '^proof/ModInverse/Extern.lean:'

# Fail if a trusted file (the spec, the gate, the Extern postulates) changed without
# its pinned hash being deliberately updated alongside it.
trusted-unchanged:
    cd proof && shasum -a 256 --check trusted.sha256
