#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
TOOLCHAIN="${VERUS_TOOLCHAIN:-1.93.0-x86_64-unknown-linux-gnu}"

usage() {
  cat <<'USAGE'
usage: ./scripts/check.sh [--runtime-only]

options:
  --runtime-only   run only cargo runtime tests; skip Verus verification
  -h, --help       show this help
USAGE
}

RUNTIME_ONLY=0
case "${1:-}" in
  "")
    ;;
  --runtime-only)
    RUNTIME_ONLY=1
    ;;
  -h|--help)
    usage
    exit 0
    ;;
  *)
    echo "error: unknown argument '$1'"
    usage
    exit 1
    ;;
esac

echo "[1/2] Running cargo tests"
cargo test --manifest-path "$ROOT_DIR/Cargo.toml"

if [[ "$RUNTIME_ONLY" == "1" ]]; then
  echo "runtime checks complete"
  exit 0
fi

if [[ ! -x "$VERUS_SOURCE/target-verus/release/cargo-verus" ]]; then
  echo "[2/2] Skipping Verus verification: cargo-verus not found at $VERUS_SOURCE/target-verus/release/cargo-verus"
  echo "hint: build Verus tools first (for example via ../VerusCAD/scripts/setup-verus.sh)"
  exit 0
fi

if [[ ! -x "$VERUS_SOURCE/z3" ]]; then
  echo "[2/2] Skipping Verus verification: z3 not found at $VERUS_SOURCE/z3"
  echo "hint: build Verus tools first (for example via ../VerusCAD/scripts/setup-verus.sh)"
  exit 0
fi

echo "[2/2] Running cargo verus verify"
if command -v rustup >/dev/null 2>&1; then
  export PATH="$VERUS_SOURCE/target-verus/release:$PATH"
  export VERUS_Z3_PATH="$VERUS_SOURCE/z3"
  export RUSTUP_TOOLCHAIN="$TOOLCHAIN"
  cd "$ROOT_DIR"
  cargo verus verify --manifest-path Cargo.toml -p verus-bigint -- --triggers-mode silent
elif command -v nix-shell >/dev/null 2>&1; then
  if nix-shell -p rustup --run "rustup --version >/dev/null 2>&1" >/dev/null 2>&1; then
    nix-shell -p rustup --run "
      set -euo pipefail
      export RUSTUP_TOOLCHAIN='$TOOLCHAIN'
      export PATH='$VERUS_SOURCE/target-verus/release':\$PATH
      export VERUS_Z3_PATH='$VERUS_SOURCE/z3'
      cd '$ROOT_DIR'
      cargo verus verify --manifest-path Cargo.toml -p verus-bigint -- --triggers-mode silent
    "
  else
    echo "[2/2] Skipping Verus verification: rustup is unavailable and nix-shell could not provide it in this environment"
    echo "hint: install rustup locally, or use an environment where nix-shell can access the nix daemon"
    exit 0
  fi
else
  echo "[2/2] Skipping Verus verification: rustup not found in PATH"
  echo "hint: install rustup with default toolchain $TOOLCHAIN"
  exit 0
fi
