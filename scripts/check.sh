#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
TOOLCHAIN="${VERUS_TOOLCHAIN:-1.93.0-x86_64-unknown-linux-gnu}"

usage() {
  cat <<'USAGE'
usage: ./scripts/check.sh [--runtime-only] [--require-verus] [--forbid-rug-normal-deps] [--offline]

options:
  --runtime-only            run only cargo runtime tests; skip Verus verification
  --require-verus           fail instead of skipping when Verus verification cannot run
  --forbid-rug-normal-deps  fail if `rug` appears in the normal dependency graph
  --offline                 run cargo commands in offline mode (`cargo --offline`)
  -h, --help                show this help
USAGE
}

RUNTIME_ONLY=0
REQUIRE_VERUS=0
FORBID_RUG_NORMAL_DEPS=0
OFFLINE=0
while [[ "$#" -gt 0 ]]; do
  case "${1:-}" in
    --runtime-only)
      RUNTIME_ONLY=1
      ;;
    --require-verus)
      REQUIRE_VERUS=1
      ;;
    --forbid-rug-normal-deps)
      FORBID_RUG_NORMAL_DEPS=1
      ;;
    --offline)
      OFFLINE=1
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
  shift
done

if [[ "$RUNTIME_ONLY" == "1" && "$REQUIRE_VERUS" == "1" ]]; then
  echo "error: --runtime-only and --require-verus cannot be used together"
  exit 1
fi

if [[ "$OFFLINE" == "1" ]]; then
  export CARGO_NET_OFFLINE=true
fi

CARGO_CMD=(cargo)
if [[ "$OFFLINE" == "1" ]]; then
  CARGO_CMD+=(--offline)
fi

check_runtime_verified_api_parity() {
  local runtime_impl="$ROOT_DIR/src/runtime_bigint_witness/runtime_impl.rs"
  local verified_impl="$ROOT_DIR/src/runtime_bigint_witness/verified_impl.rs"
  local -a runtime_methods=()
  local -a verified_methods=()
  local missing_in_verified=""
  local missing_in_runtime=""

  mapfile -t runtime_methods < <(rg -No '^\s*pub fn\s+([A-Za-z0-9_]+)\s*\(' -r '$1' "$runtime_impl" | LC_ALL=C sort -u)
  mapfile -t verified_methods < <(rg -No '^\s*pub fn\s+([A-Za-z0-9_]+)\s*\(' -r '$1' "$verified_impl" | LC_ALL=C sort -u)

  if [[ "${#runtime_methods[@]}" -eq 0 || "${#verified_methods[@]}" -eq 0 ]]; then
    echo "error: failed to discover public methods in runtime/verified bigint implementations"
    echo "runtime file: $runtime_impl"
    echo "verified file: $verified_impl"
    exit 1
  fi

  missing_in_verified="$(comm -23 <(printf '%s\n' "${runtime_methods[@]}") <(printf '%s\n' "${verified_methods[@]}"))"
  missing_in_runtime="$(comm -13 <(printf '%s\n' "${runtime_methods[@]}") <(printf '%s\n' "${verified_methods[@]}"))"

  if [[ -n "$missing_in_verified" || -n "$missing_in_runtime" ]]; then
    echo "error: runtime/verified public API mismatch detected"
    if [[ -n "$missing_in_verified" ]]; then
      echo "missing in verified_impl.rs:"
      printf '%s\n' "$missing_in_verified"
    fi
    if [[ -n "$missing_in_runtime" ]]; then
      echo "missing in runtime_impl.rs:"
      printf '%s\n' "$missing_in_runtime"
    fi
    exit 1
  fi
}

skip_or_fail_verus_unavailable() {
  local reason="$1"
  local hint="$2"

  if [[ "$REQUIRE_VERUS" == "1" ]]; then
    echo "[check] error: Verus verification required but unavailable: $reason" >&2
    if [[ -n "$hint" ]]; then
      echo "hint: $hint" >&2
    fi
    exit 1
  fi

  echo "[check] Skipping Verus verification: $reason"
  if [[ -n "$hint" ]]; then
    echo "hint: $hint"
  fi
  exit 0
}

echo "[check] Verifying runtime/verified API parity"
check_runtime_verified_api_parity

echo "[check] Running cargo tests"
"${CARGO_CMD[@]}" test --manifest-path "$ROOT_DIR/Cargo.toml"

if [[ "$FORBID_RUG_NORMAL_DEPS" == "1" ]]; then
  echo "[check] Verifying normal dependency graph excludes rug"
  dep_tree="$("${CARGO_CMD[@]}" tree -e normal --prefix none --manifest-path "$ROOT_DIR/Cargo.toml")"
  if printf '%s\n' "$dep_tree" | rg -q '^rug v'; then
    echo "error: rug appears in the normal dependency graph"
    printf '%s\n' "$dep_tree" | rg '^rug v'
    exit 1
  fi
fi

if [[ "$RUNTIME_ONLY" == "1" ]]; then
  echo "runtime checks complete"
  exit 0
fi

if [[ ! -x "$VERUS_SOURCE/target-verus/release/cargo-verus" ]]; then
  skip_or_fail_verus_unavailable \
    "cargo-verus not found at $VERUS_SOURCE/target-verus/release/cargo-verus" \
    "build Verus tools first (for example via ../VerusCAD/scripts/setup-verus.sh)"
fi

if [[ ! -x "$VERUS_SOURCE/z3" ]]; then
  skip_or_fail_verus_unavailable \
    "z3 not found at $VERUS_SOURCE/z3" \
    "build Verus tools first (for example via ../VerusCAD/scripts/setup-verus.sh)"
fi

echo "[check] Running cargo verus verify"
if command -v rustup >/dev/null 2>&1; then
  export PATH="$VERUS_SOURCE/target-verus/release:$PATH"
  export VERUS_Z3_PATH="$VERUS_SOURCE/z3"
  export RUSTUP_TOOLCHAIN="$TOOLCHAIN"
  cd "$ROOT_DIR"
  "${CARGO_CMD[@]}" verus verify --manifest-path Cargo.toml -p verus-bigint -- --triggers-mode silent
elif command -v nix-shell >/dev/null 2>&1; then
  if nix-shell -p rustup --run "rustup --version >/dev/null 2>&1" >/dev/null 2>&1; then
    OFFLINE_CARGO_FLAG=""
    OFFLINE_EXPORT=""
    if [[ "$OFFLINE" == "1" ]]; then
      OFFLINE_CARGO_FLAG="--offline"
      OFFLINE_EXPORT="export CARGO_NET_OFFLINE=true"
    fi
    nix-shell -p rustup --run "
      set -euo pipefail
      $OFFLINE_EXPORT
      export RUSTUP_TOOLCHAIN='$TOOLCHAIN'
      export PATH='$VERUS_SOURCE/target-verus/release':\$PATH
      export VERUS_Z3_PATH='$VERUS_SOURCE/z3'
      cd '$ROOT_DIR'
      cargo $OFFLINE_CARGO_FLAG verus verify --manifest-path Cargo.toml -p verus-bigint -- --triggers-mode silent
    "
  else
    skip_or_fail_verus_unavailable \
      "rustup is unavailable and nix-shell could not provide it in this environment" \
      "install rustup locally, or use an environment where nix-shell can access the nix daemon"
  fi
else
  skip_or_fail_verus_unavailable \
    "rustup not found in PATH" \
    "install rustup with default toolchain $TOOLCHAIN"
fi
