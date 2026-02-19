#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
TOOLCHAIN="${VERUS_TOOLCHAIN:-1.93.0-x86_64-unknown-linux-gnu}"

usage() {
  cat <<'USAGE'
usage: ./scripts/check.sh [--runtime-only] [--require-verus] [--forbid-rug-normal-deps] [--forbid-trusted-escapes] [--target-a-strict-smoke] [--min-verified N] [--offline]

options:
  --runtime-only            run only cargo runtime tests; skip Verus verification
  --require-verus           fail instead of skipping when Verus verification cannot run
  --forbid-rug-normal-deps  fail if `rug` appears in normal deps or non-test source files
  --forbid-trusted-escapes  fail if non-test source uses trusted proof escapes (`admit`, `assume`, verifier externals, or `#[verifier::truncate]`)
  --target-a-strict-smoke   verify strict-mode guards (default non-Verus build fails; non-Verus `--release --features runtime-compat` fails; Verus verify with `target-a-strict` passes)
  --min-verified N          fail if any Verus run reports fewer than N verified items
  --offline                 run cargo commands in offline mode (`cargo --offline`)
  -h, --help                show this help
USAGE
}

RUNTIME_ONLY=0
REQUIRE_VERUS=0
FORBID_RUG_NORMAL_DEPS=0
FORBID_TRUSTED_ESCAPES=0
TARGET_A_STRICT_SMOKE=0
OFFLINE=0
MIN_VERIFIED=""
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
    --forbid-trusted-escapes)
      FORBID_TRUSTED_ESCAPES=1
      ;;
    --target-a-strict-smoke)
      TARGET_A_STRICT_SMOKE=1
      ;;
    --min-verified)
      if [[ "$#" -lt 2 ]]; then
        echo "error: --min-verified requires an integer argument"
        usage
        exit 1
      fi
      MIN_VERIFIED="${2:-}"
      if ! [[ "$MIN_VERIFIED" =~ ^[0-9]+$ ]]; then
        echo "error: --min-verified expects a nonnegative integer"
        usage
        exit 1
      fi
      shift
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

if [[ "$RUNTIME_ONLY" == "1" && "$TARGET_A_STRICT_SMOKE" == "1" ]]; then
  echo "error: --runtime-only and --target-a-strict-smoke cannot be used together"
  exit 1
fi

if [[ "$RUNTIME_ONLY" == "1" && -n "$MIN_VERIFIED" ]]; then
  echo "error: --runtime-only and --min-verified cannot be used together"
  exit 1
fi

if [[ "$TARGET_A_STRICT_SMOKE" == "1" ]]; then
  REQUIRE_VERUS=1
fi

if [[ "$OFFLINE" == "1" ]]; then
  export CARGO_NET_OFFLINE=true
fi

CARGO_CMD=(cargo)
if [[ "$OFFLINE" == "1" ]]; then
  CARGO_CMD+=(--offline)
fi

normalize_public_return_for_parity() {
  local ret="$1"
  ret="$(printf '%s' "$ret" | tr -d '[:space:]')"

  # Verus exec fns often use named return syntax like `(out: T)`.
  if [[ "$ret" =~ ^\([A-Za-z_][A-Za-z0-9_]*:(.*)\)$ ]]; then
    ret="${BASH_REMATCH[1]}"
  fi

  printf '%s' "$ret"
}

collect_public_fn_signatures() {
  local impl_file="$1"
  local method=""
  local args=""
  local ret=""
  local args_norm=""
  local ret_norm=""

  while IFS='|' read -r method args ret; do
    [[ -z "$method" ]] && continue
    args_norm="$(printf '%s' "$args" | tr -d '[:space:]')"
    ret_norm="$(normalize_public_return_for_parity "$ret")"
    printf '%s\t%s->%s\n' "$method" "$args_norm" "$ret_norm"
  done < <(
    rg -No '^\s*pub fn\s+([A-Za-z0-9_]+)\s*\(([^)]*)\)\s*->\s*([^{]+)' -r '$1|$2|$3' "$impl_file" || true
  )
}

check_runtime_verified_api_parity() {
  local runtime_impl="$ROOT_DIR/src/runtime_bigint_witness/runtime_impl.rs"
  local verified_impl="$ROOT_DIR/src/runtime_bigint_witness/verified_impl.rs"
  local -a runtime_signatures=()
  local -a verified_signatures=()
  local -a runtime_methods=()
  local -a verified_methods=()
  local -A runtime_sig_by_method=()
  local -A verified_sig_by_method=()
  local method=""
  local sig=""
  local missing_in_verified=""
  local missing_in_runtime=""
  local signature_mismatches=""

  mapfile -t runtime_signatures < <(collect_public_fn_signatures "$runtime_impl" | LC_ALL=C sort -u)
  mapfile -t verified_signatures < <(collect_public_fn_signatures "$verified_impl" | LC_ALL=C sort -u)

  if [[ "${#runtime_signatures[@]}" -eq 0 || "${#verified_signatures[@]}" -eq 0 ]]; then
    echo "error: failed to discover public method signatures in runtime/verified bigint implementations"
    echo "runtime file: $runtime_impl"
    echo "verified file: $verified_impl"
    exit 1
  fi

  for sig in "${runtime_signatures[@]}"; do
    method="${sig%%$'\t'*}"
    runtime_methods+=("$method")
    runtime_sig_by_method["$method"]="${sig#*$'\t'}"
  done
  for sig in "${verified_signatures[@]}"; do
    method="${sig%%$'\t'*}"
    verified_methods+=("$method")
    verified_sig_by_method["$method"]="${sig#*$'\t'}"
  done

  mapfile -t runtime_methods < <(printf '%s\n' "${runtime_methods[@]}" | LC_ALL=C sort -u)
  mapfile -t verified_methods < <(printf '%s\n' "${verified_methods[@]}" | LC_ALL=C sort -u)

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

  while IFS= read -r method; do
    [[ -z "$method" ]] && continue
    if [[ "${runtime_sig_by_method[$method]}" != "${verified_sig_by_method[$method]}" ]]; then
      signature_mismatches+="$method"$'\n'
      signature_mismatches+="  runtime:  ${runtime_sig_by_method[$method]}"$'\n'
      signature_mismatches+="  verified: ${verified_sig_by_method[$method]}"$'\n'
    fi
  done < <(printf '%s\n' "${runtime_methods[@]}")

  if [[ -n "$signature_mismatches" ]]; then
    echo "error: runtime/verified public API signature mismatch detected"
    printf '%s' "$signature_mismatches"
    exit 1
  fi
}

check_no_rug_in_non_test_sources() {
  local matches=""
  matches="$(
    rg -n \
      --color never \
      --glob '!**/tests.rs' \
      --glob '!**/test_*.rs' \
      --glob '!**/tests/**' \
      -e '\brug::' \
      -e 'extern\s+crate\s+rug\b' \
      "$ROOT_DIR/src" || true
  )"

  if [[ -n "$matches" ]]; then
    echo "error: non-test source files reference rug"
    printf '%s\n' "$matches"
    exit 1
  fi
}

check_no_trusted_escapes_in_non_test_sources() {
  local matches=""
  matches="$(
    rg -n \
      --color never \
      --glob '!**/tests.rs' \
      --glob '!**/test_*.rs' \
      --glob '!**/tests/**' \
      -e '\badmit\s*\(' \
      -e '\bassume\s*\(' \
      -e '#\s*\[\s*verifier::external(_body|_fn_specification|_type_specification)?\b' \
      -e '#\s*\[\s*verifier::truncate\b' \
      "$ROOT_DIR/src" || true
  )"

  if [[ -n "$matches" ]]; then
    echo "error: non-test source files use trusted proof escapes"
    printf '%s\n' "$matches"
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

run_cargo_verus_verify() {
  local feature_flags="${1:-}"

  if command -v rustup >/dev/null 2>&1; then
    export PATH="$VERUS_SOURCE/target-verus/release:$PATH"
    export VERUS_Z3_PATH="$VERUS_SOURCE/z3"
    export RUSTUP_TOOLCHAIN="$TOOLCHAIN"
    cd "$ROOT_DIR"
    if [[ -n "$feature_flags" ]]; then
      # shellcheck disable=SC2086
      "${CARGO_CMD[@]}" verus verify --manifest-path Cargo.toml -p verus-bigint $feature_flags -- --triggers-mode silent
    else
      "${CARGO_CMD[@]}" verus verify --manifest-path Cargo.toml -p verus-bigint -- --triggers-mode silent
    fi
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
        cargo $OFFLINE_CARGO_FLAG verus verify --manifest-path Cargo.toml -p verus-bigint $feature_flags -- --triggers-mode silent
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
}

verify_verus_summary_threshold() {
  local log_file="$1"
  local threshold="$2"
  local summary=""
  local verified_count=""
  local error_count=""

  summary="$(rg -No 'verification results::\s*([0-9]+) verified,\s*([0-9]+) errors' -r '$1|$2' "$log_file" | tail -n 1 || true)"
  if [[ -z "$summary" ]]; then
    echo "error: could not parse Verus verification summary"
    cat "$log_file"
    exit 1
  fi

  verified_count="${summary%%|*}"
  error_count="${summary##*|}"
  if ! [[ "$verified_count" =~ ^[0-9]+$ && "$error_count" =~ ^[0-9]+$ ]]; then
    echo "error: malformed Verus verification summary: $summary"
    cat "$log_file"
    exit 1
  fi

  if (( error_count != 0 )); then
    echo "error: Verus verification summary reported nonzero errors: $error_count"
    cat "$log_file"
    exit 1
  fi

  if (( verified_count < threshold )); then
    echo "error: Verus verified-count regression: expected at least $threshold, got $verified_count"
    cat "$log_file"
    exit 1
  fi

  echo "[check] Verus verified-count gate passed ($verified_count >= $threshold)"
}

run_cargo_verus_verify_with_threshold() {
  local feature_flags="${1:-}"
  local verus_log=""
  local verus_status=0

  if [[ -z "$MIN_VERIFIED" ]]; then
    run_cargo_verus_verify "$feature_flags"
    return
  fi

  verus_log="$(mktemp)"
  set +e
  run_cargo_verus_verify "$feature_flags" 2>&1 | tee "$verus_log"
  verus_status="${PIPESTATUS[0]}"
  set -e

  if (( verus_status != 0 )); then
    rm -f "$verus_log"
    exit "$verus_status"
  fi

  verify_verus_summary_threshold "$verus_log" "$MIN_VERIFIED"
  rm -f "$verus_log"
}

echo "[check] Verifying runtime/verified API parity"
check_runtime_verified_api_parity

echo "[check] Running cargo tests (runtime-compat)"
"${CARGO_CMD[@]}" test --manifest-path "$ROOT_DIR/Cargo.toml" --features runtime-compat

if [[ "$FORBID_RUG_NORMAL_DEPS" == "1" ]]; then
  echo "[check] Verifying normal dependency graph excludes rug"
  dep_tree="$("${CARGO_CMD[@]}" tree -e normal --prefix none --manifest-path "$ROOT_DIR/Cargo.toml")"
  if printf '%s\n' "$dep_tree" | rg -q '^rug v'; then
    echo "error: rug appears in the normal dependency graph"
    printf '%s\n' "$dep_tree" | rg '^rug v'
    exit 1
  fi

  echo "[check] Verifying non-test source tree excludes rug"
  check_no_rug_in_non_test_sources
fi

if [[ "$FORBID_TRUSTED_ESCAPES" == "1" ]]; then
  echo "[check] Verifying non-test source tree excludes trusted proof escapes"
  check_no_trusted_escapes_in_non_test_sources
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
run_cargo_verus_verify_with_threshold ""

if [[ "$TARGET_A_STRICT_SMOKE" == "1" ]]; then
  echo "[check] Verifying target-a-strict rejects non-Verus cargo builds"
  strict_smoke_log="$(mktemp)"
  set +e
  "${CARGO_CMD[@]}" test --manifest-path "$ROOT_DIR/Cargo.toml" --no-run >"$strict_smoke_log" 2>&1
  strict_smoke_status="$?"
  set -e

  if [[ "$strict_smoke_status" == "0" ]]; then
    echo "error: expected non-Verus cargo build (default strict mode) to fail, but it succeeded"
    cat "$strict_smoke_log"
    rm -f "$strict_smoke_log"
    exit 1
  fi

  if ! rg -q 'feature `target-a-strict` requires a Verus build' "$strict_smoke_log"; then
    echo "error: strict-mode smoke failure did not match the expected compile guard"
    cat "$strict_smoke_log"
    rm -f "$strict_smoke_log"
    exit 1
  fi
  rm -f "$strict_smoke_log"

  echo "[check] Verifying runtime-compat rejects non-Verus release builds"
  runtime_compat_release_log="$(mktemp)"
  set +e
  "${CARGO_CMD[@]}" build --manifest-path "$ROOT_DIR/Cargo.toml" --release --features runtime-compat >"$runtime_compat_release_log" 2>&1
  runtime_compat_release_status="$?"
  set -e

  if [[ "$runtime_compat_release_status" == "0" ]]; then
    echo "error: expected non-Verus release build with runtime-compat to fail, but it succeeded"
    cat "$runtime_compat_release_log"
    rm -f "$runtime_compat_release_log"
    exit 1
  fi

  if ! rg -q 'feature `runtime-compat` is debug/test-only in non-Verus builds' "$runtime_compat_release_log"; then
    echo "error: runtime-compat release guard failure did not match the expected compile guard"
    cat "$runtime_compat_release_log"
    rm -f "$runtime_compat_release_log"
    exit 1
  fi
  rm -f "$runtime_compat_release_log"

  echo "[check] Running cargo verus verify with target-a-strict feature"
  run_cargo_verus_verify_with_threshold "--features target-a-strict"
fi
