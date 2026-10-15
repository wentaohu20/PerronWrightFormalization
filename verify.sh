#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v lake >/dev/null 2>&1; then
  echo 'Lake/Elan is required: https://lean-lang.org/install/' >&2
  exit 1
fi
mkdir -p .verification
if grep -REn --include='*.lean' '^[[:space:]]*((private|protected)[[:space:]]+)?(axiom|unsafe|opaque|sorry|admit)[[:space:]]|:=[[:space:]]*(sorry|admit)([[:space:]]|$)|skipKernelTC|sorryAx' PerronWright; then
  echo 'Forbidden proof placeholder or kernel bypass in proof sources.' >&2
  exit 1
fi
check_diagnostics() {
  if grep -Eiq '(^|[[:space:]])(error|warning)(\([^)]*\))?:' "$1"; then
    echo "Verification diagnostic: see $1" >&2
    exit 1
  fi
}
run_logged() {
  local label="$1" log="$2"
  shift 2
  printf '\n=== %s ===\n' "$label"
  if "$@" >"$log" 2>&1; then
    check_diagnostics "$log"
    printf 'OK (full output saved to %s)\n' "$log"
  else
    local code=$?
    printf '%s failed (exit %s); see %s\n' "$label" "$code" "$log" >&2
    exit "$code"
  fi
}
if [[ "${SKIP_CACHE:-0}" != 1 ]]; then
  run_logged 'Fetch pinned mathlib cache' .verification/cache.log lake exe cache get
fi
run_logged 'Build PerronWright library target' .verification/build.log lake build PerronWright
rm -f .verification/main-theorem-dependencies.json .verification/main-theorem-axioms.txt
run_logged 'Inspect Lean declarations and export dependencies' .verification/main-theorem-dependencies.log lake env lean MainTheoremDependencies.lean
test -s .verification/main-theorem-dependencies.json
grep -q '^DEPENDENCY AUDIT PASSED: 4 paper main theorems; 21 audited Lean declarations (17 implementation + 4 supporting);' .verification/main-theorem-dependencies.log
test -s .verification/main-theorem-axioms.txt
test "$(grep -Ec "^'PerronWright\.[^']+' (depends on axioms:|does not depend on any axioms)" .verification/main-theorem-axioms.txt)" -eq 17
if [[ "${FULL_AUDIT:-0}" == 1 ]]; then
  for audit in Audit.lean ProbabilityAudit.lean Chapter3FiniteProcessSpatialBridgeAudit.lean; do
    run_logged "Full axiom audit: $audit" ".verification/$audit.log" lake env lean "$audit"
  done
fi
printf '\n'
cat .verification/main-theorem-axioms.txt
printf '\nVerification completed. Reports: .verification/\n'
