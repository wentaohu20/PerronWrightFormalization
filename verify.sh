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
if [[ "${SKIP_CACHE:-0}" != 1 ]]; then
  lake exe cache get 2>&1 | tee .verification/cache.log
  check_diagnostics .verification/cache.log
fi
lake build PerronWright 2>&1 | tee .verification/build.log
check_diagnostics .verification/build.log
rm -f .verification/main-theorem-dependencies.json
lake env lean MainTheoremDependencies.lean 2>&1 | tee .verification/main-theorem-dependencies.log
check_diagnostics .verification/main-theorem-dependencies.log
test -s .verification/main-theorem-dependencies.json
grep -q '^DEPENDENCY AUDIT PASSED: 4 paper main theorems; 21 audited Lean declarations (17 implementation + 4 supporting);' .verification/main-theorem-dependencies.log
if [[ "${FULL_AUDIT:-0}" == 1 ]]; then
  for audit in Audit.lean ProbabilityAudit.lean Chapter3FiniteProcessSpatialBridgeAudit.lean; do
    lake env lean "$audit" 2>&1 | tee ".verification/$audit.log"
    check_diagnostics ".verification/$audit.log"
  done
fi
echo 'VERIFIED: paper Theorems 3.6, 3.8, 3.9 and 3.10; 17 implementation + 4 supporting Lean declarations. Reports: .verification/'
