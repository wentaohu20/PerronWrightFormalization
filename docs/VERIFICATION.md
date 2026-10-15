# Verification record

This record accompanies the first public-release baseline. It describes
actual local tests, not a substitute for running verification on a checkout.

## Tested entry: 2026-10-15 (Asia/Shanghai)

```powershell
.\Verify.ps1 -SkipCache
```

This entry returned exit code `0` under PowerShell 7. The pinned dependencies
and cache were already present; a fresh checkout should normally omit
`-SkipCache`.

| Item | Observed result |
| --- | --- |
| Library target | `PerronWright` and its transitive imports built successfully (5,356 jobs) |
| Paper main theorems | Four: 3.6, 3.8, 3.9, and 3.10 |
| Distinct main-theorem implementation declarations | 17: two for 3.6, fourteen for 3.8, and one joint declaration for 3.9 and 3.10 |
| Supporting declarations checked in the dependency export | Four Brownian factorial-density and determinacy results |
| Dependency export | 21 checked declarations and 88,559 reachable type/proof constants; no unknown nodes |
| Console output | 17 complete native `#print axioms` messages with fully qualified Lean names |
| Axioms | Only `propext`, `Classical.choice`, and `Quot.sound` |
| Build and inspection diagnostics | No Lean errors or warnings |

The entry checks that every main-theorem implementation name appears once
and that its native axiom list agrees with the JSON dependency record.
The saved native messages were also compared with Lean's actual standard
output, preserving wrapped lines without regrouping declarations.

## Scope and platform limits

The default entry builds the imported proof library. This is not a claim
that every separately stored auxiliary audit module is compiled by that
target. The main theorem declarations and their proof dependencies are
covered by the library build and dependency inspection.

Both Windows PowerShell 5 and PowerShell 7 passed the existing five
output-handler/error-exit tests. PowerShell 5 parsed the updated entry
without syntax errors, and Bash `-n verify.sh` passed. These handler tests
use ASCII test strings. A full run of the current entry under PowerShell 5,
Linux, or macOS, or a fresh-clone build, is not claimed here.

The optional `-FullAudit` mode runs `Audit.lean`, `ProbabilityAudit.lean`,
and `Chapter3FiniteProcessSpatialBridgeAudit.lean`. These extra audit runs
are not part of the default-entry test recorded above.

## Reproducible reports

Complete local outputs are written to `.verification/` and are not committed.
They include the build log, native axiom messages, the JSON dependency graph
(approximately 170 MB), and the generated definition index. Previous main
reports are removed before inspection, so a failed run cannot be accepted
through stale reports.

The [README](../README.md) explains the verification entries and links each
main theorem to its semantic definitions. The generated
[definition index](MAIN_THEOREM_DEFINITIONS.md) expands the reachable project
definitions. These records do not replace the assumptions in the actual
Lean statements, including compact `QP`, finite type-count bounds, and the
empirical spectral-drift premise for the unnormalized countable model.
