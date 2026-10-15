# Reproducible verification record

Original full-audit date: 2026-10-12 (Asia/Shanghai). This page records actual local runs and the current output format. To verify a checkout, use the repository's one-command entry rather than relying on this record.

## Native-output rerun: 2026-10-15

`./Verify.ps1 -SkipCache` returned exit code `0` under PowerShell 7. The full library build completed successfully (5,356 jobs), followed by the complete 21-declaration dependency export. The console displayed 17 native `#print axioms` messages with distinct fully qualified implementation names, preserving all wrapped lines. The entry checked each name and axiom set against the JSON report; all used only `propext`, `Classical.choice`, and `Quot.sound`.

Both Windows PowerShell 5 and PowerShell 7 passed the five existing output-handler/error-exit tests. PowerShell 5 also parsed the updated entry without syntax errors, and Bash `-n verify.sh` passed. A full rerun of the updated entry under PowerShell 5 or Linux/macOS is not claimed. The mathematical proof sources were unchanged.

## Original full-audit runs: 2026-10-12

```powershell
.\Verify.ps1 -SkipCache -FullAudit
.\verify.cmd -SkipCache
```

Both entries returned exit code `0`. After correcting the paper-to-Lean mapping, `verify.cmd -SkipCache` was run again and returned `0`, checking all 21 distinct Lean audit targets. That historical run used the grouped console format, which has since been removed. The mathematical sources were unchanged by that correction.

The pinned dependencies and cache were already available locally, so these runs used `-SkipCache`. The default cache-fetching step was also checked successfully. A fresh clone should normally use the default entry. PowerShell and Bash entry syntax was checked; a full Linux/macOS execution is not claimed.

## Results

| Item | Observed result |
| --- | --- |
| Mathematical proof sources | All 1,663 Lean files under `PerronWright/` are included |
| Full build | `Build completed successfully (5356 jobs).` |
| Paper main theorems | **Four: Theorems 3.6, 3.8, 3.9, and 3.10** |
| Distinct implementation/specialization declarations | 17: two for 3.6, fourteen for 3.8, and one joint terminal for both 3.9 and 3.10 |
| Supporting declarations | Four Brownian factorial-density and determinacy results; not additional main theorems |
| Checked Lean audit targets | 21 in total; actual checked proof expressions were read and their direct type/proof dependencies exported |
| Transitive closure of type and proof constants | 88,559 declarations; no unknown or uninspectable nodes |
| Axioms | Only `propext`, `Classical.choice`, and `Quot.sound`; no nonstandard axioms found |
| Additional audits | `Audit.lean`, `ProbabilityAudit.lean`, and `Chapter3FiniteProcessSpatialBridgeAudit.lean` all passed |
| Build and audit diagnostics | No Lean errors or warnings found |
| Generated definition locations | Lean's one-based identifier positions are used; density, finite-model, and compact-terminal locations were checked against the source |

## Native Lean console output and Windows encoding

The console now displays the actual built-in `#print axioms` messages for the 17 distinct main-theorem implementation declarations. Each message contains the declaration's fully qualified Lean name and its own axiom dependencies. The joint declaration for Theorems 3.9 and 3.10 appears once. There are no paper-number axiom unions, renamed declarations, or wrapper theorems.

`MainTheoremDependencies.lean` invokes Lean's command for each declaration and saves each complete native message to `.verification/main-theorem-axioms.txt`. The verification entry replays that file without rewriting it or selecting only the first line of a wrapped message. Windows also checks that all 17 names appear exactly once and that each axiom set agrees with the checked JSON record. The complete 21-declaration audit remains in the JSON, including the four supporting Brownian results.

The inspection program does not manually generate text imitating `#print axioms`, combine the dependencies of several declarations, or replace Lean names with paper theorem numbers. Paper numbering remains only in the documentation and structured report as a navigation aid.

The earlier Windows PowerShell 5 and PowerShell 7 full runs checked UTF-8 log decoding without replacement characters. Both shells also passed output-handler tests for successful native stderr, nonzero native exit, script error, warning diagnostic, and terminating script error; failure cases retained their logs. PowerShell 5 successfully parsed the actual approximately 170 MB UTF-8 JSON report, with four paper groups, 21 checked targets, and 88,559 reachable declarations. These historical runs do not by themselves test the new native-console presentation. Full Linux/macOS execution is not claimed.

The dependency-export log retains the completion record:

```text
DEPENDENCY AUDIT PASSED: 4 paper main theorems; 21 audited Lean declarations (17 implementation + 4 supporting); 88559 reachable constants. Reports: .verification/
```

Complete local outputs are in `.verification/`. The full JSON dependency graph (approximately 170 MB) and compilation caches are not committed. The smaller project-definition index is preserved in [MAIN_THEOREM_DEFINITIONS.md](MAIN_THEOREM_DEFINITIONS.md). JSON schema v2 records the four paper groups, each declaration's role, and its paper theorem number(s); the shared countable terminal belongs to both 3.9 and 3.10 and is inspected only once. Verification regenerates the reports and cannot accept stale JSON from a previous failed run.

This record does not replace the hypotheses in the theorem statements. In particular, consult the [README](../README.md) and linked Lean statements for the compact probabilistic `QP` assumption, finite type-count errors, and the empirical spectral-drift condition for the unnormalized countable source.
