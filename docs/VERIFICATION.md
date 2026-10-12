# Reproducible verification record

Verification date: 2026-10-12 (Asia/Shanghai). This page records actual local runs. To verify a checkout, use the repository's one-command entry rather than relying on this record.

## Actual runs

```powershell
.\Verify.ps1 -SkipCache -FullAudit
.\verify.cmd -SkipCache
```

Both entries returned exit code `0`. After correcting the paper-to-Lean mapping, `verify.cmd -SkipCache` was run again and returned `0`, printing the four paper-theorem groups and checking all 21 distinct Lean audit targets. The mathematical sources were unchanged by that correction.

The pinned dependencies and cache were already available locally, so these runs used `-SkipCache`. The default cache-fetching step was also checked successfully. A fresh clone should normally use the default entry. PowerShell and Bash entry syntax was checked; a full Linux/macOS execution is not claimed.

## Results

| Item | Observed result |
| --- | --- |
| Mathematical proof sources | All 1,663 Lean files under `PerronWright/` are included |
| Full build | `Build completed successfully (5356 jobs).` |
| Paper main theorems | **Four: Theorems 3.6, 3.8, 3.9, and 3.10** |
| Distinct implementation/specialization declarations | 17: two for 3.6, fourteen for 3.8, and one joint terminal for both 3.9 and 3.10 |
| Supporting declarations | Four Brownian factorial-density and determinacy results; not additional main theorems |
| Checked Lean audit targets | 21 in total; actual checked proof expressions were read and direct proof-theorem dependencies printed |
| Transitive closure of type and proof constants | 88,559 declarations; no unknown or uninspectable nodes |
| Axioms | Only `propext`, `Classical.choice`, and `Quot.sound`; no nonstandard axioms found |
| Additional audits | `Audit.lean`, `ProbabilityAudit.lean`, and `Chapter3FiniteProcessSpatialBridgeAudit.lean` all passed |
| Build and audit diagnostics | No Lean errors or warnings found |
| Generated definition locations | Lean's one-based identifier positions are used; density, finite-model, and compact-terminal locations were checked against the source |

The latest successful entry printed:

```text
AUDIT COVERAGE: 4 paper main theorems; 17 distinct implementation declarations; 4 supporting declarations.
DEPENDENCY AUDIT PASSED: 4 paper main theorems; 21 audited Lean declarations (17 implementation + 4 supporting); 88559 reachable constants. Reports: .verification/
```

Complete local outputs are in `.verification/`. The full JSON dependency graph (approximately 170 MB) and compilation caches are not committed. The smaller project-definition index is preserved in [MAIN_THEOREM_DEFINITIONS.md](MAIN_THEOREM_DEFINITIONS.md). JSON schema v2 records the four paper groups, each declaration's role, and its paper theorem number(s); the shared countable terminal belongs to both 3.9 and 3.10 and is inspected only once. Verification regenerates the reports and cannot accept stale JSON from a previous failed run.

This record does not replace the hypotheses in the theorem statements. In particular, consult the [README](../README.md) and linked Lean statements for the compact probabilistic `QP` assumption, finite type-count errors, and the empirical spectral-drift condition for the unnormalized countable source.
