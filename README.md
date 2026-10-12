# Perron–Wright Formalization

A Lean 4 formalization of the paper's four main theorems: **Theorems 3.6, 3.8, 3.9, and 3.10**. The project includes kernel-weighted enumeration, local factorial asymptotics, actual Brownian component-process limits, and countable-type realizations with growing supports. [PerronWright.lean](PerronWright.lean) imports the proof modules.

The paper has **four main theorems, not 21**. A paper theorem may have several model-specific Lean declarations or separately stated consequences; conversely, a single joint Lean declaration can implement more than one paper theorem. In particular, the countable terminal implements both Theorems 3.9 and 3.10. Brownian density and determinacy results are supporting results, not additional main theorems.

The project pins **Lean / mathlib v4.33.1**. See [lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), and [lake-manifest.json](lake-manifest.json) for the toolchain and exact dependency commits. The linked Lean statements are authoritative for assumptions and quantifier order. See the [verification record](docs/VERIFICATION.md) for the scope of actual tests.

## One-command build and dependency verification

Install [Lean's Elan toolchain manager](https://lean-lang.org/install/) and ensure `lake` is on your `PATH`. Python, Node.js, and the GitHub CLI are not required.

On Windows, double-click **[verify.cmd](verify.cmd)** or run:

```powershell
.\Verify.ps1
```

On Linux/macOS:

```sh
bash verify.sh
```

The entry fetches the pinned mathlib cache, builds the proof library, and prints the four paper-theorem groups followed by the actual theorem dependencies and axiom dependencies of their Lean declarations. It reads checked proof expressions, traverses definitions as well as theorem bodies, and exports the complete transitive graph. It does not substitute module imports or `#print axioms` alone for theorem dependencies. Failures return a nonzero exit code.

For the three additional axiom audits:

```powershell
.\Verify.ps1 -FullAudit
```

Use `-SkipCache` when the pinned dependencies and cache are already present. Unix equivalents are `SKIP_CACHE=1 bash verify.sh` and `FULL_AUDIT=1 bash verify.sh`. The first run needs network access, disk space, and substantial build time; subsequent runs reuse local artifacts.

### What the verifier counts

- **4 paper main theorems:** 3.6, 3.8, 3.9, and 3.10.
- **17 distinct Lean implementation/specialization declarations:** two for 3.6; fourteen model-specific local, process, and rescaling declarations for 3.8; one joint countable declaration for both 3.9 and 3.10, counted only once.
- **4 supporting Brownian declarations:** factorial density and determinacy results.

Thus the audit checks **21 Lean declarations**, not 21 main theorems. Each declaration's report records its role and the paper theorem number(s) it belongs to. Axioms are reported separately: only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are accepted; `sorryAx` or any other nonstandard axiom causes failure. The inspection program adds no mathematical assumptions and is not imported by proof modules.

Local outputs are written to `.verification/` and are not committed:

| Output | Contents |
| --- | --- |
| `build.log` | Complete build output |
| `main-theorem-dependencies.log` | Paper numbering, declaration roles, direct proof-theorem dependencies, transitive project-theorem counts, and axioms |
| `main-theorem-dependencies.json` | Schema v2: four paper-theorem groups, declaration-to-paper mappings, statements, direct type/proof constants, the full transitive graph, and source locations |
| `main-theorem-definitions.md` | All reachable project definitions, including generated helpers and private declarations |

The dependency inspector is [MainTheoremDependencies.lean](MainTheoremDependencies.lean). A previous report is removed before verification; a failed run cannot be accepted through stale JSON.

## Main theorems and their source locations

| Paper theorem | Title | Lean implementation |
| --- | --- | --- |
| **3.6** | Perron–Wright formula | [Finite terminal](PerronWright/Analysis/FiniteIrreduciblePerronWrightTerminal.lean#L120), [compact terminal](PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L232) |
| **3.8** | Local factorial asymptotics and component process limit | [Finite local formula](PerronWright/Probability/FiniteIrreducibleLocalMainTerminal.lean#L34), [compact local formula](PerronWright/Probability/CompactAnnealedFactorialUniform.lean#L44), [model-specific Brownian limits](PerronWright/Probability/ModelActualBrownianLimits.lean#L45) |
| **3.9** | Countable type critical realization | [Joint countable terminal, normalized branch](PerronWright/Probability/CountableActualBrownianLimits.lean#L90) |
| **3.10** | Countable type limits without spectral renormalization | [The same terminal, unnormalized/spectral-drift branch](PerronWright/Probability/CountableActualBrownianLimits.lean#L90) |

Names below omit the common prefix `PerronWright.` unless otherwise indicated. Each link points to the declaration's source line, where its full statement and proof can be read.

### Theorem 3.6 — Perron–Wright formula

| Model | Declaration | Location |
| --- | --- | --- |
| Finite irreducible critical types | `FiniteIrreduciblePerronWrightTerminal.finite_perronWright` | [Line 120](PerronWright/Analysis/FiniteIrreduciblePerronWrightTerminal.lean#L120) |
| Regular critical compact BJR types | `CompactPerronWrightTheorem.compactPerronWright_theorem` | [Line 232](PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L232) |

The compact conclusion fields are defined in [CompactPerronWrightConclusions](PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L193). Both versions include analyticity of the genuine rooted-tree radius, `ρ(1)=1`, its quadratic logarithmic response with cubic error, and uniform bounded-surplus asymptotics:

$$
C_t(k,r)=w_r\beta^{(r-1)/2}e^{-k}\rho(t)^{-k}
k^{k+3r/2-2}\{1+O_R(\eta_k+k^{-1/2})\},\qquad |t-1|\le\eta_k\to0.
$$

They also give the Gaussian specialization on `|t−1|≤Lk⁻¹ᐟ²`. Here **`ρ` is the actual radius of the rooted-tree series**; `eρ` is an exponential scale in the enumerative main term, not another tree-series radius. The compact enumeration theorem requires B1–B2, not the additional probabilistic `QP` assumption.

### Theorem 3.8 — Local factorial asymptotics and component process limit

The fixed-size factorial formula has two model-specific declarations:

| Model | Declaration | Location |
| --- | --- | --- |
| Fixed finite type assignments with `O(1)` count errors | `FiniteIrreducibleLocalMainTerminal.eventually_uniform_paper_floor_factorial_density` | [Line 34](PerronWright/Probability/FiniteIrreducibleLocalMainTerminal.lean#L34) |
| Regular compact model with `QP` | `CompactAnnealedFactorialUniform.factorial_uniform_bounded_surplus` | [Line 44](PerronWright/Probability/CompactAnnealedFactorialUniform.lean#L44) |

The counts concern ordered, pairwise distinct genuine connected components, with literal integer sizes `⌊x n^(2/3)⌋`. Uniformity holds over fixed positive size windows and bounded surplus tuples.

Process-law declarations and their window/unstarred variants are all in `PerronWright.ModelActualBrownianLimits`:

| Conclusion or specialization | Finite irreducible declaration | Regular compact declaration |
| --- | --- | --- |
| Unmarked closed window | [`finite_windowLaw_tendsto_actual_Brownian`:45](PerronWright/Probability/ModelActualBrownianLimits.lean#L45) | [`compact_windowLaw_tendsto_actual_Brownian`:158](PerronWright/Probability/ModelActualBrownianLimits.lean#L158) |
| Unmarked global vague law | [`finite_processLaw_tendsto_actual_Brownian`:63](PerronWright/Probability/ModelActualBrownianLimits.lean#L63) | [`compact_processLaw_tendsto_actual_Brownian`:173](PerronWright/Probability/ModelActualBrownianLimits.lean#L173) |
| Empirically marked closed window | [`finite_markedWindowLaw_tendsto_actual_Brownian`:80](PerronWright/Probability/ModelActualBrownianLimits.lean#L80) | [`compact_markedWindowLaw_tendsto_actual_Brownian`:187](PerronWright/Probability/ModelActualBrownianLimits.lean#L187) |
| Empirically marked global law | [`finite_markedProcessLaw_tendsto_actual_Brownian`:97](PerronWright/Probability/ModelActualBrownianLimits.lean#L97) | [`compact_markedProcessLaw_tendsto_actual_Brownian`:201](PerronWright/Probability/ModelActualBrownianLimits.lean#L201) |
| **Starred unmarked global law** | [`finite_starredProcessLaw_tendsto_actual_Brownian`:113](PerronWright/Probability/ModelActualBrownianLimits.lean#L113) | [`compact_starredProcessLaw_tendsto_actual_Brownian`:215](PerronWright/Probability/ModelActualBrownianLimits.lean#L215) |
| **Starred empirically marked global law** | [`finite_starredMarkedProcessLaw_tendsto_actual_Brownian`:128](PerronWright/Probability/ModelActualBrownianLimits.lean#L128) | [`compact_starredMarkedProcessLaw_tendsto_actual_Brownian`:229](PerronWright/Probability/ModelActualBrownianLimits.lean#L229) |

The starred declarations are the paper's rescaled process conclusions. The size coordinate is multiplied by `β^(1/3)`; surplus and empirical type marks are unchanged. The Brownian parameter is `Λ=αβ^(−2/3)λ`. Unstarred limits use the corresponding inverse size dilation. The limiting type mark is the Perron probability `u·μ`, not the original `μ`.

The finite model permits arbitrary actual deterministic assignments whose type counts have uniformly bounded errors. The compact probabilistic declarations require both `IsRegularCritical` and `QP`.

### Theorem 3.9 — Countable type critical realization

The joint declaration is:

`PerronWright.CountableActualBrownianLimits.exists_actual_growing_Brownian_global_and_TV_window_limits`

See [line 90](PerronWright/Probability/CountableActualBrownianLimits.lean#L90). One outermost `∃ level` supplies exhausting supports, exact positive integer type counts, and the actual graph sources used throughout. Its **spectrally normalized branch** uses edge hazard `tκ/(Nσ_n)` and gives uniform local factorial limits, starred unmarked global Brownian limits, unmarked and TV-marked window limits, and quantitative type-mark control.

### Theorem 3.10 — Countable type limits without spectral renormalization

This is the **unnormalized branch of the same joint declaration**, using the same integer realization and edge hazard `tκ/N`. Under `N^(1/3)(σ_n−1)→θ`, its local density parameter is **`λ+θ`**, and its actual Brownian parameter is **`αβ^(−2/3)(λ+θ)`**. The spectral-drift hypothesis cannot be omitted.

For both countable branches, global convergence is asserted only for the **unmarked vague law**. TV refers to the metric on component type marks; marked window laws converge weakly in that mark space. It does **not** mean total-variation convergence between whole process probability laws. The [countable index](docs/COUNTABLE_INDEX.md) distinguishes normalized/raw sources, starred laws, and unstarred-window quantitative estimates.

## Supporting Brownian results

These results support the paper's Brownian factorial-density and determinacy proposition and the identification used in Theorem 3.8; they are **not extra main theorems**:

| Supporting declaration | Location |
| --- | --- |
| `BrownianActualFactorialDensity.actual_ordered_source_factorial_density` | [Line 64](PerronWright/Probability/BrownianActualFactorialDensity.lean#L64) |
| `BrownianActualFactorialDensity.actual_window_factorial_density` | [Line 136](PerronWright/Probability/BrownianActualFactorialDensity.lean#L136) |
| `BrownianActualArbitraryWindowDeterminacy.actual_cell_countLaw_eq_of_factorial_lintegrals` | [Line 36](PerronWright/Probability/BrownianActualArbitraryWindowDeterminacy.lean#L36) |
| `BrownianActualArbitraryWindowDeterminacy.actual_windowLaw_eq_of_density_factorial_lintegrals` | [Line 95](PerronWright/Probability/BrownianActualArbitraryWindowDeterminacy.lean#L95) |

Their source is an actual continuous Brownian path, reflected excursions, and Poisson marks that are conditionally independent given the path, with excursion areas as their rates. Brownian identification is proved rather than assumed as an external interface.

## Definitions used by the main theorems

This table locates the core semantic objects. The detailed indices below supply fully qualified names and source lines for the remaining objects; the generated index covers all project definitions reachable through types and proofs, including internal helpers.

| Object | Definition and location |
| --- | --- |
| Finite irreducible model and criticality | [`FiniteIrreducibleModel`:22](PerronWright/Model/FiniteIrreducibleModel.lean#L22), [`IsCritical`:51](PerronWright/Model/FiniteIrreducibleModel.lean#L51) |
| Compact BJR model, B1–B2, regular criticality | [`CompactBJRModel`:29](PerronWright/Model/CompactBJR.lean#L29), [B1:93](PerronWright/Model/CompactBJR.lean#L93), [B2:174](PerronWright/Model/CompactBJR.lean#L174), [`IsRegularCritical`:191](PerronWright/Model/CompactBJR.lean#L191) |
| Countable model and regular criticality | [`CountableKernel`:19](PerronWright/Model/CountableKernel.lean#L19), [`IsRegularCritical`:18](PerronWright/Model/CountablePerronQuantities.lean#L18) |
| Compact probability assumption `QP` | [`CompactBJRModel.QP`:82](PerronWright/Probability/ProjectiveKernel.lean#L82): an absolutely summable quadratic feature representation of the kernel, not a type-count condition |
| Normalized Perron function, Perron law, `α`, `β` | [Compact quantities](PerronWright/Model/PerronQuantities.lean#L22), [finite quantities](PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L124), [countable quantities](PerronWright/Model/CountablePerronQuantities.lean#L27) |
| Kernel-weighted connected graph count `C_t(k,r)` | [`connectedWeight`:53](PerronWright/Enumeration/ConnectedWeight.lean#L53), [`fieldConnectedWeight`:97](PerronWright/Enumeration/FieldWeight.lean#L97) |
| Rooted-tree series and genuine critical radius | [`FieldRootedTree.fms`:41](PerronWright/Enumeration/ScalarFieldRootedTreeRadius.lean#L41), [`ScalarRadius.physicalRadius`:34](PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L34) |
| Wright constants and exact-radius main term | [`wrightConstant`:25](PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L25), [`perronWrightRadiusMainTerm`:58](PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L58) |
| Actual finite and compact graph probability measures | [`FiniteIrreducibleTypedGraphLaw.law`:52](PerronWright/Probability/FiniteIrreducibleTypedGraphLaw.lean#L52), [`AnnealedGraph.law`:166](PerronWright/Probability/AnnealedGraph.lean#L166) |
| Critical time, integer component sizes, ordered distinct component count | [CriticalScaling:24, 49](PerronWright/Probability/CriticalScaling.lean#L24), [`ComponentCounts.count`:60](PerronWright/Probability/ComponentCounts.lean#L60) |
| Target local factorial density | [`FactorialDensity.density`:29](PerronWright/Probability/FactorialDensity.lean#L29); its exponent and size factor are at lines 19 and 24 of the same file |
| Finite-window and locally finite global point measures | [`PointMeasure`:33](PerronWright/Probability/FinitePointMeasureCompact.lean#L33), [`SurplusWindow`:250](PerronWright/Probability/FinitePointMeasureCompact.lean#L250), [`LocalPointMeasure`:29](PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L29) |
| Actual Brownian path and excursion process law | [`BrownianPathLaw.pathLaw`:111](PerronWright/Probability/BrownianPathLaw.lean#L111), [`BrownianExcursionPointProcessLaw.law`:45](PerronWright/Probability/BrownianExcursionPointProcessLaw.lean#L45) |
| Excursion area and conditional Poisson marking | [`excursionArea`:51](PerronWright/Probability/BrownianFullHorizonExcursionAreas.lean#L51), [`markLaw`:78](PerronWright/Probability/BrownianFullHorizonPoissonMarks.lean#L78) |
| Empirical component type mark and Perron mark | [`componentMark`:75](PerronWright/Probability/EmpiricalTypeMarks.lean#L75), [`perronMark`:118](PerronWright/Probability/EmpiricalTypeMarks.lean#L118) |
| Countable integer counts, empirical spectral radius, and actual graph sources | [GrowingTypeCounts](PerronWright/Probability/GrowingTypeCounts.lean#L57), [`empiricalSpectralRadius`:55](PerronWright/Kernel/CountableApproximationEmpirical.lean#L55), [CountableEmpiricalGraphLaw](PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L25) |
| Countable TV type-mark space | [`VariationMark`:52](PerronWright/Probability/CountableVariationMarks.lean#L52), [distance formula:72](PerronWright/Probability/CountableVariationMarks.lean#L72) |

Detailed definition and declaration indices:

- [Enumeration: models, operators, Perron quantities, fields, tree radii, and Wright constants](docs/ENUMERATION_INDEX.md)
- [Probability: graph sources, densities, Brownian objects, topologies, marks, and normalization](docs/PROBABILITY_INDEX.md)
- [Countable types: integer realizations, spectral drift, processes, and TV marks](docs/COUNTABLE_INDEX.md)
- [All reachable project definitions, generated from checked expressions](docs/MAIN_THEOREM_DEFINITIONS.md)

## Repository layout and maintenance

```text
PerronWright/Kernel/          Integral kernels, compactness, spectra, continuous realizations
PerronWright/Model/           Finite, compact, and countable models; Perron quantities
PerronWright/Analysis/        Analytic perturbation, implicit functions, folds, transfer
PerronWright/Enumeration/     Graph decomposition, weighted enumeration, Wright constants
PerronWright/Probability/     Actual graph laws, factorial moments, Brownian/process limits
docs/                        Source indices and preserved development history
Verify.ps1 / verify.cmd       Windows build and theorem-dependency verification
verify.sh                    Unix verification entry
MainTheoremDependencies.lean  Inspector of checked theorem expressions
```

Mathematical proof sources and the inspection program are separate. This repository cleanup does not change mathematical statements or proofs. Caches, scratch experiments, credentials, and local reports are excluded from Git. The original long README is preserved as [development history](docs/DEVELOPMENT_HISTORY.md), in its original language; historical progress reports and old interfaces do not replace the current source or indices.

When public declaration names change, update the paper-to-Lean mapping in `MainTheoremDependencies.lean`, this README, and the relevant indices, then rerun verification. Do not substitute old reports for a fresh build.
