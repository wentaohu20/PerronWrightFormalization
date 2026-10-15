# Perron–Wright Formalization

A Lean 4 formalization of the paper's four main theorems: **Theorems 3.6, 3.8, 3.9, and 3.10**. The project includes kernel-weighted enumeration, local factorial asymptotics, actual Brownian component-process limits, and countable-type realizations with growing supports. [PerronWright.lean](PerronWright.lean) imports the proof modules.

The paper has **four main theorems, not 21**. A paper theorem may have several model-specific Lean declarations or separately stated consequences; conversely, a single joint Lean declaration can implement more than one paper theorem. In particular, the countable terminal implements both Theorems 3.9 and 3.10. Brownian density and determinacy results are supporting results, not additional main theorems.

The project pins **Lean / mathlib v4.33.1**. See [lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), and [lake-manifest.json](lake-manifest.json) for the toolchain and exact dependency commits. The linked Lean statements are authoritative for assumptions and quantifier order. See the [verification record](docs/VERIFICATION.md) for the scope of actual tests.

## License

Copyright 2026 PerronWrightFormalization contributors.

The original Lean source code, verification scripts, and documentation in this repository are licensed under the [Apache License, Version 2.0](LICENSE) (SPDX: `Apache-2.0`). Reuse, modification, redistribution, and commercial use are permitted under its terms; derivative projects are not required to be open source. When redistributing, retain the required license and attribution notices and identify modified files.

Third-party dependencies, including Lean and mathlib, retain their own licenses and notices. This repository license does not determine the separate publication license of the accompanying paper. No additional paper-citation requirement is imposed by this repository license.

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

The entry fetches the pinned mathlib cache, builds the proof library, and displays **Lean's own `#print axioms` output for each of the 17 distinct main-theorem implementation declarations**, using their fully qualified Lean names. It does not combine axiom lists by paper number or introduce wrapper theorems. The joint declaration for Theorems 3.9 and 3.10 is printed once. Complete messages, including wrapped lines, are preserved. Build output and the full dependency graph go to UTF-8 local reports. The Windows entry sets UTF-8 explicitly, including for Windows PowerShell 5.

The inspector reads checked proof expressions, traverses definitions as well as theorem bodies, and exports the complete transitive graph. Reducing console output does not reduce the audit's coverage. Failures return a nonzero exit code and identify the relevant log.

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
| `main-theorem-axioms.txt` | Complete native `#print axioms` messages for the 17 main-theorem implementation declarations, replayed without rewriting |
| `main-theorem-dependencies.log` | Native Lean axiom output and dependency-export completion status |
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

The tables below are a statement-semantics reading list: model assumptions, quantities named in the conclusions, and actual source and limiting objects. Shared definitions are listed once. Proof constructions, auxiliary conversions, encodings, and instances are left to the detailed indices, not added to this reading list.

To audit, read a linked theorem statement together with these definitions, then run the verification entry to inspect its checked dependencies and accepted axioms. The axiom check verifies the formal proof's foundations; checking that its definitions express the intended mathematical claim is a separate semantic step.

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

#### Definitions used in Theorem 3.6

Here `Kf(x)=∫κ(x,y)f(y)dμ(y)` (a weighted sum in finite types). The graph weight uses vertex factors `exp(−tK1)` and edge factors `tκ`.

| Meaning in the statement | Finite irreducible definition | Compact definition |
| --- | --- | --- |
| Type probability law and symmetric kernel | [`FiniteIrreducibleModel`:22](PerronWright/Model/FiniteIrreducibleModel.lean#L22) | [`CompactBJRModel`:29](PerronWright/Model/CompactBJR.lean#L29) |
| Criticality and regularity assumptions | [`FiniteIrreducibleModel.IsCritical`:51](PerronWright/Model/FiniteIrreducibleModel.lean#L51) | [`CompactBJRModel.B1`:93](PerronWright/Model/CompactBJR.lean#L93), [`B2`:174](PerronWright/Model/CompactBJR.lean#L174), [`IsRegularCritical`:191](PerronWright/Model/CompactBJR.lean#L191) |
| Perron function `Ku=u`, `∫u dμ=1`; scales `α=∫u² dμ`, `β=∫u³ dμ` | [`FiniteIrreducibleModel.perronFunction`:124](PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L124), [`alpha`:139](PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L139), [`beta`:142](PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L142) | [`CompactBJRModel.perronFunction`:22](PerronWright/Model/PerronQuantities.lean#L22), [`alpha`:92](PerronWright/Model/PerronQuantities.lean#L92), [`beta`:96](PerronWright/Model/PerronQuantities.lean#L96) |
| `C_t(k,r)`: sum of type-integrated weights of connected labelled simple graphs on `k` vertices with `k+r−1` edges | Uses the same [`connectedWeight`:53](PerronWright/Enumeration/ConnectedWeight.lean#L53), via [`FiniteIrreducibleModel.bjrModel`:62](PerronWright/Model/FiniteIrreducibleBJRBridge.lean#L62) | [`CompactBJRModel.connectedWeight`:53](PerronWright/Enumeration/ConnectedWeight.lean#L53) |
| Scalar field `g_t=(log t)1−(t−1)K1` | [`FiniteIrreducibleScalarFieldResponse.scalarField`:22](PerronWright/Analysis/FiniteIrreducibleScalarFieldResponse.lean#L22) | [`ScalarFieldResponse.scalarFieldComplex`:14](PerronWright/Analysis/ScalarFieldResponse.lean#L14) |
| Rooted-tree power series whose convergence radius the theorem identifies | [`FiniteIrreducibleModel.fieldFMS`:58](PerronWright/Analysis/FiniteIrreducibleFieldSeriesNormalization.lean#L58) | [`FieldRootedTree.fms`:41](PerronWright/Enumeration/ScalarFieldRootedTreeRadius.lean#L41) |
| Real radius `ρ(t)`; the compact statement also asserts analyticity of its complex extension | [`FiniteIrreducibleCriticalWindowRadiusConversion.realScalarRadius`:23](PerronWright/Analysis/FiniteIrreducibleCriticalWindowRadiusConversion.lean#L23) | [`CompactPerronWrightTheorem.ScalarRadius.physicalRadius`:34](PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L34), [`criticalRadius`:28](PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L28) |
| Surplus-indexed Wright constant `w_r` | [`FiniteIrreduciblePerronWrightFormulaMainTerm.wrightConstant`:26](PerronWright/Analysis/FiniteIrreduciblePerronWrightFormulaMainTerm.lean#L26) | [`PerronWrightFormulaMainTerm.wrightConstant`:25](PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L25) |
| Exact-radius main term displayed above and its Gaussian specialization | [`FiniteIrreduciblePerronWrightFormulaMainTerm.perronWrightRadiusMainTerm`:64](PerronWright/Analysis/FiniteIrreduciblePerronWrightFormulaMainTerm.lean#L64), [`FiniteIrreducibleBoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm`:131](PerronWright/Analysis/FiniteIrreducibleBoundedSurplusPerronWrightFormula.lean#L131) | [`PerronWrightFormulaMainTerm.perronWrightRadiusMainTerm`:58](PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L58), [`BoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm`:131](PerronWright/Enumeration/BoundedSurplusPerronWrightFormula.lean#L131) |

Further details of graph integrals, tree coefficients, analytic critical-pair construction, and Wright constants are in the [Theorem 3.6 definition index](docs/ENUMERATION_INDEX.md).

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

#### Definitions used in Theorem 3.8

The model, criticality, Perron function, and scales `α, β` are the [definitions listed for Theorem 3.6](#definitions-used-in-theorem-36). The additional probability objects are listed below. For finite types, `hround` is the assumption that one `D ≥ 0` bounds `|fiberCount(xₙ,s)−n M.weight(s)|` for every type and all sufficiently large `n`; it is written directly in the theorem statements, not packaged as a separate definition.

| Meaning in the statement | Definitions and source locations |
| --- | --- |
| Actual finite-type counts used in the bounded-rounding assumption `hround` | [`FiniteIrreducibleTypePlacementMultiplicity.fiberCount`:97](PerronWright/Probability/FiniteIrreducibleTypePlacementMultiplicity.lean#L97) |
| Additional compact assumption `QP`: `κ(x,y)=Σ aⱼfⱼ(x)fⱼ(y)`, with `Σ abs(aⱼ)‖fⱼ‖∞²<∞` | [`CompactBJRModel.QP`:82](PerronWright/Probability/ProjectiveKernel.lean#L82), [`ProjectiveKernel.HasRepresentation`:47](PerronWright/Probability/ProjectiveKernel.lean#L47) |
| Actual graph sources: deterministic finite types or i.i.d. compact types; conditional edges have probability `1−exp(−tκ/n)` | [`FiniteIrreducibleTypedGraphLaw.law`:52](PerronWright/Probability/FiniteIrreducibleTypedGraphLaw.lean#L52), [`AnnealedGraph.law`:166](PerronWright/Probability/AnnealedGraph.lean#L166) |
| Critical time, literal sizes, and ordered distinct component counts; surplus is `edges+1−vertices` | [`CriticalScaling.time`:24](PerronWright/Probability/CriticalScaling.lean#L24) is `max(0,1+λn^(−1/3))`; [`size`:49](PerronWright/Probability/CriticalScaling.lean#L49) is `⌊xn^(2/3)⌋₊`; [`ComponentCounts.count`:60](PerronWright/Probability/ComponentCounts.lean#L60). The finite local statement writes `1+λn^(−1/3)` and the floor directly. |
| Compact local quantity `n^(2q/3) E[count]` and its closed size window `[a,b]^q` | [`CompactAnnealedFactorialLocal.localExpectation`:27](PerronWright/Probability/CompactAnnealedFactorialLocal.lean#L27), [`FactorialDensity.sizeWindow`:21](PerronWright/Probability/FactorialWindowMass.lean#L21). The finite local statement writes the scaled integral directly. |
| Explicit limiting ordered factorial density | [`FactorialDensity.density`:29](PerronWright/Probability/FactorialDensity.lean#L29); its polynomial exponent and surplus factors are defined immediately above it. |
| State spaces: finite integer point measures on closed windows (weak topology), locally finite integer point measures on `(0,∞)×ℕ` (vague topology), and probability-valued type marks (weak topology) | [`FinitePointMeasureCompact.PointMeasure`:33](PerronWright/Probability/FinitePointMeasureCompact.lean#L33), [`LocallyFinitePointMeasureVague.LocalPointMeasure`:29](PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L29), [`WeakProbabilityMarks.WeakMark`:17](PerronWright/Probability/WeakProbabilityMarks.lean#L17). Marked state spaces add this mark coordinate. |
| Component empirical type probability and limiting Perron mark `u·μ` | [`EmpiricalTypeMarks.componentMark`:75](PerronWright/Probability/EmpiricalTypeMarks.lean#L75), [`perronMark`:118](PerronWright/Probability/EmpiricalTypeMarks.lean#L118), [`FiniteIrreducibleConnectedTypeLaw.perronLaw`:43](PerronWright/Probability/FiniteIrreducibleConnectedTypeLaw.lean#L43) |
| Actual unstarred source laws, with or without empirical marks, globally or on a closed window | Finite: [`FiniteIrreducibleComponentProcess.unmarkedProcessLaw`:38](PerronWright/Probability/FiniteIrreducibleComponentProcess.lean#L38) / [`unmarkedWindowLaw`:43](PerronWright/Probability/FiniteIrreducibleComponentProcess.lean#L43), [`FiniteIrreducibleMarkedComponentProcess.markedProcessLaw`:52](PerronWright/Probability/FiniteIrreducibleMarkedComponentProcess.lean#L52) / [`markedWindowLaw`:46](PerronWright/Probability/FiniteIrreducibleMarkedComponentProcess.lean#L46). Compact: [`ComponentGlobalPointProcess.unmarkedProcessLaw`:218](PerronWright/Probability/ComponentGlobalPointProcess.lean#L218) / [`ComponentWindowPointMeasures.unmarkedWindowLaw`:249](PerronWright/Probability/ComponentWindowPointMeasures.lean#L249), [`ComponentGlobalMarkedProcess.markedProcessLaw`:76](PerronWright/Probability/ComponentGlobalMarkedProcess.lean#L76) / [`ComponentWindowMarkedLaw.markedWindowLaw`:77](PerronWright/Probability/ComponentWindowMarkedLaw.lean#L77) |
| Starred global source laws: multiply sizes by `β^(1/3)`, leaving surplus and marks unchanged | Finite: [`FiniteIrreducibleGlobalSizeRescaling.starredProcessLaw`:77](PerronWright/Probability/FiniteIrreducibleGlobalSizeRescaling.lean#L77), [`FiniteIrreducibleGlobalMarkedSizeRescaling.starredMarkedProcessLaw`:148](PerronWright/Probability/FiniteIrreducibleGlobalMarkedSizeRescaling.lean#L148). Compact: [`GlobalPointSizeRescaling.starredProcessLaw`:112](PerronWright/Probability/GlobalPointSizeRescaling.lean#L112), [`GlobalMarkedPointSizeRescaling.starredMarkedProcessLaw`:156](PerronWright/Probability/GlobalMarkedPointSizeRescaling.lean#L156) |
| Brownian target: excursions of reflected `B(t)+Λt−t²/2`, with conditionally independent Poisson surplus marks of excursion-area means | [`BrownianExcursionPointProcessLaw.law`:45](PerronWright/Probability/BrownianExcursionPointProcessLaw.lean#L45). Unstarred targets apply inverse size dilation: [`BrownianInverseSizeLaw.inverseScaledLaw`:41](PerronWright/Probability/BrownianInverseSizeLaw.lean#L41), [`BrownianInverseWindowLaw.law`:24](PerronWright/Probability/BrownianInverseWindowLaw.lean#L24). The direct closed-window restriction, also used in Theorems 3.9–3.10, is [`BrownianArbitraryWindowLaw.law`:183](PerronWright/Probability/BrownianArbitraryWindowLaw.lean#L183). |
| Marked Brownian targets: attach the same Perron probability to every atom | Finite: [`FiniteIrreducibleMarkedWindowConvergence.canonicalPerronMarkedLaw`:26](PerronWright/Probability/FiniteIrreducibleMarkedWindowConvergence.lean#L26), [`FiniteIrreducibleMarkedGlobalTests.canonicalGlobalMarkedLaw`:33](PerronWright/Probability/FiniteIrreducibleMarkedGlobalTests.lean#L33). Compact: [`ComponentWindowMarkedConvergence.canonicalPerronMarkedLaw`:27](PerronWright/Probability/ComponentWindowMarkedConvergence.lean#L27), [`GlobalPointMeasureMarking.canonicalGlobalMarkedLaw`:78](PerronWright/Probability/GlobalPointMeasureMarking.lean#L78) |

The terminal statements write the Brownian parameter `αβ^(−2/3)λ` directly, using the Perron scales defined for Theorem 3.6. Convergence is weak convergence of probability laws on the specified point-measure spaces, not total-variation convergence of process laws. For the full construction and topology details, see the [probability definition index](docs/PROBABILITY_INDEX.md).

### Theorem 3.9 — Countable type critical realization

The joint declaration is:

`PerronWright.CountableActualBrownianLimits.exists_actual_growing_Brownian_global_and_TV_window_limits`

See [line 90](PerronWright/Probability/CountableActualBrownianLimits.lean#L90). One outermost `∃ level` supplies exhausting supports, exact positive integer type counts, and the actual graph sources used throughout. Its **spectrally normalized branch** uses edge hazard `tκ/(Nσ_n)` and gives uniform local factorial limits, starred unmarked global Brownian limits, unmarked and TV-marked window limits, and quantitative type-mark control.

#### Definitions used in Theorem 3.9

The original countable model supplies all Perron quantities and the limiting mark. The graph index is `n`, with actual vertex count `N=n+1`. Component counts, density, point-measure topologies, and Brownian constructions use the [shared probability definitions listed for Theorem 3.8](#definitions-used-in-theorem-38).

| Meaning in the statement | Definitions and source locations |
| --- | --- |
| Countable type probability law and kernel; spectral criticality and regular criticality | [`CountableKernel`:19](PerronWright/Model/CountableKernel.lean#L19), [`CountableKernel.IsCritical`:19](PerronWright/Kernel/CountablePerron.lean#L19), [`IsRegularCritical`:18](PerronWright/Model/CountablePerronQuantities.lean#L18). The theorem also takes an explicit uniform lower bound `0<lower≤κ(s,t)`. |
| Original normalized Perron vector and scales `∫u dμ=1`, `α=∫u² dμ`, `β=∫u³ dμ` | [`CountableKernel.perronVector`:27](PerronWright/Model/CountablePerronQuantities.lean#L27), [`alpha`:92](PerronWright/Model/CountablePerronQuantities.lean#L92), [`beta`:95](PerronWright/Model/CountablePerronQuantities.lean#L95) |
| Positive integer counts on `{0,…,level N}`, actual vertex types, and empirical type probability | [`GrowingTypeCounts.truncatedCounts`:57](PerronWright/Probability/GrowingTypeCounts.lean#L57), [`CountableTypeRealization.vertexTypes`:30](PerronWright/Probability/CountableTypeRealization.lean#L30), [`empiricalMeasure`:65](PerronWright/Probability/CountableTypeRealization.lean#L65); the input weights are the original atoms `μ({s})`. |
| Empirical spectral radius `σ_n` used to normalize edge hazards | [`CountableKernel.empiricalSpectralRadius`:55](PerronWright/Kernel/CountableApproximationEmpirical.lean#L55) |
| Actual normalized graph law, with independent edge probability `1−exp(−tκ/(Nσ_n))` | [`CountableKernel.empiricalNormalizedGraphLaw`:41](PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L41); `t=max(0,1+λN^(−1/3))`. |
| Normalized local factorial quantity `N^(2q/3) E[count]` | [`CountableKernel.growingLocalExpectation`:32](PerronWright/Probability/CountableFixedSupportGrowingSource.lean#L32); the density and floor-size convention are shared with Theorem 3.8. |
| Normalized starred global **unmarked** law and starred unmarked/empirical-TV-marked window laws | [`CountableStarredGlobalSizeRescaling.normalizedStarredProcessLaw`:32](PerronWright/Probability/CountableStarredGlobalSizeRescaling.lean#L32), [`CountableStarredTVWindowLaw.normalizedStarredWindowLaw`:30](PerronWright/Probability/CountableStarredTVWindowLaw.lean#L30), [`normalizedStarredMarkedWindowLaw`:36](PerronWright/Probability/CountableStarredTVWindowLaw.lean#L36). Sizes are multiplied by the original `β^(1/3)`. |
| TV type-mark space: probabilities on `ℕ` with distance `Σ_s abs(p({s})−q({s}))`; limiting mark is `u·μ` | [`CountableVariationMarks.VariationMark`:52](PerronWright/Probability/CountableVariationMarks.lean#L52), [`CountablePerronMarkConvergence.perronMark`:19](PerronWright/Probability/CountablePerronMarkConvergence.lean#L19). This distance is twice the convention that defines TV distance as half the atomic sum. |
| TV-marked closed-window state space and Brownian target with the constant Perron mark | [`CountableComponentWindowLaw.MarkedWindow`:26](PerronWright/Probability/CountableComponentWindowLaw.lean#L26), [`CountableTVWindowConvergence.canonicalMarkedWindowLaw`:26](PerronWright/Probability/CountableTVWindowConvergence.lean#L26); the unmarked target is [`BrownianArbitraryWindowLaw.law`:183](PerronWright/Probability/BrownianArbitraryWindowLaw.lean#L183). |
| Quantitative mark controls: sum of component mark distances, and event that some mark has distance at least `δ` | [`CountableTVWindowProfile.windowDistance`:27](PerronWright/Probability/CountableTVWindowProfile.lean#L27), [`badMarkCell`:102](PerronWright/Probability/CountableTVWindowProfile.lean#L102) |
| Normalized expectation of that distance sum and probability of that bad-mark event, both tending to zero | [`CountableKernel.growingWindowDistanceExpectation`:94](PerronWright/Probability/CountableTVWindowExpectation.lean#L94), [`growingWindowBadProbability`:22](PerronWright/Probability/CountableTVWindowTerminal.lean#L22) |

The quantitative distance and bad-mark controls use **unstarred** size windows; the process limits use the displayed starred laws. The [countable definition index](docs/COUNTABLE_INDEX.md) spells out the common integer realization and each branch of the joint conclusion.

### Theorem 3.10 — Countable type limits without spectral renormalization

This is the **unnormalized branch of the same joint declaration**, using the same integer realization and edge hazard `tκ/N`. Under `N^(1/3)(σ_n−1)→θ`, its local density parameter is **`λ+θ`**, and its actual Brownian parameter is **`αβ^(−2/3)(λ+θ)`**. The spectral-drift hypothesis cannot be omitted.

For both countable branches, global convergence is asserted only for the **unmarked vague law**. TV refers to the metric on component type marks; marked window laws converge weakly in that mark space. It does **not** mean total-variation convergence between whole process probability laws. The [countable index](docs/COUNTABLE_INDEX.md) distinguishes normalized/raw sources, starred laws, and unstarred-window quantitative estimates.

#### Definitions used in Theorem 3.10

The model, original Perron quantities, integer realization, empirical spectral radius, point-measure spaces, TV marks, and Brownian targets are the [same definitions as in Theorem 3.9](#definitions-used-in-theorem-39). Only the changed source objects are listed below; the limiting parameter shift `λ+θ` is written directly in the statement. The spectral-drift premise is written directly in the [joint terminal statement](PerronWright/Probability/CountableActualBrownianLimits.lean#L110).

| Additional or changed meaning in the statement | Definitions and source locations |
| --- | --- |
| Raw graph law: independent edge probability `1−exp(−tκ/N)`, without division by `σ_n` | [`CountableKernel.empiricalUnnormalizedGraphLaw`:78](PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L78); the time convention is unchanged. |
| Raw scaled local factorial expectation | [`CountableKernel.growingUnnormalizedLocalExpectation`:23](PerronWright/Probability/CountableUnnormalizedLocalTerminal.lean#L23); its limiting density uses `λ+θ`. |
| Raw starred global **unmarked** source law | [`CountableStarredGlobalSizeRescaling.unnormalizedStarredProcessLaw`:37](PerronWright/Probability/CountableStarredGlobalSizeRescaling.lean#L37) |
| Raw starred unmarked and empirical-TV-marked closed-window source laws | [`CountableStarredTVWindowLaw.unnormalizedStarredWindowLaw`:43](PerronWright/Probability/CountableStarredTVWindowLaw.lean#L43), [`unnormalizedStarredMarkedWindowLaw`:48](PerronWright/Probability/CountableStarredTVWindowLaw.lean#L48) |
| Raw empirical-marked law used in the unstarred-window bad-mark probability | [`CountableKernel.empiricalUnnormalizedMarkedWindowLaw`:144](PerronWright/Probability/CountableComponentWindowLaw.lean#L144). The distance integral uses the raw graph law; `windowDistance` and `badMarkCell` are defined in the Theorem 3.9 table. |

The raw quantitative controls are literal integrals and event probabilities in the joint statement, not separately named expectation/probability definitions. As in Theorem 3.9, they concern **unstarred** size windows.

## Supporting Brownian results

These results support the paper's Brownian factorial-density and determinacy proposition and the identification used in Theorem 3.8; they are **not extra main theorems**:

| Supporting declaration | Location |
| --- | --- |
| `BrownianActualFactorialDensity.actual_ordered_source_factorial_density` | [Line 64](PerronWright/Probability/BrownianActualFactorialDensity.lean#L64) |
| `BrownianActualFactorialDensity.actual_window_factorial_density` | [Line 136](PerronWright/Probability/BrownianActualFactorialDensity.lean#L136) |
| `BrownianActualArbitraryWindowDeterminacy.actual_cell_countLaw_eq_of_factorial_lintegrals` | [Line 36](PerronWright/Probability/BrownianActualArbitraryWindowDeterminacy.lean#L36) |
| `BrownianActualArbitraryWindowDeterminacy.actual_windowLaw_eq_of_density_factorial_lintegrals` | [Line 95](PerronWright/Probability/BrownianActualArbitraryWindowDeterminacy.lean#L95) |

Their source is an actual continuous Brownian path, reflected excursions, and Poisson marks that are conditionally independent given the path, with excursion areas as their rates. Brownian identification is proved rather than assumed as an external interface.

## Detailed source and dependency indices

The per-theorem tables above contain the semantic reading list. These indices expand the constructions and locate additional proof objects; the generated index also includes internal helpers.

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
docs/                        Source indices, verification record, and release history
Verify.ps1 / verify.cmd       Windows build and theorem-dependency verification
verify.sh                    Unix verification entry
MainTheoremDependencies.lean  Inspector of checked theorem expressions
```

Mathematical proof sources and the inspection program are separate. Caches, scratch experiments, credentials, and local reports are excluded from Git. The [release history](docs/RELEASE_HISTORY.md) starts with the first public release; pre-publication development milestones are not separate public versions.

When public declaration names change, update the paper-to-Lean mapping in `MainTheoremDependencies.lean`, this README, and the relevant indices, then rerun verification. Do not substitute old reports for a fresh build.
