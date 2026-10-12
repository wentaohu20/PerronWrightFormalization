# Probability results and definition index

This page locates the probability declarations used for the Chapter 3 results: the supporting Aldous factorial-density and determinacy results, the finite-type and compact-type local formulas, and the Brownian window and global point-process limits. The paper has four main theorems, Theorems 3.6, 3.8, 3.9, and 3.10; multiple public Lean declarations implement their different cases and conclusions. The supporting Brownian results below are not additional main theorems. Each source link points to the beginning of a definition or theorem. This index explains their mathematical meaning; it does not replace verification or report build or audit status.

## 1. Public Lean results

### 1.1 Supporting Brownian results for `prop:AW-density`

| Fully qualified Lean name and location | Content |
| --- | --- |
| [PerronWright.BrownianActualFactorialDensity.actual_ordered_source_factorial_density](../PerronWright/Probability/BrownianActualFactorialDensity.lean#L64) | Factorial-density formula of arbitrary order for ordered, distinct, full excursions, prescribed surplus in each slot, and arbitrary jointly coupled nonnegative Borel tests of the lengths. |
| [PerronWright.BrownianActualFactorialDensity.actual_window_factorial_density](../PerronWright/Probability/BrownianActualFactorialDensity.lean#L136) | Intrinsic factorial-measure density formula on closed positive-size windows; the windows in different slots may overlap. |
| [PerronWright.BrownianActualArbitraryWindowDeterminacy.actual_cell_countLaw_eq_of_factorial_lintegrals](../PerronWright/Probability/BrownianActualArbitraryWindowDeterminacy.lean#L36) | Mixed factorial moments of the density determine the joint count law on disjoint cells. |
| [PerronWright.BrownianActualArbitraryWindowDeterminacy.actual_windowLaw_eq_of_density_factorial_lintegrals](../PerronWright/Probability/BrownianActualArbitraryWindowDeterminacy.lean#L95) | Density moments determine the entire weak-Borel point-process law on any closed positive-size window, including singleton windows. |

For the comparison law, the last result assumes only equality with the density factorial integrals on disjoint size cells with Lebesgue-null boundaries. Integrability of the comparison law, the series needed for moment determinacy, and determination of the entire window law are proved, not supplied as additional hypotheses.

### 1.2 Theorem 3.8: finite-type and compact-type local formulas

| Fully qualified Lean name and location | Content |
| --- | --- |
| [PerronWright.FiniteIrreducibleLocalMainTerminal.eventually_uniform_paper_floor_factorial_density](../PerronWright/Probability/FiniteIrreducibleLocalMainTerminal.lean#L34) | Raw-time/floor formula for fixed types with an eventually uniform bounded integer count error, uniform over all sizes in the window, bounded surplus, and all actual assignments realizing those counts. |
| [PerronWright.CompactAnnealedFactorialUniform.factorial_uniform_bounded_surplus](../PerronWright/Probability/CompactAnnealedFactorialUniform.lean#L44) | Under `IsRegularCritical` and `QP`, uniform convergence of the actual annealed graph law's floor factorial expectation over the entire positive-size window and bounded-surplus tuples. |

The finite-type result directly uses the paper's time `1 + λ n^(−1/3)` and the literal floor. The compact-type result uses a nonnegative time convention defined for every n, which eventually agrees with the paper's time.

### 1.3 Theorem 3.8: twelve public declarations for the Brownian limits

These results are in [ModelActualBrownianLimits.lean](../PerronWright/Probability/ModelActualBrownianLimits.lean). The finite-type results assume `M.IsCritical` and an eventually uniform `O(1)` fibre-count error, and allow general irreducible kernels. The compact-type results assume `M.IsRegularCritical` and `M.QP`. Window results require `0 < a ≤ b` and a surplus bound `R`. They assert convergence of the full sequence, not merely a subsequence, and do not assume the Brownian density formula or Brownian-law identification as additional hypotheses.

| Fully qualified Lean name and location | Conclusion |
| --- | --- |
| [PerronWright.ModelActualBrownianLimits.finite_windowLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L45) | Finite-type unmarked window law. |
| [PerronWright.ModelActualBrownianLimits.finite_processLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L63) | Finite-type unmarked global law. |
| [PerronWright.ModelActualBrownianLimits.finite_markedWindowLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L80) | Finite-type window law with actual empirical marks. |
| [PerronWright.ModelActualBrownianLimits.finite_markedProcessLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L97) | Finite-type global law with actual empirical marks. |
| [PerronWright.ModelActualBrownianLimits.finite_starredProcessLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L113) | Finite-type starred unmarked global law. |
| [PerronWright.ModelActualBrownianLimits.finite_starredMarkedProcessLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L128) | Finite-type starred global law with actual empirical marks. |
| [PerronWright.ModelActualBrownianLimits.compact_windowLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L158) | Compact-type unmarked window law. |
| [PerronWright.ModelActualBrownianLimits.compact_processLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L173) | Compact-type unmarked global law. |
| [PerronWright.ModelActualBrownianLimits.compact_markedWindowLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L187) | Compact-type window law with actual empirical marks. |
| [PerronWright.ModelActualBrownianLimits.compact_markedProcessLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L201) | Compact-type global law with actual empirical marks. |
| [PerronWright.ModelActualBrownianLimits.compact_starredProcessLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L215) | Compact-type starred unmarked global law. |
| [PerronWright.ModelActualBrownianLimits.compact_starredMarkedProcessLaw_tendsto_actual_Brownian](../PerronWright/Probability/ModelActualBrownianLimits.lean#L229) | Compact-type starred global law with actual empirical marks. |

## 2. Models, criticality assumptions, and Perron parameters

| Fully qualified Lean name and location | Meaning |
| --- | --- |
| [PerronWright.FiniteIrreducibleModel](../PerronWright/Model/FiniteIrreducibleModel.lean#L22) | Finitely many positive type weights summing to one and a symmetric irreducible kernel. Nonnegativity is part of kernel irreducibility; strict positivity and aperiodicity are not required. |
| [PerronWright.FiniteIrreducibleModel.meanMatrix](../PerronWright/Model/FiniteIrreducibleModel.lean#L44) | Mean matrix `κ diag(μ)`. |
| [PerronWright.FiniteIrreducibleModel.IsCritical](../PerronWright/Model/FiniteIrreducibleModel.lean#L51) | The spectral radius of the actual mean matrix equals one. |
| [PerronWright.FiniteIrreducibleModel.perronFunction](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L124) | Positive fixed function normalized by `Σ μₐφₐ = 1`. |
| [PerronWright.FiniteIrreducibleModel.alpha](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L139) | `Σ μₐφₐ²`. |
| [PerronWright.FiniteIrreducibleModel.beta](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L142) | `Σ μₐφₐ³`. |
| [PerronWright.CompactBJRModel](../PerronWright/Model/CompactBJR.lean#L29) | Compact metric type space, full-support probability measure, and continuous symmetric nonnegative kernel. |
| [PerronWright.CompactBJRModel.B1](../PerronWright/Model/CompactBJR.lean#L93) | Existence of an associated compact self-adjoint L² operator with operator norm one. |
| [PerronWright.CompactBJRModel.B2](../PerronWright/Model/CompactBJR.lean#L174) | Some iterated kernel is strictly positive everywhere. |
| [PerronWright.CompactBJRModel.IsRegularCritical](../PerronWright/Model/CompactBJR.lean#L191) | `B1` and `B2`. |
| [PerronWright.CompactBJRModel.QP](../PerronWright/Probability/ProjectiveKernel.lean#L82) | The kernel has the specified projective representation. |
| [PerronWright.CompactBJRModel.perronFunction](../PerronWright/Model/PerronQuantities.lean#L22) | Positive fixed function normalized by `∫φ dμ = 1`. |
| [PerronWright.CompactBJRModel.alpha](../PerronWright/Model/PerronQuantities.lean#L92) | `∫φ² dμ`. |
| [PerronWright.CompactBJRModel.beta](../PerronWright/Model/PerronQuantities.lean#L96) | `∫φ³ dμ`. |

Here `QP` means **projective quadratic regularity** of the kernel, not a quasirandom type-count condition. It requires real coefficients `aⱼ` and continuous functions `fⱼ` such that `κ(x,y) = Σⱼ aⱼ fⱼ(x)fⱼ(y)` and `Σⱼ |aⱼ| ‖fⱼ‖∞² < ∞`; see [PerronWright.ProjectiveKernel.HasRepresentation](../PerronWright/Probability/ProjectiveKernel.lean#L47) for the exact definition. The compact-type probability results on this page additionally require `QP`. In contrast, the enumeration conclusion [PerronWright.CompactPerronWrightTheorem.compactPerronWright_theorem](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L232) requires only `IsRegularCritical`, not `QP`.

## 3. Actual graph sources and component counts

Both graph sources use the edge hazard `z = t κ(xᵢ,xⱼ)/n`. Conditional on the types, distinct edges are independent, and the edge-presence probability is **`1 − exp(−z)`**, not `z`. The finite-type source fixes the actual assignment; the compact-type source first samples types independently from `μ`, then samples edges conditionally.

Finite-type vertex types form a deterministic assignment sequence `xₙ : Fin n → S`; they are not resampled inside the graph law. The finite-type local formula and Brownian-limit results assume a single `D ≥ 0` such that, for all sufficiently large n and every type s, `|fiberCount(xₙ,s) − n M.weight(s)| ≤ D`. This controls actual empirical counts, rather than merely specifying ideal type proportions. It is a hypothesis of the asymptotic results, not a requirement for defining the graph source `FiniteIrreducibleTypedGraphLaw.law`.

| Fully qualified Lean name and location | Meaning |
| --- | --- |
| [PerronWright.IndependentEdges.edgeMass](../PerronWright/Probability/IndependentEdges.lean#L25) | Literal edge-presence/absence masses `1−exp(−z)` / `exp(−z)`. |
| [PerronWright.FiniteIrreducibleTypedGraphLaw.pairKernel](../PerronWright/Probability/FiniteIrreducibleTypedGraphLaw.lean#L27) | Actual pair kernel for a fixed assignment. |
| [PerronWright.FiniteIrreducibleTypedGraphLaw.hazard](../PerronWright/Probability/FiniteIrreducibleTypedGraphLaw.lean#L42) | `t κ/n`. |
| [PerronWright.FiniteIrreducibleTypedGraphLaw.law](../PerronWright/Probability/FiniteIrreducibleTypedGraphLaw.lean#L52) | Actual graph probability law for fixed types. |
| [PerronWright.AnnealedGraph.typeLaw](../PerronWright/Probability/AnnealedGraph.lean#L82) | Independent type product law. |
| [PerronWright.AnnealedGraph.hazard](../PerronWright/Probability/AnnealedGraph.lean#L86) | Actual conditional edge hazard in the compact-type model. |
| [PerronWright.AnnealedGraph.conditionalMass](../PerronWright/Probability/AnnealedGraph.lean#L95) | Conditional graph mass given the types. |
| [PerronWright.AnnealedGraph.mass](../PerronWright/Probability/AnnealedGraph.lean#L128) | Graph mass after integrating over the types. |
| [PerronWright.AnnealedGraph.law](../PerronWright/Probability/AnnealedGraph.lean#L166) | Actual annealed graph law. |
| [PerronWright.AnnealedTypedGraph.State](../PerronWright/Probability/AnnealedTypedGraph.lean#L31) | Joint state of the type and edge assignments. |
| [PerronWright.AnnealedTypedGraph.law](../PerronWright/Probability/AnnealedTypedGraph.lean#L39) | Actual joint type/graph law, the source of the empirically marked laws. |
| [PerronWright.FiniteIrreducibleTypePlacementMultiplicity.fiberCount](../PerronWright/Probability/FiniteIrreducibleTypePlacementMultiplicity.lean#L97) | Number of vertices of each type in the actual assignment. |
| [PerronWright.ComponentCounts.blockSurplus](../PerronWright/Probability/ComponentCounts.lean#L27) | `edges + 1 − vertices`. |
| [PerronWright.ComponentCounts.componentSize](../PerronWright/Probability/ComponentCounts.lean#L31) | Number of vertices in an actual connected component. |
| [PerronWright.ComponentCounts.componentSurplus](../PerronWright/Probability/ComponentCounts.lean#L35) | Surplus of an actual connected component. |
| [PerronWright.ComponentCounts.GoodComponentTuples](../PerronWright/Probability/ComponentCounts.lean#L46) | Ordered tuples of distinct actual components with prescribed sizes and surpluses. |
| [PerronWright.ComponentCounts.count](../PerronWright/Probability/ComponentCounts.lean#L60) | Cardinality of those tuples, not a graph-pattern surrogate. |

The actual source laws appearing in the twelve convergence declarations are:

| Fully qualified Lean name and location | Source law |
| --- | --- |
| [PerronWright.FiniteIrreducibleComponentProcess.graphLaw](../PerronWright/Probability/FiniteIrreducibleComponentProcess.lean#L28) | Finite-type graph law at critical time. |
| [PerronWright.FiniteIrreducibleComponentProcess.unmarkedProcessLaw](../PerronWright/Probability/FiniteIrreducibleComponentProcess.lean#L38) | Finite-type unmarked global law. |
| [PerronWright.FiniteIrreducibleComponentProcess.unmarkedWindowLaw](../PerronWright/Probability/FiniteIrreducibleComponentProcess.lean#L43) | Finite-type unmarked window law. |
| [PerronWright.ComponentWindowPointMeasures.unmarkedWindowLaw](../PerronWright/Probability/ComponentWindowPointMeasures.lean#L249) | Compact-type unmarked window law. |
| [PerronWright.ComponentGlobalPointProcess.unmarkedProcessLaw](../PerronWright/Probability/ComponentGlobalPointProcess.lean#L218) | Compact-type unmarked global law. |
| [PerronWright.FiniteIrreducibleMarkedComponentProcess.markedWindowLaw](../PerronWright/Probability/FiniteIrreducibleMarkedComponentProcess.lean#L46) | Finite-type window law with actual empirical marks. |
| [PerronWright.FiniteIrreducibleMarkedComponentProcess.markedProcessLaw](../PerronWright/Probability/FiniteIrreducibleMarkedComponentProcess.lean#L52) | Finite-type global law with actual empirical marks. |
| [PerronWright.ComponentWindowMarkedLaw.markedWindowLaw](../PerronWright/Probability/ComponentWindowMarkedLaw.lean#L77) | Compact-type window law with actual empirical marks. |
| [PerronWright.ComponentGlobalMarkedProcess.markedProcessLaw](../PerronWright/Probability/ComponentGlobalMarkedProcess.lean#L76) | Compact-type global law with actual empirical marks. |

## 4. Local scaling, density, and factorial tests

Let `q` be the number of ordered components, `rᵢ` their slotwise surpluses, and `xᵢ > 0` their scaled sizes. The local formula concerns `n^(2q/3) E[count]`. The density is defined by

\[
F_{\alpha,\beta,\lambda}(s)
=\frac{\beta s^3}{6}-\frac{\alpha\lambda s^2}{2}
+\frac{\alpha^2\lambda^2s}{2\beta},\qquad
g_r(x)=\frac{w_r\beta^{(r-1)/2}}{\sqrt{2\pi}}x^{3r/2-5/2},
\]

\[
\rho_q(x,r)=\exp\!\left(-F_{\alpha,\beta,\lambda}\!\left(\sum_i x_i\right)\right)
\prod_i g_{r_i}(x_i).
\]

The actual Aldous/Brownian factorial density is the special case `α = β = 1`.

| Fully qualified Lean name and location | Meaning |
| --- | --- |
| [PerronWright.CriticalScaling.time](../PerronWright/Probability/CriticalScaling.lean#L24) | `max(1+λ n^(−1/3),0)`; clipping for small n keeps the graph law well-defined. |
| [PerronWright.CriticalScaling.size](../PerronWright/Probability/CriticalScaling.lean#L49) | Literal floor `⌊x n^(2/3)⌋₊`. |
| [PerronWright.FiniteIrreducibleCriticalPrefactorScaling.rawTime](../PerronWright/Probability/FiniteIrreducibleCriticalPrefactorScaling.lean#L19) | The paper's raw time. |
| [PerronWright.FiniteIrreducibleCriticalPrefactorScaling.normalizedSize](../PerronWright/Probability/FiniteIrreducibleCriticalPrefactorScaling.lean#L22) | `k/n^(2/3)`. |
| [PerronWright.FiniteIrreducibleLocalMainIdentity.scaledFactorialExpectation](../PerronWright/Probability/FiniteIrreducibleLocalMainIdentity.lean#L34) | Scaled actual factorial expectation for fixed types. |
| [PerronWright.CompactAnnealedFactorialLocal.localExpectation](../PerronWright/Probability/CompactAnnealedFactorialLocal.lean#L27) | Annealed floor-scaled actual factorial expectation. |
| [PerronWright.FactorialDensity.sizeWindow](../PerronWright/Probability/FactorialWindowMass.lean#L21) | q-dimensional closed size window. |
| [PerronWright.PerronWrightFormulaMainTerm.wrightConstant](../PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L25) | Wright constant `wᵣ` for each surplus. |
| [PerronWright.FactorialDensity.criticalExponent](../PerronWright/Probability/FactorialDensity.lean#L19) | `F` above. |
| [PerronWright.FactorialDensity.sizeFactor](../PerronWright/Probability/FactorialDensity.lean#L24) | `gᵣ` above. |
| [PerronWright.FactorialDensity.density](../PerronWright/Probability/FactorialDensity.lean#L29) | Ordered q-point density above. |
| [PerronWright.FinitePointMeasureFactorialMeasure.factorialMeasure](../PerronWright/Probability/FinitePointMeasureFactorialMeasure.lean#L74) | Intrinsic factorial measure of ordered distinct atoms of the actual point measure. |
| [PerronWright.FinitePointMeasureFactorialKernel.rectangleTest](../PerronWright/Probability/FinitePointMeasureFactorialKernel.lean#L32) | Integral for slotwise rectangle restrictions and an arbitrary coupled test. |
| [PerronWright.BrownianExcursionRectangleFactorials.cells](../PerronWright/Probability/BrownianExcursionRectangleFactorials.lean#L32) | Slotwise cells `Icc(aᵢ,bᵢ) × {rᵢ}`. |
| [PerronWright.BrownianExcursionRectangleFactorials.windowSet](../PerronWright/Probability/BrownianExcursionRectangleFactorials.lean#L39) | Union of the slotwise cells. |
| [PerronWright.BrownianExcursionFactorialTests.factorialTest](../PerronWright/Probability/BrownianExcursionFactorialTests.lean#L34) | Intrinsic factorial test on the actual window point measure. |
| [PerronWright.BrownianExcursionDeletionTupleSource.sourceSum](../PerronWright/Probability/BrownianExcursionDeletionTupleSource.lean#L31) | Ordered excursion source sum with Poisson weights from full excursion areas. |
| [PerronWright.ComponentWindowMixedFactorials.sizeSurplusCells](../PerronWright/Probability/ComponentWindowMixedFactorials.lean#L146) | Size/surplus cells `Jᵢ × Sᵢ`. |
| [PerronWright.FactorialCountDeterminacy.factorialPolynomial](../PerronWright/Probability/FactorialCountDeterminacy.lean#L101) | Product of the descending factorials of the cell counts. |
| [PerronWright.FactorialCountDeterminacy.factorialMoment](../PerronWright/Probability/FactorialCountDeterminacy.lean#L104) | Expectation of that polynomial. |
| [PerronWright.BrownianActualArbitraryWindowCellMoments.mixedStatistic](../PerronWright/Probability/BrownianActualArbitraryWindowCellMoments.lean#L30) | Mixed factorial count statistic on an arbitrary window. |
| [PerronWright.BrownianActualArbitraryWindowCellMoments.cellCountLaw](../PerronWright/Probability/BrownianActualArbitraryWindowCellMoments.lean#L187) | Joint cell-count law on an arbitrary actual Brownian window. |
| [PerronWright.CompactSizeCellFactorialLimits.cellMomentMass](../PerronWright/Probability/CompactSizeCellFactorialLimits.lean#L31) | Literal density integral retaining all slot multiplicities. |

For eventual agreement between clipped time and the paper's raw time, see [PerronWright.CriticalScaling.time_eq_raw_eventually](../PerronWright/Probability/CriticalScaling.lean#L36).

## 5. Point-measure spaces and topologies

Window point measures carry the **weak topology** inherited from `FiniteMeasure` and its Borel sigma algebra. Global locally finite point measures carry the **vague topology**, induced by integration against all compactly supported continuous tests, and its Borel sigma algebra. In the convergence results, `Tendsto` expresses weak convergence of probability laws on these point-measure spaces. The topology on the point measures and convergence of their probability laws are two different levels.

| Fully qualified Lean name and location | Meaning |
| --- | --- |
| [PerronWright.FinitePointMeasureCompact.IsPointMeasure](../PerronWright/Probability/FinitePointMeasureCompact.lean#L28) | Finite integer sum of Dirac measures, allowing multiplicities and the zero measure. |
| [PerronWright.FinitePointMeasureCompact.PointMeasure](../PerronWright/Probability/FinitePointMeasureCompact.lean#L33) | Space of actual finite point measures. |
| [PerronWright.FinitePointMeasureCompact.size](../PerronWright/Probability/FinitePointMeasureCompact.lean#L97) | Number of points, counting multiplicity. |
| [PerronWright.FinitePointMeasureCompact.count](../PerronWright/Probability/FinitePointMeasureCompact.lean#L112) | Number of points in a set. |
| [PerronWright.FinitePointMeasureCompact.SurplusWindow](../PerronWright/Probability/FinitePointMeasureCompact.lean#L250) | `Icc a b × Fin(R+1)`. |
| [PerronWright.LocallyFinitePointMeasureVague.IsLocallyFinitePointMeasure](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L25) | Local finiteness, with each compact restriction a finite integer sum of Dirac measures. |
| [PerronWright.LocallyFinitePointMeasureVague.LocalPointMeasure](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L29) | Space of actual global locally finite point measures. |
| [PerronWright.LocallyFinitePointMeasureVague.testEncoding](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L42) | Integrals against all `C_c` tests. |
| [PerronWright.ComponentGlobalPointProcess.PositiveSizeSurplus](../PerronWright/Probability/ComponentGlobalPointProcess.lean#L25) | `(0,∞) × ℕ`. |
| [PerronWright.ComponentWindowPointMeasures.windowEmbedding](../PerronWright/Probability/ComponentWindowPointMeasures.lean#L31) | Embedding of window coordinates into the ambient size/surplus space. |
| [PerronWright.ComponentWindowPointMeasures.windowPointMeasure](../PerronWright/Probability/ComponentWindowPointMeasures.lean#L78) | Integer point measure of the actual components in a window. |
| [PerronWright.ComponentGlobalPointProcess.unmarkedProcess](../PerronWright/Probability/ComponentGlobalPointProcess.lean#L58) | Positive-size/surplus point measure of all actual components. |

Topology and Borel instance locations: [finite weak topology](../PerronWright/Probability/FinitePointMeasureCompact.lean#L61), [finite weak-Borel structure](../PerronWright/Probability/FinitePointMeasureCompact.lean#L66), [global vague topology](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L45), and [global vague-Borel structure](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L48).

## 6. Actual Brownian source and Aldous law

The target law is not a candidate process defined solely by a density. Starting from the continuous Brownian whole-path law, the construction forms `B(t)+λt−t²/2`, reflects it at its running minimum, takes its full positive excursions, and attaches a Poisson surplus to each excursion with conditional rate equal to its full area. The Poisson marks are **independent conditional on the path**, not unconditionally independent of the path. The global point-process law is the pushforward of this actual joint path/mark law.

| Fully qualified Lean name and location | Meaning |
| --- | --- |
| [PerronWright.BrownianPathLaw.Path](../PerronWright/Probability/BrownianPathLaw.lean#L32) | Continuous whole-path space `C(ℝ≥0,ℝ)`. |
| [PerronWright.BrownianPathLaw.pathLaw](../PerronWright/Probability/BrownianPathLaw.lean#L111) | Actual Brownian whole-path law. |
| [PerronWright.BrownianPathReflectionLaw.reflectionPath](../PerronWright/Probability/BrownianPathReflectionLaw.lean#L30) | Subtraction of the running minimum. |
| [PerronWright.BrownianPathReflectionLaw.driftPath](../PerronWright/Probability/BrownianPathReflectionLaw.lean#L33) | `B(t)+λt−t²/2`. |
| [PerronWright.BrownianPathReflectionLaw.driftedReflectionPath](../PerronWright/Probability/BrownianPathReflectionLaw.lean#L36) | Reflection of that drifted path. |
| [PerronWright.FullHorizonExcursionComponents.component](../PerronWright/Probability/FullHorizonExcursionComponents.lean#L27) | Connected component of a positive excursion. |
| [PerronWright.FullHorizonExcursionComponents.leftEndpoint](../PerronWright/Probability/FullHorizonExcursionComponents.lean#L117) | Left endpoint of a full excursion. |
| [PerronWright.FullHorizonExcursionComponents.rightEndpoint](../PerronWright/Probability/FullHorizonExcursionComponents.lean#L120) | Right endpoint of a full excursion. |
| [PerronWright.FullHorizonExcursionComponents.length](../PerronWright/Probability/FullHorizonExcursionComponents.lean#L123) | Full, not truncated, excursion length. |
| [PerronWright.FullHorizonExcursionSection.Representative](../PerronWright/Probability/FullHorizonExcursionSection.lean#L75) | A distinct rational representative for each excursion. |
| [PerronWright.BrownianFullHorizonExcursionAreas.excursionArea](../PerronWright/Probability/BrownianFullHorizonExcursionAreas.lean#L51) | Full, not truncated, excursion area. |
| [PerronWright.BrownianFullHorizonPoissonMarks.naturalRates](../PerronWright/Probability/BrownianFullHorizonPoissonMarks.lean#L28) | Conditional rates given by full excursion areas. |
| [PerronWright.BrownianFullHorizonPoissonMarks.markLaw](../PerronWright/Probability/BrownianFullHorizonPoissonMarks.lean#L78) | Conditional Poisson mark law given the path. |
| [PerronWright.BrownianFullHorizonPoissonMarks.pathJointLaw](../PerronWright/Probability/BrownianFullHorizonPoissonMarks.lean#L174) | Actual joint law of the path and surplus marks. |
| [PerronWright.BrownianExcursionAtomicMeasure.measure](../PerronWright/Probability/BrownianExcursionAtomicMeasure.lean#L51) | Actual atomic excursion measure. |
| [PerronWright.BrownianExcursionAtomicMeasure.process](../PerronWright/Probability/BrownianExcursionAtomicMeasure.lean#L141) | Actual global locally finite excursion point measure. |
| [PerronWright.BrownianExcursionPointProcessLaw.law](../PerronWright/Probability/BrownianExcursionPointProcessLaw.lean#L45) | Actual Aldous global probability law. |
| [PerronWright.BrownianExcursionPointProcessLaw.windowLaw](../PerronWright/Probability/BrownianExcursionPointProcessLaw.lean#L53) | Actual Brownian law in the canonical chart. |
| [PerronWright.BrownianArbitraryWindowLaw.pointMeasure](../PerronWright/Probability/BrownianArbitraryWindowLaw.lean#L150) | Actual Brownian point measure on any closed positive-size window. |
| [PerronWright.BrownianArbitraryWindowLaw.law](../PerronWright/Probability/BrownianArbitraryWindowLaw.lean#L183) | Actual Brownian probability law on any closed positive-size window. |
| [PerronWright.BrownianExcursionCompactWindows.law](../PerronWright/Probability/BrownianExcursionCompactWindows.lean#L72) | Actual law on any compact-set window, as used in the density result. |

## 7. Actual empirical marks, Perron marks, and the TV distinction

The mark of an actual component `C` is the probability measure `|C|⁻¹ Σ_{v∈C} δ_{xᵥ}`, not a prescribed profile. The deterministic limiting Perron mark is `φ dμ`, or `Σₐ μₐφₐ δₐ` in the finite-type case. It generally differs from the original sampling law `μ`. The constructions `canonicalPerronMarkedLaw` and `canonicalGlobalMarkedLaw` attach this same Perron probability measure to every atom of the unmarked target.

Marks in the twelve finite-type/compact-type convergence declarations carry the **weak topology** on actual probability measures, with the Borel structure selected by `WeakMark`. This is different from the total-variation topology in the countable-type local TV-marked conclusion. The marked global laws on this page must not be interpreted as global TV-product marked laws.

| Fully qualified Lean name and location | Meaning |
| --- | --- |
| [PerronWright.EmpiricalTypeMarks.empiricalMeasure](../PerronWright/Probability/EmpiricalTypeMarks.lean#L31) | Actual empirical measure of a block. |
| [PerronWright.EmpiricalTypeMarks.empiricalProbability](../PerronWright/Probability/EmpiricalTypeMarks.lean#L45) | Empirical probability measure of a nonempty block. |
| [PerronWright.EmpiricalTypeMarks.componentMark](../PerronWright/Probability/EmpiricalTypeMarks.lean#L75) | Empirical mark of an actual component. |
| [PerronWright.EmpiricalTypeMarks.perronMark](../PerronWright/Probability/EmpiricalTypeMarks.lean#L118) | Compact-type Perron probability mark. |
| [PerronWright.WeakProbabilityMarks.WeakMark](../PerronWright/Probability/WeakProbabilityMarks.lean#L17) | Weak-Borel wrapper whose values are still actual elements of `ProbabilityMeasure S`. |
| [PerronWright.WeakProbabilityMarks.homeomorph](../PerronWright/Probability/WeakProbabilityMarks.lean#L27) | Homeomorphism with the actual weak topology on probability measures. |
| [PerronWright.FiniteIrreducibleConnectedTypeLaw.perronLaw](../PerronWright/Probability/FiniteIrreducibleConnectedTypeLaw.lean#L43) | Finite-type Perron probability law. |
| [PerronWright.FiniteIrreducibleMarkedComponentProcess.perronWeakMark](../PerronWright/Probability/FiniteIrreducibleMarkedComponentProcess.lean#L31) | Finite-type Perron weak mark. |
| [PerronWright.ComponentWindowMarkedTransfer.perronWeakMark](../PerronWright/Probability/ComponentWindowMarkedTransfer.lean#L28) | Compact-type Perron weak mark. |
| [PerronWright.ComponentWindowMarkedLaw.MarkedWindow](../PerronWright/Probability/ComponentWindowMarkedLaw.lean#L29) | `SurplusWindow × WeakMark`. |
| [PerronWright.ComponentWindowMarkedLaw.markedWindowPointMeasure](../PerronWright/Probability/ComponentWindowMarkedLaw.lean#L40) | Actual empirically marked window point measure. |
| [PerronWright.ComponentGlobalMarkedProcess.MarkedPositiveSizeSurplus](../PerronWright/Probability/ComponentGlobalMarkedProcess.lean#L33) | `PositiveSizeSurplus × WeakMark`. |
| [PerronWright.ComponentGlobalMarkedProcess.markedProcess](../PerronWright/Probability/ComponentGlobalMarkedProcess.lean#L45) | Actual empirically marked global point measure. |
| [PerronWright.GlobalPointMeasureMarking.constantMark](../PerronWright/Probability/GlobalPointMeasureMarking.lean#L53) | Point-measure pushforward attaching the same probability mark to every atom. |
| [PerronWright.FiniteIrreducibleMarkedWindowConvergence.canonicalPerronMarkedLaw](../PerronWright/Probability/FiniteIrreducibleMarkedWindowConvergence.lean#L26) | Finite-type Perron-marked window target law. |
| [PerronWright.ComponentWindowMarkedConvergence.canonicalPerronMarkedLaw](../PerronWright/Probability/ComponentWindowMarkedConvergence.lean#L27) | Compact-type Perron-marked window target law. |
| [PerronWright.FiniteIrreducibleMarkedGlobalTests.canonicalGlobalMarkedLaw](../PerronWright/Probability/FiniteIrreducibleMarkedGlobalTests.lean#L33) | Finite-type Perron-marked global target law. |
| [PerronWright.GlobalPointMeasureMarking.canonicalGlobalMarkedLaw](../PerronWright/Probability/GlobalPointMeasureMarking.lean#L78) | Compact-type Perron-marked global target law. |

## 8. Starred and inverse Brownian normalizations

The paper's starred transformation multiplies only the size by `c = β^(1/3)`; it leaves surplus and actual empirical marks unchanged. The target Brownian parameter is `λ⋆ = α β^(−2/3) λ`. The unstarred global target is the actual Brownian law at `λ⋆`, with sizes multiplied by `c⁻¹`. The starred global target is that Brownian law itself. The unstarred window target first restricts the Brownian process to `[ca,cb]`, then multiplies sizes by `c⁻¹` to return to `[a,b]`.

| Fully qualified Lean name and location | Meaning |
| --- | --- |
| [PerronWright.ComponentPointProcesses.sizeScale](../PerronWright/Probability/PointProcessNormalization.lean#L37) | Compact-type `β^(1/3)`. |
| [PerronWright.ComponentPointProcesses.aldousParameter](../PerronWright/Probability/PointProcessNormalization.lean#L45) | Compact-type `αβ^(−2/3)λ`. |
| [PerronWright.FiniteIrreduciblePointProcessNormalization.sizeScale](../PerronWright/Probability/FiniteIrreduciblePointProcessNormalization.lean#L26) | Finite-type `β^(1/3)`. |
| [PerronWright.FiniteIrreduciblePointProcessNormalization.paperParameter](../PerronWright/Probability/FiniteIrreduciblePointProcessNormalization.lean#L41) | Finite-type `αβ^(−2/3)λ`. |
| [PerronWright.GlobalPointSizeRescaling.positiveSizeScale](../PerronWright/Probability/GlobalPointSizeRescaling.lean#L25) | Size-dilation homeomorphism on the positive-size base space. |
| [PerronWright.GlobalPointSizeRescaling.scalePoint](../PerronWright/Probability/GlobalPointSizeRescaling.lean#L53) | Actual dilation pushforward of a global point measure. |
| [PerronWright.GlobalPointSizeRescaling.starredProcessLaw](../PerronWright/Probability/GlobalPointSizeRescaling.lean#L112) | Compact-type starred unmarked global source law. |
| [PerronWright.GlobalMarkedPointSizeRescaling.scaleMarkedPoint](../PerronWright/Probability/GlobalMarkedPointSizeRescaling.lean#L52) | Global size dilation leaving marks unchanged. |
| [PerronWright.GlobalMarkedPointSizeRescaling.starredMarkedProcessLaw](../PerronWright/Probability/GlobalMarkedPointSizeRescaling.lean#L156) | Compact-type starred empirically marked global source law. |
| [PerronWright.FiniteIrreducibleGlobalSizeRescaling.starredProcessLaw](../PerronWright/Probability/FiniteIrreducibleGlobalSizeRescaling.lean#L77) | Finite-type starred unmarked global source law. |
| [PerronWright.FiniteIrreducibleGlobalMarkedSizeRescaling.starredMarkedProcessLaw](../PerronWright/Probability/FiniteIrreducibleGlobalMarkedSizeRescaling.lean#L148) | Finite-type starred empirically marked global source law. |
| [PerronWright.BrownianInverseSizeLaw.inverseScaledLaw](../PerronWright/Probability/BrownianInverseSizeLaw.lean#L41) | Inverse-size dilation of the actual Brownian global law. |
| [PerronWright.BrownianInverseWindowLaw.law](../PerronWright/Probability/BrownianInverseWindowLaw.lean#L24) | Inverse-size dilation of the actual arbitrary-window Brownian law. |

An individual `#print axioms` entry for each of the twelve Brownian-limit declarations is available in [ModelActualBrownianLimitsAudit.lean](../PerronWright/Probability/ModelActualBrownianLimitsAudit.lean#L3). These commands print logical axiom dependencies, not the full graph of intermediate theorem dependencies. The one-click verification entry distinguishes these two reports.
