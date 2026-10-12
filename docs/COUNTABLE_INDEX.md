# Theorems 3.9 and 3.10: countable types, definitions, and exact scope

This page indexes **Theorem 3.9 (Countable type critical realization)** and **Theorem 3.10 (Countable type limits without spectral renormalization)**. The former constructs a spectrally normalized critical realization; the latter treats the same realization without spectral renormalization, subject to a spectral-drift condition. All links point to this repository's Lean sources. This page explains their statements, rather than recording verification results.

## Joint Lean entry for Theorems 3.9 and 3.10

Fully qualified declaration:

```text
PerronWright.CountableActualBrownianLimits.exists_actual_growing_Brownian_global_and_TV_window_limits
```

Location: [CountableActualBrownianLimits.lean, line 90](../PerronWright/Probability/CountableActualBrownianLimits.lean#L90). This joint theorem supplies both paper results using the same integer realization, not two separately chosen realizations.

Its model inputs are `M : CountableKernel`, `hM : M.IsRegularCritical`, and witnesses of `0 < lower` and `lower ≤ M.kernel s t`. Such a lower bound is already part of regular criticality; the witness is not an additional model assumption. The preceding [`omit level hlocal in`](../PerronWright/Probability/CountableActualBrownianLimits.lean#L86) makes explicit that the support sequence is constructed in the conclusion and that the local-limit estimates are not external assumptions.

### What the same outermost `∃ level` provides

| Joint conclusion | Location in the theorem |
| --- | --- |
| `level` is monotone, tends to infinity, and satisfies `level N ≤ N`; the counts sum exactly to `N`, and every retained type has a strictly positive count when `N>0` | [Line 91](../PerronWright/Probability/CountableActualBrownianLimits.lean#L91) |
| The actual empirical probability measures converge to the original `μ` in atomic absolute variation; `N^(1/3)` times the smallest retained empirical type proportion tends to infinity | [Line 97](../PerronWright/Probability/CountableActualBrownianLimits.lean#L97) |
| Local factorial expectations of the spectrally normalized graph source converge to the density with the original `α,β`, uniformly for each fixed order, surplus bound, positive size window, and bounded critical-parameter interval | [Line 104](../PerronWright/Probability/CountableActualBrownianLimits.lean#L104) |
| Under the actual empirical spectral-drift condition, local expectations of the same raw graph source converge to the density at parameter `λ+θ` | [Line 110](../PerronWright/Probability/CountableActualBrownianLimits.lean#L110) |
| Spectrally normalized starred global unmarked graph laws converge to the actual full-excursion Brownian law | [Line 120](../PerronWright/Probability/CountableActualBrownianLimits.lean#L120) |
| Under the spectral-drift condition, the same raw starred global unmarked graph laws converge to the corresponding Brownian law | [Line 124](../PerronWright/Probability/CountableActualBrownianLimits.lean#L124) |
| Spectrally normalized starred unmarked laws and actual empirical-TV-marked laws converge on every positive closed size window with bounded surplus | [Line 131](../PerronWright/Probability/CountableActualBrownianLimits.lean#L131) |
| Under the spectral-drift condition, the same raw starred unmarked and empirical-TV-marked window laws converge | [Line 139](../PerronWright/Probability/CountableActualBrownianLimits.lean#L139) |
| For the normalized model, the expected sum of mark distances in a window and the probability of a bad mark tend to zero | [Line 150](../PerronWright/Probability/CountableActualBrownianLimits.lean#L150) |
| Under the spectral-drift condition, the corresponding expected mark distance and bad-mark probability for the raw model tend to zero | [Line 155](../PerronWright/Probability/CountableActualBrownianLimits.lean#L155) |

The quantifier `∃ level` precedes every `λ`, `θ`, factorial order, and window parameter. Thus all conclusions use the same vertex-type assignment, positive integer-count construction, and exhausting support sequence, without selecting a new realization for each parameter.

### Indexing, spectral drift, and the starred parameter

The Lean graph-sequence index is `n`; the actual number of vertices is `N = n+1`. The support is `{0,…,level N}`, and its actual spectral radius is `σ_n = M.empiricalSpectralRadius level n`.

The raw graph branch requires precisely:

```text
(n+1)^(1/3) * (M.empiricalSpectralRadius level n - 1) → θ.
```

Under this condition, the raw local-density parameter is `λ+θ`. The actual Brownian parameter of the global and window starred limits is:

```text
Spectrally normalized source: α * β^(-2/3) * λ
Raw graph source:             α * β^(-2/3) * (λ+θ)
```

The shift `θ` is inside the scaling factor. This condition concerns the actual empirical kernel, not a separately chosen approximate spectral root. Regular criticality alone is not asserted to imply an arbitrary prescribed drift or zero drift. The zero-drift result is the `θ=0` specialization of this conditional branch.

The starred size coordinate multiplies `|C|/N^(2/3)` by the original countable model's `β^(1/3)`; surplus and actual empirical type marks are unchanged. The original `β` is not replaced by each empirical finite model's own `β_n`.

### Topology and window scope

- The global conclusions concern **unmarked** laws only. The base space is `(0,∞) × ℕ`; locally finite integer point measures carry the vague topology, and their probability laws converge weakly.
- The marked conclusions are weak convergence of probability laws on local windows. The closed window is `[a,b] × {0,…,R}`, with `0<a≤b`, including both endpoints. The public theorem does not ask the user to supply an additional boundary-null proof.
- The marked base space is the product of this window with `VariationMark`. Its mark distance is `Σ_s |p{s}-q{s}|`, twice the total-variation distance under the convention `sup_A |p(A)-q(A)|`.
- A “TV-marked limit” refers to this total-variation topology on marks. It does not mean total-variation convergence of the entire point-process probability laws, and it does not assert a global TV-product marked point-process limit.
- The target marked law adds the original constant Perron mark to the unmarked Brownian window law. The finite graph sources still use each actual component's own empirical mark.

## 1. Model assumptions and original Perron quantities

| Meaning | Fully qualified Lean declaration and location |
| --- | --- |
| Type space `ℕ`, probability measure `μ` with every atomic mass positive, and bounded symmetric nonnegative kernel `κ` | [`PerronWright.CountableKernel`](../PerronWright/Model/CountableKernel.lean#L19) |
| Original `L²(μ)` space | [`PerronWright.CountableKernel.L2`](../PerronWright/Kernel/CountableIntegral.lean#L21) |
| Pointwise integral-kernel action `∫ κ(a,b)v(b) dμ(b)` | [`PerronWright.CountableKernel.pointwiseAction`](../PerronWright/Kernel/CountableIntegral.lean#L54) |
| Corresponding continuous linear operator | [`PerronWright.CountableKernel.actionCLM`](../PerronWright/Kernel/CountableIntegral.lean#L106) |
| Criticality: the original operator has spectral radius one | [`PerronWright.CountableKernel.IsCritical`](../PerronWright/Kernel/CountablePerron.lean#L19) |
| Regular criticality: criticality together with a uniform strictly positive kernel lower bound | [`PerronWright.CountableKernel.IsRegularCritical`](../PerronWright/Model/CountablePerronQuantities.lean#L18) |
| Existence and uniqueness of a normalized positive Perron fixed vector | [`PerronWright.CountableKernel.IsRegularCritical.existsUnique_normalized_positive_fixed`](../PerronWright/Model/CountablePerronQuantities.lean#L21) |
| Normalized positive vector `u` selected from that existence-and-uniqueness theorem | [`PerronWright.CountableKernel.perronVector`](../PerronWright/Model/CountablePerronQuantities.lean#L27) |
| `u>0` | [`PerronWright.CountableKernel.perronVector_pos`](../PerronWright/Model/CountablePerronQuantities.lean#L30) |
| `Ku=u` | [`PerronWright.CountableKernel.perronVector_fixed`](../PerronWright/Model/CountablePerronQuantities.lean#L34) |
| `∫u dμ=1` | [`PerronWright.CountableKernel.perronVector_integral`](../PerronWright/Model/CountablePerronQuantities.lean#L38) |
| Perron probability measure `u·μ`, with density `u` | [`PerronWright.CountableKernel.perronLaw`](../PerronWright/Model/CountablePerronQuantities.lean#L52) |
| Quadratic scale `α=∫u² dμ` | [`PerronWright.CountableKernel.alpha`](../PerronWright/Model/CountablePerronQuantities.lean#L92) |
| Cubic scale `β=∫u³ dμ` | [`PerronWright.CountableKernel.beta`](../PerronWright/Model/CountablePerronQuantities.lean#L95) |

## 2. Growing supports, integer counts, and empirical spectral roots

The count construction first normalizes the original weights on the initial support `{0,…,m}`, then rounds them. All rounding remainder is assigned to type `0`. The actual vertex assignment realizes these counts, rather than merely supplying real-valued weights. The theorem asserts positive counts and an empirical probability measure for `N>0`; it does not require the empirical measure to be a probability measure at `N=0`.

| Meaning | Fully qualified Lean declaration and location |
| --- | --- |
| Original atomic weights `w(a)=μ.real {a}` | [`PerronWright.CountableTypeRealization.weights`](../PerronWright/Probability/CountableTypeRealization.lean#L28) |
| Truncated mass `Σ_{a≤m} w(a)` | [`PerronWright.GrowingTypeCounts.mass`](../PerronWright/Probability/GrowingTypeCounts.lean#L23) |
| Normalized truncated distribution `w(a)/mass(w,m)` | [`PerronWright.GrowingTypeCounts.truncatedLaw`](../PerronWright/Probability/GrowingTypeCounts.lean#L46) |
| Rounded finite-type counts and remainder allocation | [`PerronWright.FiniteTypeCounts.counts`](../PerronWright/Model/FiniteTypeCounts.lean#L32) |
| Truncated integer counts summing exactly to `N` | [`PerronWright.GrowingTypeCounts.truncatedCounts`](../PerronWright/Probability/GrowingTypeCounts.lean#L57) |
| Finite empirical frequencies obtained by dividing these counts by `N` | [`PerronWright.GrowingTypeCounts.empiricalLaw`](../PerronWright/Probability/GrowingTypeCounts.lean#L60) |
| Support `{0,…,level N}` | [`PerronWright.GrowingTypeCounts.support`](../PerronWright/Probability/GrowingTypeCounts.lean#L137) |
| Natural-number type assigned to every actual vertex | [`PerronWright.CountableTypeRealization.vertexTypes`](../PerronWright/Probability/CountableTypeRealization.lean#L30) |
| Actual empirical measure of vertex types | [`PerronWright.CountableTypeRealization.empiricalMeasure`](../PerronWright/Probability/CountableTypeRealization.lean#L65) |
| Empirical atomic weights at graph index `n`, with `N=n+1` | [`PerronWright.CountableKernel.empiricalWeights`](../PerronWright/Kernel/CountableApproximationEmpirical.lean#L33) |
| Actual operator associated with the empirical weights | [`PerronWright.CountableKernel.empiricalOperator`](../PerronWright/Kernel/CountableApproximationEmpirical.lean#L51) |
| Empirical spectral radius `σ_n` of that operator | [`PerronWright.CountableKernel.empiricalSpectralRadius`](../PerronWright/Kernel/CountableApproximationEmpirical.lean#L55) |
| Real-valued construction of the weighted integral operator's spectral radius | [`PerronWright.CountableKernel.weightedSpectralRadius`](../PerronWright/Kernel/CountableApproximationSpectral.lean#L69) |

## 3. Normalized and raw independent-edge graph sources

Set `N=n+1` and `t_N=max(1+λN^(-1/3),0)`, and assign vertex types using the integer realization above. For an edge whose endpoint types are `s,t`:

```text
Spectrally normalized hazard: z = t_N * κ(s,t) / (N * σ_n)
Raw graph hazard:             z = t_N * κ(s,t) / N
Actual edge probability:      1 - exp(-z)
```

Here `z` is a hazard, not itself the edge probability. The graph law is the actual independent joint law of all edges. The effective parameter rewrites the entire raw graph law exactly as a normalized law, not merely the marginal distribution of one edge.

| Meaning | Fully qualified Lean declaration and location |
| --- | --- |
| Critical time `t_N`; truncation only prevents negative time at small graph sizes | [`PerronWright.CriticalScaling.time`](../PerronWright/Probability/CriticalScaling.lean#L24) |
| Boolean probability mass of a single edge with a given hazard | [`PerronWright.IndependentEdges.edgeMass`](../PerronWright/Probability/IndependentEdges.lean#L25) |
| Actual labelled independent-edge graph law | [`PerronWright.FixedTypeGraph.law`](../PerronWright/Probability/FixedTypeGraph.lean#L31) |
| Spectrally normalized hazards | [`PerronWright.CountableKernel.empiricalNormalizedHazards`](../PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L25) |
| Spectrally normalized actual graph law | [`PerronWright.CountableKernel.empiricalNormalizedGraphLaw`](../PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L41) |
| Raw hazards | [`PerronWright.CountableKernel.empiricalUnnormalizedHazards`](../PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L66) |
| Raw actual graph law | [`PerronWright.CountableKernel.empiricalUnnormalizedGraphLaw`](../PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L78) |
| Effective parameter `N^(1/3)((1+λN^(-1/3))σ-1)` | [`PerronWright.CriticalParameterDrift.effectiveParameter`](../PerronWright/Probability/CriticalParameterDrift.lean#L22) |
| Effective parameter using the actual empirical spectral root, reindexed by `N=n+1` | [`PerronWright.CountableKernel.empiricalEffectiveParameter`](../PerronWright/Probability/CountableEmpiricalSpectralDrift.lean#L17) |
| Equality of the full raw and normalized graph laws | [`PerronWright.CountableKernel.empiricalUnnormalizedGraphLaw_eq_normalized`](../PerronWright/Probability/CountableEmpiricalGraphLaw.lean#L90) |

## 4. Local numerical expectations and target factorial density

The order-`q` count is the number of ordered, pairwise distinct tuples of actual connected components. Component `i` must have size `⌊y_i N^(2/3)⌋₊` and surplus `r_i`; surplus is `number of edges + 1 - number of vertices`. The local quantity in the theorem is `N^(2q/3)` times the expectation of this count, integrated against the normalized or raw actual graph law, respectively.

| Meaning | Fully qualified Lean declaration and location |
| --- | --- |
| Actual component size | [`PerronWright.ComponentCounts.componentSize`](../PerronWright/Probability/ComponentCounts.lean#L31) |
| Actual component surplus | [`PerronWright.ComponentCounts.componentSurplus`](../PerronWright/Probability/ComponentCounts.lean#L35) |
| Ordered distinct component tuples with matching sizes and surpluses | [`PerronWright.ComponentCounts.GoodComponentTuples`](../PerronWright/Probability/ComponentCounts.lean#L46) |
| Actual factorial tuple count | [`PerronWright.ComponentCounts.count`](../PerronWright/Probability/ComponentCounts.lean#L60) |
| Critical size with literal integer rounding | [`PerronWright.CriticalScaling.size`](../PerronWright/Probability/CriticalScaling.lean#L49) |
| Normalized local expectation | [`PerronWright.CountableKernel.growingLocalExpectation`](../PerronWright/Probability/CountableFixedSupportGrowingSource.lean#L32) |
| Raw local expectation | [`PerronWright.CountableKernel.growingUnnormalizedLocalExpectation`](../PerronWright/Probability/CountableUnnormalizedLocalTerminal.lean#L23) |
| Surplus-indexed Wright constant | [`PerronWright.PerronWrightFormulaMainTerm.wrightConstant`](../PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L25) |
| Critical population exponent polynomial | [`PerronWright.FactorialDensity.criticalExponent`](../PerronWright/Probability/FactorialDensity.lean#L19) |
| Size factor for a single surplus coordinate | [`PerronWright.FactorialDensity.sizeFactor`](../PerronWright/Probability/FactorialDensity.lean#L24) |
| Target ordered `q`-point factorial density | [`PerronWright.FactorialDensity.density`](../PerronWright/Probability/FactorialDensity.lean#L29) |

## 5. Global point measures, closed windows, and starred laws

An actual component atom is `(c * |C| / N^(2/3), surplus(C))`. Every component contributes one Dirac atom, with multiplicity retained. The unstarred coordinate has `c=1`; the starred coordinate in this theorem has `c=β^(1/3)`.

| Meaning | Fully qualified Lean declaration and location |
| --- | --- |
| Global positive-size/surplus base space `(0,∞)×ℕ` | [`PerronWright.ComponentGlobalPointProcess.PositiveSizeSurplus`](../PerronWright/Probability/ComponentGlobalPointProcess.lean#L25) |
| Local finiteness with a finite integer atomic sum on each compact set | [`PerronWright.LocallyFinitePointMeasureVague.IsLocallyFinitePointMeasure`](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L25) |
| Space of locally finite integer point measures | [`PerronWright.LocallyFinitePointMeasureVague.LocalPointMeasure`](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L29) |
| Vague topology defined by integrals against compactly supported continuous test functions | [`PerronWright.LocallyFinitePointMeasureVague.testEncoding`](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L42); [topology instance](../PerronWright/Probability/LocallyFinitePointMeasureVague.lean#L45) |
| Space of finite integer point measures | [`PerronWright.FinitePointMeasureCompact.PointMeasure`](../PerronWright/Probability/FinitePointMeasureCompact.lean#L33) |
| Weak topology on finite point measures | [`TopologicalSpace` instance in `PerronWright.FinitePointMeasureCompact`](../PerronWright/Probability/FinitePointMeasureCompact.lean#L61) |
| Closed window `[a,b]×{0,…,R}` | [`PerronWright.FinitePointMeasureCompact.SurplusWindow`](../PerronWright/Probability/FinitePointMeasureCompact.lean#L250) |
| Actual component size/surplus atom | [`PerronWright.ComponentWindowPointMeasures.componentAtom`](../PerronWright/Probability/ComponentWindowPointMeasures.lean#L49) |
| Actual components lying in a closed window | [`PerronWright.ComponentWindowPointMeasures.WindowComponent`](../PerronWright/Probability/ComponentWindowPointMeasures.lean#L58) |
| Actual window point measure, with one atom per selected component | [`PerronWright.ComponentWindowPointMeasures.windowPointMeasure`](../PerronWright/Probability/ComponentWindowPointMeasures.lean#L78) |
| Starred multiplier `β^(1/3)` using the original countable cubic scale | [`PerronWright.CountableStarredGlobalSizeRescaling.sizeScale`](../PerronWright/Probability/CountableStarredGlobalSizeRescaling.lean#L26) |
| Normalized starred global unmarked law | [`PerronWright.CountableStarredGlobalSizeRescaling.normalizedStarredProcessLaw`](../PerronWright/Probability/CountableStarredGlobalSizeRescaling.lean#L32) |
| Raw starred global unmarked law | [`PerronWright.CountableStarredGlobalSizeRescaling.unnormalizedStarredProcessLaw`](../PerronWright/Probability/CountableStarredGlobalSizeRescaling.lean#L37) |
| Normalized starred unmarked closed-window law | [`PerronWright.CountableStarredTVWindowLaw.normalizedStarredWindowLaw`](../PerronWright/Probability/CountableStarredTVWindowLaw.lean#L30) |
| Normalized starred actual empirical-marked closed-window law | [`PerronWright.CountableStarredTVWindowLaw.normalizedStarredMarkedWindowLaw`](../PerronWright/Probability/CountableStarredTVWindowLaw.lean#L36) |
| Raw starred unmarked closed-window law | [`PerronWright.CountableStarredTVWindowLaw.unnormalizedStarredWindowLaw`](../PerronWright/Probability/CountableStarredTVWindowLaw.lean#L43) |
| Raw starred actual empirical-marked closed-window law | [`PerronWright.CountableStarredTVWindowLaw.unnormalizedStarredMarkedWindowLaw`](../PerronWright/Probability/CountableStarredTVWindowLaw.lean#L48) |
| Actual global Brownian law using full excursions and full-area Poisson surplus marks | [`PerronWright.BrownianExcursionPointProcessLaw.law`](../PerronWright/Probability/BrownianExcursionPointProcessLaw.lean#L45) |
| Law of the actual global Brownian process restricted to any positive closed window | [`PerronWright.BrownianArbitraryWindowLaw.law`](../PerronWright/Probability/BrownianArbitraryWindowLaw.lean#L183) |

## 6. Actual empirical TV marks and quantitative controls

A component's mark is the actual empirical probability distribution of natural-number types among its vertices, not an artificially assigned Perron mark. Only in the limit is the original Perron probability added as a constant mark to every Brownian component atom.

| Meaning | Fully qualified Lean declaration and location |
| --- | --- |
| Actual empirical type measure of any vertex block | [`PerronWright.EmpiricalTypeMarks.empiricalMeasure`](../PerronWright/Probability/EmpiricalTypeMarks.lean#L31) |
| Empirical type probability measure of an actual component | [`PerronWright.EmpiricalTypeMarks.componentMark`](../PerronWright/Probability/EmpiricalTypeMarks.lean#L75) |
| Mark space whose elements are actual probability measures on `ℕ` | [`PerronWright.CountableVariationMarks.VariationMark`](../PerronWright/Probability/CountableVariationMarks.lean#L52) |
| Distance equals the full sum of atomic absolute variations | [`PerronWright.CountableVariationMarks.dist_eq_atomic_variation`](../PerronWright/Probability/CountableVariationMarks.lean#L72) |
| Completeness | [`PerronWright.CountableVariationMarks.variationMarkComplete`](../PerronWright/Probability/CountableVariationTopology.lean#L56) |
| Polish mark space | [`PerronWright.CountableVariationMarks.variationMarkPolish`](../PerronWright/Probability/CountableVariationTopology.lean#L84) |
| TV mark corresponding to the original Perron probability `u·μ` | [`PerronWright.CountablePerronMarkConvergence.perronMark`](../PerronWright/Probability/CountablePerronMarkConvergence.lean#L19) |
| Product of a closed window with the TV mark space | [`PerronWright.CountableComponentWindowLaw.MarkedWindow`](../PerronWright/Probability/CountableComponentWindowLaw.lean#L26) |
| Actual empirical-marked window point measure in unstarred size coordinates | [`PerronWright.CountableComponentWindowLaw.markedWindowPointMeasure`](../PerronWright/Probability/CountableComponentWindowLaw.lean#L28) |
| Empirical-marked window law obtained by pushing forward the normalized actual graph law | [`PerronWright.CountableKernel.empiricalMarkedWindowLaw`](../PerronWright/Probability/CountableComponentWindowLaw.lean#L98) |
| Empirical-marked window law obtained by pushing forward the raw actual graph law | [`PerronWright.CountableKernel.empiricalUnnormalizedMarkedWindowLaw`](../PerronWright/Probability/CountableComponentWindowLaw.lean#L144) |
| Component atom after starred size rescaling, with its original empirical mark retained | [`PerronWright.CountableTVWindowSizeRescaling.scaledMarkedWindowAtom`](../PerronWright/Probability/CountableTVWindowSizeRescaling.lean#L26) |
| Starred actual empirical-marked window point measure | [`PerronWright.CountableTVWindowSizeRescaling.scaledMarkedWindowPointMeasure`](../PerronWright/Probability/CountableTVWindowSizeRescaling.lean#L35) |
| Pushforward adding the constant Perron mark to an unmarked window law | [`PerronWright.CountableTVWindowConvergence.canonicalMarkedWindowLaw`](../PerronWright/Probability/CountableTVWindowConvergence.lean#L26) |
| Sum of component mark distances within a window | [`PerronWright.CountableTVWindowProfile.windowDistance`](../PerronWright/Probability/CountableTVWindowProfile.lean#L27) |
| Bad-mark set where mark distance reaches threshold `δ` | [`PerronWright.CountableTVWindowProfile.badMarkCell`](../PerronWright/Probability/CountableTVWindowProfile.lean#L102) |
| Actual graph expectation of the sum of window mark distances | [`PerronWright.CountableKernel.growingWindowDistanceExpectation`](../PerronWright/Probability/CountableTVWindowExpectation.lean#L94) |
| Actual probability that the window contains at least one bad-mark atom | [`PerronWright.CountableKernel.growingWindowBadProbability`](../PerronWright/Probability/CountableTVWindowTerminal.lean#L22) |

These distance expectations and bad-mark probabilities are controlled in the original, unstarred size windows. The starred laws themselves are transferred to corresponding closed windows by positive size rescaling. The public theorem gives both formulations; these quantitative controls must not be rewritten as new external convergence assumptions.
