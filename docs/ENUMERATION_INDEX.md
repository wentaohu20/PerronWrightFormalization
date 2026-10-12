# Theorem 3.6: Perron–Wright enumeration and definition index

This page locates the finite irreducible and regular critical compact formulations of the Perron–Wright enumeration theorem, Theorem 3.6 of the paper. Each link points to the source line of a definition or theorem declaration; the complete theorem type and proof are given in the linked Lean source. The other documents in this directory cover probability processes, Brownian densities, and countable models.

## Theorem 3.6 entry points

The two Lean declarations below implement the finite and compact cases of the same paper theorem; they are not two additional main theorems.

| Case | Fully qualified Lean name and location | Scope of the conclusion |
| --- | --- | --- |
| Finite irreducible | [PerronWright.FiniteIrreduciblePerronWrightTerminal.finite_perronWright](../PerronWright/Analysis/FiniteIrreduciblePerronWrightTerminal.lean#L120) | Analyticity of the radius of the actual tree series, its normalization at `t=1`, and a local quadratic logarithmic expansion with a cubic remainder; uniform shrinking-window radius and critical Gaussian formulas over every finite surplus range. |
| Regular critical compact | [PerronWright.CompactPerronWrightTheorem.compactPerronWright_theorem](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L232) | For each surplus cutoff `R`, an analytic radius, identification with the radius of the actual series, a local logarithmic expansion, and both uniform enumeration formulas. |
| Expanded compact conclusion | [PerronWright.CompactPerronWrightTheorem.CompactPerronWrightConclusions](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L193) | Exact types and quantifier order of the individual fields in the compact theorem's conclusion. |

The finite case assumes irreducibility, not strict positivity or primitivity of the kernel; bipartite kernels are therefore not excluded. The compact enumeration case assumes `B1`–`B2`, but not the probability branch's `QP` hypothesis.

## 1. Models and criticality assumptions

| Mathematical object | Fully qualified Lean name and definition location | Meaning |
| --- | --- | --- |
| Continuous kernel | [PerronWright.ContinuousKernel](../PerronWright/Kernel/Basic.lean#L27) | A continuous, symmetric, everywhere nonnegative real kernel `κ(x,y)`. |
| Finite model | [PerronWright.FiniteIrreducibleModel](../PerronWright/Model/FiniteIrreducibleModel.lean#L22) | A finite type set, strictly positive type weights summing to one, and a symmetric nonnegative irreducible kernel matrix; nonnegativity is obtained from the irreducible matrix data. |
| Finite type measure | [PerronWright.FiniteIrreducibleModel.measure](../PerronWright/Model/FiniteIrreducibleModel.lean#L56) | `μ = Σ_a weight(a) δ_a`. |
| Finite mean matrix | [PerronWright.FiniteIrreducibleModel.meanMatrix](../PerronWright/Model/FiniteIrreducibleModel.lean#L44) | `κ diag(weight)`, with `(a,b)` entry `κ(a,b) weight(b)`. |
| Finite criticality | [PerronWright.FiniteIrreducibleModel.IsCritical](../PerronWright/Model/FiniteIrreducibleModel.lean#L51) | The spectral radius of this actual mean matrix equals one. |
| Compact model | [PerronWright.CompactBJRModel](../PerronWright/Model/CompactBJR.lean#L29) | A compact metric type space, a full-support Borel probability measure `μ`, and a continuous kernel `κ`. |
| Operator witness for B1 | [PerronWright.CompactBJRModel.B1Witness](../PerronWright/Model/CompactBJR.lean#L85) | An `L²(μ)` operator associated with the given kernel that is compact, self-adjoint, and has norm one; the witness is not an arbitrary unrelated operator. |
| B1 | [PerronWright.CompactBJRModel.B1](../PerronWright/Model/CompactBJR.lean#L93) | Existence of the preceding operator witness. |
| B2 | [PerronWright.CompactBJRModel.B2](../PerronWright/Model/CompactBJR.lean#L174) | The actual iterated kernel of some positive power is everywhere strictly positive. |
| Regular criticality | [PerronWright.CompactBJRModel.IsRegularCritical](../PerronWright/Model/CompactBJR.lean#L191) | B1 and B2 together. |
| Finite-model data adapter | [PerronWright.FiniteIrreducibleModel.bjrModel](../PerronWright/Model/FiniteIrreducibleBJRBridge.lean#L62) | Represents a finite model as discrete continuous BJR data for the common graph-weight definitions; it does not add B2 or regular criticality. |

The metric, discrete-topology, and Borel type classes in the finite theorem support this discrete continuous representation. The finite spectral criticality assumption remains `IsCritical`.

## 2. Kernel operators and the degree function

| Mathematical object | Fully qualified Lean name and definition location | Meaning |
| --- | --- | --- |
| `L²(μ)` space | [PerronWright.CompactBJRModel.L2](../PerronWright/Model/CompactBJR.lean#L52) | The Hilbert-space realization of the kernel. |
| Pointwise integral action | [PerronWright.CompactBJRModel.integralAction](../PerronWright/Model/CompactBJR.lean#L60) | `Kf(x)=∫ κ(x,y)f(y) μ(dy)`. |
| Correspondence between the kernel and its `L²` operator | [PerronWright.CompactBJRModel.IsAssociatedL2Operator](../PerronWright/Model/CompactBJR.lean#L71) | The weak pairing on continuous test functions agrees with the kernel integral pairing. |
| Bounded operator on continuous functions | [PerronWright.ContinuousKernel.actionCLM](../PerronWright/Kernel/Integral.lean#L165) | The same integral action as a continuous linear map on `C(S,ℝ)`. |
| Finite action | [PerronWright.FiniteIrreducibleModel.action](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L20) | `Kf(a)=Σ_b κ(a,b) weight(b) f(b)`. |
| Iterated kernel | [PerronWright.CompactBJRModel.iteratedKernel](../PerronWright/Model/CompactBJR.lean#L102) | Index `n` denotes the kernel of `K^(n+1)`, not `K^n`; `n=0` is the original kernel. |
| Continuous iterated-kernel map | [PerronWright.CompactBJRModel.iteratedKernelMap](../PerronWright/Model/CompactBJR.lean#L118) | The continuous iterated integral kernel used in B2. |
| Degree function | [PerronWright.ContinuousKernel.degree](../PerronWright/Kernel/Basic.lean#L85) | `d(x)=∫ κ(x,y) μ(dy)`. |
| Continuous degree-function map | [PerronWright.CompactBJRModel.degreeFunction](../PerronWright/Model/PerronQuantities.lean#L128) | The degree function as an element of `C(S,ℝ)`. |

## 3. Perron normalization and scales

Let `u` denote the strictly positive Perron function. Its normalization is type average one, not `L²` norm one:

\[
Ku=u,\qquad \int u\,d\mu=1,\qquad
\alpha=\int u^2\,d\mu,\qquad \beta=\int u^3\,d\mu.
\]

In the finite model, the integrals are finite sums weighted by `weight`. The scales `α` and `β` are defined from the Perron function obtained from the model assumptions; they are not additional model parameters.

| Mathematical object | Fully qualified Lean name and location |
| --- | --- |
| Finite type average | [PerronWright.FiniteIrreducibleModel.average](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L90) |
| Finite Perron function | [PerronWright.FiniteIrreducibleModel.perronFunction](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L124) |
| Finite fixed-point and normalization proofs | [PerronWright.FiniteIrreducibleModel.perronFunction_fixed](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L131); [PerronWright.FiniteIrreducibleModel.perronFunction_average](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L135) |
| Finite `α` and `β` | [PerronWright.FiniteIrreducibleModel.alpha](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L139); [PerronWright.FiniteIrreducibleModel.beta](../PerronWright/Model/FiniteIrreduciblePerronQuantities.lean#L142) |
| Compact Perron function | [PerronWright.CompactBJRModel.perronFunction](../PerronWright/Model/PerronQuantities.lean#L22) |
| Compact fixed-point and normalization proofs | [PerronWright.CompactBJRModel.perronFunction_fixed](../PerronWright/Model/PerronQuantities.lean#L29); [PerronWright.CompactBJRModel.perronFunction_integral](../PerronWright/Model/PerronQuantities.lean#L33) |
| Compact `α` and `β` | [PerronWright.CompactBJRModel.alpha](../PerronWright/Model/PerronQuantities.lean#L92); [PerronWright.CompactBJRModel.beta](../PerronWright/Model/PerronQuantities.lean#L96) |
| Perron probability `u(x)μ(dx)` | [PerronWright.CompactBJRModel.perronLaw](../PerronWright/Model/PerronQuantities.lean#L57) |

## 4. Weighted graph counts and the scalar field

Here `k` is the vertex count and `r` is the surplus: a connected graph has `k+r−1` edges. The cases `r=0` and `r=1` are trees and unicyclic graphs. The positive-excess case uses `ell=r−1`, so `ell>0` corresponds to `r≥2`.

For a labelled simple graph `H`, the actual annealed weight is

\[
W_t(H)=\int_{S^k}
\left(\prod_{i=1}^k e^{-t d(x_i)}\right)
\left(\prod_{\{i,j\}\in E(H)}t\kappa(x_i,x_j)\right)
\,d\mu^{\otimes k}(x),
\qquad
C_t(k,r)=\sum_{\substack{H\text{ connected}\cr |E(H)|=k+r-1}}W_t(H).
\]

This definition directly sums and integrates over finite simple graphs; it does not replace their weights with an asymptotic main term. The finite model uses `M.bjrModel.connectedWeight`, sharing the definition with the compact case.

| Mathematical object | Fully qualified Lean name and definition location |
| --- | --- |
| Unordered edge factor | [PerronWright.CompactBJRModel.edgeFactor](../PerronWright/Enumeration/ConnectedWeight.lean#L27) |
| Graph-weight integrand | [PerronWright.CompactBJRModel.graphWeightIntegrand](../PerronWright/Enumeration/ConnectedWeight.lean#L39) |
| Product-measure integral over the type vector | [PerronWright.CompactBJRModel.graphWeight](../PerronWright/Enumeration/ConnectedWeight.lean#L46) |
| Connected weight at fixed vertex count and surplus | [PerronWright.CompactBJRModel.connectedWeight](../PerronWright/Enumeration/ConnectedWeight.lean#L53) |
| Real scalar field `g_t(x)=log t−(t−1)d(x)` | [PerronWright.CompactBJRModel.scalarField](../PerronWright/Enumeration/FieldWeight.lean#L81) |
| Field-weighted graph integrand | [PerronWright.CompactBJRModel.fieldGraphWeightIntegrand](../PerronWright/Enumeration/FieldWeight.lean#L87) |
| Field-weighted graph integral and connected sum | [PerronWright.CompactBJRModel.fieldGraphWeight](../PerronWright/Enumeration/FieldWeight.lean#L92); [PerronWright.CompactBJRModel.fieldConnectedWeight](../PerronWright/Enumeration/FieldWeight.lean#L97) |
| Complex field-weighted graph integrand | [PerronWright.CompactBJRModel.complexFieldGraphIntegrand](../PerronWright/Enumeration/FieldAnalytic.lean#L82) |
| Compact complex scalar field | [PerronWright.ScalarFieldResponse.scalarFieldComplex](../PerronWright/Analysis/ScalarFieldResponse.lean#L14) |
| Finite complex scalar-field adapter | [PerronWright.FiniteIrreducibleScalarFieldResponse.scalarField](../PerronWright/Analysis/FiniteIrreducibleScalarFieldResponse.lean#L22) |

The real-field version replaces the vertex factor by `exp(g(x_i)−d(x_i))` and the edge factor by `κ(x_i,x_j)`. For `t>0`, the source's [scalar-field identity](../PerronWright/Enumeration/FieldWeight.lean#L194) is `C_t(k,r)=t^(r−1) C_{g_t}(k,r)`, including the tree case's factor `t⁻¹`.

## 5. Tree series, analytic critical pairs, and the actual radius

The tree series is defined by actual finite labelled-tree integrals: fix the root type, integrate over the other vertex types, and sum over trees. The coefficient of degree `n+1` is divided by `n!`.

| Mathematical object | Fully qualified Lean name and definition location |
| --- | --- |
| Graph integral with fixed root type | [PerronWright.FieldRootedTree.fixedRootedGraphProfileMap](../PerronWright/Enumeration/FieldRootedTreeFinite.lean#L192) |
| Actual labelled-tree sum | [PerronWright.FieldRootedTree.numerator](../PerronWright/Enumeration/FieldRootedTreeFinite.lean#L216) |
| Factorially normalized coefficient | [PerronWright.FieldRootedTree.coefficient](../PerronWright/Enumeration/FieldRootedTreeFinite.lean#L222) |
| Actual field-weighted tree formal power series | [PerronWright.FieldRootedTree.series](../PerronWright/Enumeration/FieldRootedTreeFinite.lean#L256) |
| Multilinear representation of the compact tree series | [PerronWright.FieldRootedTree.fms](../PerronWright/Enumeration/ScalarFieldRootedTreeRadius.lean#L41) |
| Finite representation of the same actual graph series | [PerronWright.FiniteIrreducibleModel.fieldFMS](../PerronWright/Analysis/FiniteIrreducibleFieldSeriesNormalization.lean#L58) |
| Compact analytic critical pair `(ρ_g,τ_g)` | [PerronWright.CriticalPair.criticalPair](../PerronWright/Analysis/CriticalPair.lean#L341) |
| Finite analytic critical pair | [PerronWright.FiniteIrreducibleCriticalPair.criticalPair](../PerronWright/Analysis/FiniteIrreducibleCriticalPair.lean#L342) |
| Radius component of the compact critical pair | [PerronWright.RadiusResponse.radius](../PerronWright/Analysis/RadiusResponse.lean#L23) |
| Radius component of the finite critical pair | [PerronWright.FiniteIrreducibleRadiusResponse.radius](../PerronWright/Analysis/FiniteIrreducibleRadiusResponse.lean#L23) |
| Compact scalar slice `ρ(g_t)` | [PerronWright.ScalarRadiusSecond.scalarRadius](../PerronWright/Analysis/ScalarRadiusSecond.lean#L13) |
| Finite scalar slice | [PerronWright.FiniteIrreducibleScalarFieldResponse.scalarRadius](../PerronWright/Analysis/FiniteIrreducibleScalarFieldResponse.lean#L25) |
| Compact physical real radius `ρ(t)` | [PerronWright.CriticalWindowRadiusConversion.realScalarRadius](../PerronWright/Analysis/CriticalWindowRadiusConversion.lean#L23) |
| Finite physical real radius `ρ(t)` | [PerronWright.FiniteIrreducibleCriticalWindowRadiusConversion.realScalarRadius](../PerronWright/Analysis/FiniteIrreducibleCriticalWindowRadiusConversion.lean#L23) |
| Compact analytic logarithm | [PerronWright.ScalarLogRadiusTaylor.logScalarRadius](../PerronWright/Analysis/ScalarLogRadiusTaylor.lean#L57) |
| Finite analytic logarithm | [PerronWright.FiniteIrreducibleScalarLogRadiusTaylor.logScalarRadius](../PerronWright/Analysis/FiniteIrreducibleScalarLogRadiusTaylor.lean#L66) |
| Compact quadratic rate `α²/(2β)` | [PerronWright.CriticalWindowRadiusConversion.criticalQuadraticRate](../PerronWright/Analysis/CriticalWindowRadiusConversion.lean#L28) |
| Finite quadratic rate | [PerronWright.FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate](../PerronWright/Analysis/FiniteIrreducibleCriticalWindowRadiusConversion.lean#L28) |
| Public compact-theorem aliases for the complex radius, real radius, and logarithm | [PerronWright.CompactPerronWrightTheorem.ScalarRadius.criticalRadius](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L28); [PerronWright.CompactPerronWrightTheorem.ScalarRadius.physicalRadius](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L34); [PerronWright.CompactPerronWrightTheorem.ScalarRadius.logCriticalRadius](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L40) |
| Physical tree-radius aliases used in compact and finite main terms | [PerronWright.TreePerronWrightFormula.physicalTreeRadius](../PerronWright/Enumeration/TreePerronWrightFormula.lean#L50); [PerronWright.FiniteIrreducibleTreePerronWrightFormula.physicalTreeRadius](../PerronWright/Analysis/FiniteIrreducibleTreePerronWrightFormula.lean#L50) |

The critical pair is constructed analytically and satisfies both the tree equation and the eigenvalue-one constraint. See the equations in [compact `criticalPair_germ`](../PerronWright/Analysis/CriticalPair.lean#L242) and [finite `criticalPair_germ`](../PerronWright/Analysis/FiniteIrreducibleCriticalPair.lean#L246). It is not an additional assumed enumeration or radius interface.

The radius notation distinguishes the following objects:

- `ρ_g` is the analytic critical activity for a complex field. Its real scalar slice `ρ(t)=ρ_{g_t}` is positive near `t=1`, with `ρ(1)=1`.
- The source names `physicalRadius`, `realScalarRadius`, and `physicalTreeRadius` refer to this physical real branch `ρ(t)`. It equals the radius of convergence of the actual field-weighted tree series. See [finite radius identification](../PerronWright/Analysis/FiniteIrreduciblePhysicalScalarRadius.lean#L46) and [compact radius identification](../PerronWright/Enumeration/CompactPerronWrightTheorem.lean#L135).
- The main term's `ρ(t)^(−k)e^(−k)` can be written `(eρ(t))^(−k)`. Here `eρ(t)` is only the exponential scale of the combinatorial main term, not the preceding tree-series radius of convergence or a separate radius definition in the source. The factor `e^(−k)` comes from the factorial/Stirling conversion.

The local radius expansion in the theorem is

\[
\log\rho(t)=\frac{\alpha^2}{2\beta}(t-1)^2+O(|t-1|^3).
\]

## 6. Wright constants and the radius/Gaussian main terms

The common Wright constants are indexed by surplus `r`: `w_0=1` and `w_1=√(2π)/4=√(π/8)`. For `r≥2`, the definition uses a finite sum over connected cubic kernels of positive excess `ell=r−1`. These kernels allow loops and parallel edges, but `connectedWeight` always remains a simple-graph weight.

| Mathematical object | Fully qualified Lean name and definition location | Meaning |
| --- | --- | --- |
| Finite multigraph | [PerronWright.FiniteMultiGraph](../PerronWright/Enumeration/KernelBounds.lean#L14) | A finite multigraph with labelled edges and unordered endpoints. |
| Connected cubic kernel | [PerronWright.GraphCore.LabelledConnectedCubicKernel](../PerronWright/Enumeration/CubicKernelSubdivision.lean#L33) | `2ell` vertices and `3ell` edges, every vertex of degree three, and connected non-loop simple support. |
| Global representation multiplicity of a kernel | [PerronWright.GraphCore.labelledCubicKernelGlobalMultiplicity](../PerronWright/Enumeration/PositiveSurplusWrightConstant.lean#L221) | `(2ell)! (3ell)!` multiplied by the loop-orientation factor. |
| Inverse multiplicity | [PerronWright.GraphCore.labelledCubicKernelInverseMultiplicityReal](../PerronWright/Enumeration/PositiveSurplusCubicConstantPositivity.lean#L29) | The weight of each kernel in the finite cubic-kernel sum. |
| Cubic-kernel EGF constant | [PerronWright.GraphCore.positiveSurplusCubicEGFConstantReal](../PerronWright/Enumeration/PositiveSurplusCubicConstantPositivity.lean#L46) | The finite sum of inverse multiplicities multiplied by `2^(−3ell/2)`. |
| Positive-excess Wright constant | [PerronWright.GraphCore.positiveSurplusWrightConstantReal](../PerronWright/Enumeration/PositiveSurplusCubicConstantPositivity.lean#L110) | The EGF constant multiplied by `√(2π)/Γ(3ell/2)`. |
| Unicyclic constant | [PerronWright.UnicyclicPerronWrightFormula.unicyclicWrightConstant](../PerronWright/Enumeration/UnicyclicPerronWrightFormula.lean#L57) | `√(2π)/4`. |
| Common compact `w_r` | [PerronWright.PerronWrightFormulaMainTerm.wrightConstant](../PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L25) | Combines the tree, unicyclic, and positive-excess cases. |
| Common finite `w_r` | [PerronWright.FiniteIrreduciblePerronWrightFormulaMainTerm.wrightConstant](../PerronWright/Analysis/FiniteIrreduciblePerronWrightFormulaMainTerm.lean#L26) | The same constant family as in the compact case, not model-dependent constants. |
| Compact radius main term | [PerronWright.PerronWrightFormulaMainTerm.perronWrightRadiusMainTerm](../PerronWright/Enumeration/PerronWrightFormulaMainTerm.lean#L58) | `A_ρ` below. |
| Finite radius main term | [PerronWright.FiniteIrreduciblePerronWrightFormulaMainTerm.perronWrightRadiusMainTerm](../PerronWright/Analysis/FiniteIrreduciblePerronWrightFormulaMainTerm.lean#L64) | The same form, using the finite `β` and radius. |
| Compact Gaussian main term | [PerronWright.BoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm](../PerronWright/Enumeration/BoundedSurplusPerronWrightFormula.lean#L131) | `A_G` below. |
| Finite Gaussian main term | [PerronWright.FiniteIrreducibleBoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm](../PerronWright/Analysis/FiniteIrreducibleBoundedSurplusPerronWrightFormula.lean#L131) | The same form, using the finite `α` and `β`. |

For a positive integer `k`, the two main terms are

\[
A_\rho(k,r,t)=w_r\beta^{(r-1)/2}\rho(t)^{-k}e^{-k}k^{k+3r/2-2},
\]

\[
A_G(k,r,t)=w_r\beta^{(r-1)/2}e^{-k}k^{k+3r/2-2}
\exp\!\left(-\frac{\alpha^2}{2\beta}k(t-1)^2\right).
\]

The theorem compares the actual `C_t(k,r)` with these main terms. For each fixed `R` and nonnegative shrinking-window sequence `η(k)→0`, the radius formula has relative error `O(η(k)+k^(−1/2))`, uniformly over `r≤R` and `|t−1|≤η(k)`; its constant is chosen before `η`. For each fixed `L≥0`, the critical window `|t−1|≤L/√k` has Gaussian relative error `O(k^(−1/2))`, uniformly over `r≤R` and all `t` in that window.

`AnalyticAt` denotes local analyticity, `Tendsto` a limit, `=O` a big-O estimate, and `∀ᶠ k in atTop` all sufficiently large natural numbers `k`. These are general Mathlib notions. Their exact quantifiers are specified by the two theorem declarations and the compact conclusion structure linked at the top of this page. This index does not record build or execution-test status.
