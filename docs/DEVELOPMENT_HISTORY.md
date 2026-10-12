# Perron--Wright: complete Chapter 3 main results

This Lean 4 project proves all five main results stated in Chapter 3 of
*Perron--Wright asymptotics*, with the paper's actual model hypotheses.
The project is located at `E:\PerronWrightFormalization`.

| Paper result | Verified Lean entry points | Scope |
| --- | --- | --- |
| Perron--Wright formula (`thm:Perron-Wright`) | [Finite terminal](PerronWright/Analysis/FiniteIrreduciblePerronWrightTerminal.lean), [compact terminal](PerronWright/Enumeration/CompactPerronWrightTheorem.lean) | Genuine analytic physical radius, quadratic log-radius expansion, every bounded-surplus shrinking-window formula and its uniform Gaussian specialization. |
| Aldous factorial density and local determination (`prop:AW-density`) | [Actual factorial densities](PerronWright/Probability/BrownianActualFactorialDensity.lean), [arbitrary-window determination](PerronWright/Probability/BrownianActualArbitraryWindowDeterminacy.lean) | Literal all-order Brownian/Wright densities, arbitrary coupled Borel tests, and determination of the actual point law on every positive closed size/surplus window. |
| Local main theorem (`thm:local-main`) | [Finite fixed-size formula](PerronWright/Probability/FiniteIrreducibleLocalMainTerminal.lean), [compact fixed-size formula](PerronWright/Probability/CompactAnnealedFactorialUniform.lean), [actual Brownian process limits](PerronWright/Probability/ModelActualBrownianLimits.lean) | Uniform floor factorial asymptotics and full-sequence actual unmarked/empirical-marked global and window laws, including literal starred normalization, for both model branches. |
| Countable critical realization (`thm:countable-realization`) | [Joint countable terminal](PerronWright/Probability/CountableActualBrownianLimits.lean) | One exhaustive monotone support and positive integer realization, empirical variation and minimum-population conditions, simultaneous local formulas, actual global Brownian unmarked limits and all localized TV-marked window limits. |
| Countable limits without spectral renormalization (`thm:countable-unrenormalized`) | [The same joint countable terminal](PerronWright/Probability/CountableActualBrownianLimits.lean) | The same typed integer realization, actual empirical spectral drift, raw floor factorial formulas and unmarked/TV-marked Brownian limits at the parameter `lambda + theta`; the stronger zero-drift case is its `theta = 0` specialization. |

The principal theorem names are:

- `PerronWright.FiniteIrreduciblePerronWrightTerminal.finite_perronWright`;
- `PerronWright.CompactPerronWrightTheorem.compactPerronWright_theorem`;
- `PerronWright.BrownianActualFactorialDensity.actual_window_factorial_density`;
- `PerronWright.BrownianActualArbitraryWindowDeterminacy.actual_windowLaw_eq_of_density_factorial_lintegrals`;
- `PerronWright.ModelActualBrownianLimits.finite_starredProcessLaw_tendsto_actual_Brownian`
  and `finite_starredMarkedProcessLaw_tendsto_actual_Brownian`, together with
  their `compact_` counterparts;
- `PerronWright.CountableActualBrownianLimits.exists_actual_growing_Brownian_global_and_TV_window_limits`.

The fixed-size local theorem names are
`FiniteIrreducibleLocalMainTerminal.eventually_uniform_paper_floor_factorial_density`
and `CompactAnnealedFactorialUniform.factorial_uniform_bounded_surplus`,
both under the `PerronWright` namespace.

## Exact hypothesis and topology scope

Finite kernels require irreducibility, not primitivity or strict
positivity; bipartite kernels and arbitrary bounded O(1) deterministic
type-count errors remain allowed. Compact enumeration requires B1--B2,
but not QP. Only the compact probability branch uses the paper's QP
hypothesis.

The actual Brownian law is built from the full excursion path and
full-area Poisson surplus source. Its Palm deletion, Wright area moments,
all-order factorial densities, cell moments and determination series are
proved, not supplied as interfaces. Final model process theorems have no
local-limit or Brownian-identification premise: those intermediate facts
are discharged from the model hypotheses.

For countable kernels, the positive lower bound displayed in the terminal
is a witness already contained in regular criticality. A single
`exists level` precedes all local/process conclusions and all parameters.
Countable empirical marks use the original Perron probability and the
actual total-variation metric. Their convergence is the paper's localized
TV-marked convergence, expressed on every boundary-null positive closed
window; no locally compact global TV-product space is presumed.

The starred size multiplier is the original `beta^(1/3)`. The actual
Aldous parameter is `alpha * beta^(-2/3) * lambda`, and in the raw
spectral-drift branch it is
`alpha * beta^(-2/3) * (lambda + theta)`, not an outside additive shift.

## Verification

The final umbrella `PerronWright.lean` builds successfully in **5,356**
jobs. The three independent full audits check **6,646**, **5,621** and
**4,613** distinct declarations, respectively; **17**, **16** and **15**
are axiom-free. Every other audited declaration depends only on Lean's
standard `propext`, `Classical.choice` and `Quot.sound`. Diagnostics,
duplicate audit targets and nonstandard axiom dependencies are absent.
The project source has no `sorry`, `admit`, new mathematical axiom,
opaque proof constant, or kernel-check bypass.

Reproduce the build and audits from the project directory:

```powershell
.\Build.ps1 PerronWright
lake env lean Audit.lean
lake env lean ProbabilityAudit.lean
lake env lean Chapter3FiniteProcessSpatialBridgeAudit.lean
```

The following milestone record is historical. Its older pending
obligations have been discharged by the completed terminal results above.

## Trust policy

The checked development contains:

- no `sorry` or `admit`;
- no project-defined axioms;
- no unproved mathematical interface assumptions standing in for
  Perron--Frobenius--Jentzsch, analytic spectral perturbation,
  Hilbert--Schmidt/Schatten theory, regularized determinants,
  singularity transfer, core--kernel enumeration, or Wright asymptotics.

The same policy applies to the probability extension: no assumed profile
concentration, residual-factor asymptotic, moment determinacy, Brownian
excursion density identity, or process-convergence interface. In the compact
probability theorem, `(QP)` is an allowed model assumption because it is an
explicit hypothesis of the paper, not a substitute for a pending proof.

Intermediate modules are kept compiling at every milestone.  The proof is
built from leaf infrastructure upward rather than by declaring the final
theorem with placeholders.

## Initial module order

1. continuous kernels and their `C(S)` / `L²(μ)` realizations;
2. compact positive-operator and Perron--Jentzsch theory;
3. analytic simple-eigenpair perturbation, proved by the Banach implicit
   function theorem;
4. analytic implicit/fold theory and the rooted-tree branch;
5. the continuous-kernel cycle primitive needed for the unicyclic EGF;
6. exact labelled core--kernel enumeration;
7. uniform Banach-valued `Δ`-transfer and Wright asymptotics;
8. uniform field response and the final Perron--Wright theorem.

The proof follows the paper at the level of mathematical content, but it does
not build a general Riesz--Kato or regularized-determinant library first.  The
only consequences used by Theorem 3.6 are proved directly: normalized analytic
left/right eigenpairs replace general Riesz projections, and a normalized
cycle primitive replaces `det₂`.  This removes two large general-purpose
detours without introducing any unproved interface.

## Verified chronological milestones

The following record is chronological. Later checkpoints supersede the
pending obligations stated at earlier checkpoints; the status table above
tracks the current literal Chapter 3 endpoints.

- `PerronWright.Kernel.Basic`: continuous symmetric nonnegative kernels,
  measurable and integrable sections, and the degree function;
- `PerronWright.Kernel.Integral`: the `C(S, ℝ)`-valued Bochner construction
  of the integral operator, its pointwise formula, linearity, and norm bound;
- `PerronWright.Model.CompactBJR`: the compact BJR data and exactly the two
  paper hypotheses `(B1)`--`(B2)`, with no Perron conclusions included.
- `PerronWright.Kernel.Compact` and `.Complex`: compactness of the real and
  complex continuous-kernel actions by Arzelà--Ascoli.
- `PerronWright.Kernel.Composition`: continuous kernel composition, Fubini
  compatibility with action composition, and strong positivity of a strictly
  positive kernel under a full-support measure.
- `PerronWright.Kernel.SpectrumBridge` and `.Smoothing`: the exact relation
  between the `C(S)` and `L²(μ)` realizations, and a continuous representative
  of every nonzero-eigenvalue `L²` eigenvector.
- `PerronWright.Analysis.CompactSymmetric` and `.Positive`: from the original
  `(B1)`--`(B2)` assumptions, existence and uniqueness of the normalized
  strictly positive Perron fixed point and geometric simplicity of its
  continuous fixed space.
- `PerronWright.Model.PerronQuantities`: the resulting canonical Perron
  function, its uniform positive lower bound, the tilted Perron probability
  law, and positive quadratic/cubic scales `α` and `β`.
- `PerronWright.Analysis.PerronSpectrum`: algebraic multiplicity one of the
  `L²` eigenvalue `1`, exclusion of `-1`, and peripheral spectral uniqueness
  of `1` for the complexified continuous-kernel operator.
- `PerronWright.CyclePrimitive`: direct iterated-kernel cycle traces, a
  norm-controlled unicyclic series, and uniform convergence on strictly
  subcritical closed discs without invoking a regularized determinant.
- `PerronWright.CycleAnalytic`: a direct complex power series for the
  unicyclic contribution, equality with its cycle trace sum, and analyticity
  on strictly subcritical discs.
- `PerronWright.SimpleCyclePrimitive`: removes the length-two operator-trace
  term from that series.  The remaining series starts with genuine triangles,
  and is proved exactly equal to the old trace series minus
  `w^2 Tr(L^2)/4`, matching the correction required for simple graphs.
- `PerronWright.Analysis.SpectralGap`: a quantitative gap for the complex
  continuous-kernel spectrum away from the simple Perron eigenvalue.
- `PerronWright.Analysis.PerronFunctional` and `.AugmentedInverse`: the
  normalized complex left Perron functional, the compact rank-one Perron
  projection, invertibility of `I-K+P`, and a bounded inverse on `ker ell`.
- `PerronWright.Analysis.TreeImplicit`, `.TreeCritical`, and
  `.FoldCoefficients`: the actual analytic tree residual, local uniqueness at
  the zero solution, its first and second derivatives at the critical point,
  and the nonzero fold coefficients with the exact `sqrt(2/beta)` balance.
- `PerronWright.Analysis.AnalyticEigenpair`: an analytic, normalized simple
  eigenvalue/eigenvector germ for the actual family `K M_tau`, obtained via
  an invertible derivative, not assumed as a perturbation interface.
- `PerronWright.Analysis.CriticalPair`: derivative of the Perron eigenvalue,
  an invertible augmented critical linearization, and an analytic local
  critical pair `(rho_g, tau_g)` satisfying both the tree and eigenvalue-one
  equations, with local uniqueness, conjugation symmetry, and uniform real
  positivity of the critical pair for sufficiently small real fields.
- `PerronWright.Analysis.RadiusResponse`: the exact first field derivative
  `D rho(0)[h] = -alpha * ell(h) = -integral u*h`, proved from the actual
  analytic critical pair's tree equation.
- `PerronWright.Enumeration.ConnectedWeight`, `.FieldWeight`, and `.TreeCase`:
  the literal annealed finite-graph partition functions, continuity and
  positivity of their weights, the exact scalar-field identity
  `C_t(k,r) = t^(r-1) C_{g_t}(k,r)` (including `r=0`), and the zero-surplus
  characterization by trees.
- `PerronWright.Enumeration.FieldAnalytic`: the finite graph and connected
  weights extend to entire functions of the complex field, and all three
  levels of their complexification recover the original real-field weights.
- `PerronWright.Enumeration.TreeDissymmetry`: the exact weighted identity
  between unrooted, vertex-rooted, and edge-rooted labelled trees at every
  positive finite size, for the model's actual annealed field weight.
- `PerronWright.Enumeration.TreeEGF`: formal exponential generating functions
  defined directly from those finite annealed graph sums, with verified
  unrooted = vertex-rooted - edge-rooted and vertex-rooted = X·d/dX(unrooted).
- `PerronWright.Enumeration.TreeCoefficientLowOrder`: direct computations of
  the actual one- and two-vertex rooted-tree weights, including the exact
  kernel-action form at size two.  The later `RootedTreeFormalIdentity`
  module proves the corresponding all-size recursion.
- `PerronWright.Enumeration.TreeCoefficientProfile`: defines the actual
  type-resolved rooted-tree profile at every finite size and proves that its
  integral is exactly the corresponding vertex-rooted EGF coefficient.  The
  later rooted-tree formal and analytic modules prove both the recursive
  exponential equation and the exact zero-field critical radius.
- `PerronWright.Enumeration.TreeCoefficientContinuous`: each type-resolved
  finite rooted-tree coefficient is continuous in the root type and hence
  is represented by an element of `C(S, ℝ)`; these coefficients are assembled
  and identified recursively in the later `RootedTree*` modules.
- `PerronWright.Enumeration.KernelBounds` and `.KernelShapes`: an endpoint
  model for multigraph kernels that retains loops and parallel edges, the
  `v <= 2 ell`, `e <= 3 ell` bounds, the cubic equality criterion, and
  finiteness of the fixed-excess labelled endpoint shapes.
- `PerronWright.Enumeration.GraphCore`: exact leaf-pruning preservation of
  connectivity and surplus, together with a canonical maximal induced
  minimum-degree-two core and exclusion of leaves from that core.
- `PerronWright.Enumeration.CoreInvariant`: invariance of that canonical core
  under pruning a leaf, and nonemptiness of the core for a connected graph
  with positive surplus.
- `PerronWright.Enumeration.PruneTermination`: literal degree-one leaf-pruning
  relation on finite surviving vertex sets, with strict cardinal descent and
  well-foundedness.
- `PerronWright.Enumeration.LeafFactor`: exact removal of the sole edge at a
  leaf and the corresponding vertex-by-edge factorization of the model's
  actual graph-weight integrand.
- `PerronWright.Enumeration.LeafIntegration`: exact relabeling of the
  surviving vertices and edges to the induced graph, and a Fubini identity
  for the actual annealed graph weight after one leaf is integrated.
- `PerronWright.Enumeration.LeafTransfer`: a closed one-leaf integration
  identity using the actual response
  `∫ exp(-t·d(y)) t·κ(y,a) dμ(y)` at the surviving neighbor.
- `PerronWright.Enumeration.LeafIterate`: identifies the residual product
  with the smaller induced graph's actual integrand, so a single leaf-removal
  step is an exact marked weight on that smaller graph.
- `PerronWright.Enumeration.RootedForestTransfer`: an exact finite induction
  for successive leaf deletions with continuous vertex marks. Each deleted
  leaf's mark is integrated into its surviving neighbor; the terminal graph
  remains an induced graph on explicitly tracked original labels. An
  automatically terminating pruning sequence and its exact annealed-weight
  identity are proved; the terminal graph has no degree-one vertices.
- `PerronWright.Enumeration.CoreTerminal`: for every connected finite graph
  with positive surplus, the automatically pruned terminal graph's original
  label image is **exactly** the canonical greatest 2-core, and its edge
  relation is the original graph induced on those labels. This closes the
  leaf-pruning-to-2-core bridge; the full weighted core--kernel sum remains
  open.
- `PerronWright.Enumeration.CoreBranching`: proves the exact degree-excess
  identity on the 2-core, bounds its branch vertices by twice the fixed
  excess, and characterizes the cubic equality case. It also partitions the
  actual connected weighted graph sum into finite fibres indexed by labelled
  admissible 2-cores; attached trees are already absorbed into continuous
  vertex marks. Suppression of degree-two paths into multigraph kernel edges
  remains open.
- `PerronWright.Enumeration.DegreeTwoPaths` and `.DegreeTwoWeight`: the
  degree-two part of a positive-surplus 2-core is a forest of paths, each
  component has exactly two boundary incidences, and integrating one
  degree-two vertex in the actual graph weight produces the exact continuous
  two-endpoint path-convolution kernel, also with surviving marks. The full
  path suppression and weighted multigraph-kernel sum remain open.
- `PerronWright.Enumeration.KernelEdges`: canonically labels each path
  component by its two actual boundary stubs and forms an edge-labelled
  multigraph from those paths and direct branch-to-branch edges. Endpoints
  lie in the branch set; repeated endpoints and parallel edge labels are
  retained. The arbitrary-length path weight remains open.
- `PerronWright.Enumeration.KernelEdgeCount`: the number of degree-two path
  components is exactly the number of degree-two vertices minus their
  internal edges. Combined with boundary-stub accounting, this is a proven
  intermediate step toward the kernel edge count.
- `PerronWright.Enumeration.KernelTotalEdges`: the actual edge-labelled
  suppressed kernel of a connected positive-surplus core has exactly
  `|B| + ell` edges, hence at most `3 ell`; equality holds exactly when
  every branch vertex is cubic. These statements follow from proved
  incidence double counts, not an assumed kernel decomposition.
- `PerronWright.Enumeration.KernelValence`: at every branch vertex,
  suppression preserves the original core degree pointwise, counting a
  loop twice. Thus a cubic core yields a genuinely cubic endpoint table.
- `PerronWright.Enumeration.KernelEndpointValence`: the same degree identity
  is expressed in literal endpoint-multiset counts for every suppressed
  path edge and direct branch edge, preserving loops with multiplicity two;
  the sum over the actual disjoint edge-label type is also proved equal to
  this pointwise valence.
- `PerronWright.Enumeration.CubicKernelValence`: after the actual cubic
  suppressed kernel is relabelled into the finite `Sym2` endpoint-table
  space, every relabelled vertex has literal endpoint multiplicity three;
  loops contribute two through their endpoint multiset.  The same table is
  also packaged as the project's literal `FiniteMultiGraph`, where its
  built-in degree is proved equal to three at every vertex.
- `PerronWright.Enumeration.CoreWeightFactor`: the actual finite-core
  vertex and original-edge weight integrand factors pointwise into a
  branch/direct-edge block and one exact block per degree-two component.
  The simultaneous product-measure integral factorization is still open.
- `PerronWright.Enumeration.CoreBlockIntegral`: proves the simultaneous
  product-measure/Fubini identity for an arbitrary finite dependent family
  of component blocks. Its identification with the actual core variables
  is supplied by the next module.
- `PerronWright.Enumeration.CoreCoordinates`: explicitly identifies the
  vertices of a real 2-core with branch coordinates plus the vertices of
  every degree-two component, proves that this reindexing preserves the
  product type law, and conditionally integrates all path blocks at once.
  The actual integrand connection is supplied by the next module.
- `PerronWright.Enumeration.CoreComponentLocality`: proves that the literal
  compact-BJR branch and degree-two component factors depend only on their
  own canonical coordinates, and rewrites the genuine graph weight as an
  outer branch-type integral times the product of all independent component
  integrals. Identifying each component integral with its path kernel remains
  open.
- `PerronWright.Enumeration.FiniteKernelShape`: every actual cubic
  suppressed kernel can be relabelled as an edge-labelled endpoint table
  in the finite candidate space `Fin(3 ell) → Sym2(Fin(2 ell))`, retaining
  loops and parallel labels. This is not yet a bijective classification of
  cubic multigraphs or a weighted kernel sum.
- `PerronWright.Enumeration.FiniteKernelGeneral`: every actual connected
  positive-surplus core, including noncubic cases, admits exact separate
  relabellings of its branch vertices and suppressed edge labels into a
  finite bounded endpoint-table space. Each transported endpoint pair is
  proved equal to the original one. Valence characterization and the
  weighted sum over these tables remain open.
- `PerronWright.Enumeration.PathKernel`: continuous kernels for paths of
  arbitrary internal length, with exact zero/one cases and a proved
  integral-composition recurrence.
- `PerronWright.Enumeration.PathKernelActualGraph`: the path-kernel
  recurrence factors through the literal one- and two-vertex path graph
  integrands, including an exact two-vertex double-integral identity for
  every remaining path length.
- `PerronWright.Enumeration.PathKernelFullWeight`: for every internal
  length, the entire literal path-graph weight, integrated over all its
  internal vertex types and multiplied by both external endpoint edges,
  equals the path kernel. This is an exact Fubini induction. Regrouping the
  assembled branch integral into the weighted finite kernel-graph sum remains
  open.
- `PerronWright.Enumeration.PathKernelSymmetry`: reversing an actual
  finite path preserves its graph integrand and product law, proving
  that every path kernel is symmetric in its endpoints. Consequently
  it defines a genuine factor on unordered `Sym2` kernel edges,
  including loops and parallel edge labels.
- `PerronWright.Enumeration.PathGraphAutomorphismRigidity`: proves that
  the endpoints are exactly the degree-less-than-two vertices of a finite
  standard path and that every path-graph automorphism is either the identity
  or `Fin.revPerm`.  Thus reversal is proved to be the only ambiguity in an
  intrinsic ordering of a suppressed degree-two path; no automorphism-count
  interface is assumed.
- `PerronWright.Enumeration.PathComponentOrder`: every actual connected
  component of the induced degree-two forest is a finite tree of maximum
  degree two, admits a Hamilton path, and is graph-isomorphic to the standard
  path graph on exactly its number of vertices.  This supplies the missing
  coordinate ordering before identifying its component integral with the
  path kernel.
- `PerronWright.Enumeration.CorePathIntegral`: for each actual acyclic
  degree-two core component, its ambient internal edges and its two genuine
  boundary edges split exactly, the component can be relabelled in its
  Hamilton order, and its conditional product-measure integral is precisely
  the existing path kernel.  The theorem constructs the path order and both
  boundary stubs from the concrete finite graph rather than assuming them as
  an interface.
- `PerronWright.Enumeration.CorePathAssembly`: simultaneously chooses the
  intrinsic lengths and actual endpoint stubs of every acyclic degree-two
  component and rewrites the literal graph weight as the branch-type integral
  of the branch factor times the full product of path kernels.  No endpoint or
  factorization interface is assumed.  The downstream kernel-weight modules
  transport this branch integral to bounded normalized kernel coordinates.
- `PerronWright.Enumeration.KernelGraphWeight`: transports that literal
  branch integral through any finite relabelling of the branch vertices,
  identifies direct branch edges with length-zero path factors, and proves
  from the actual two boundary stubs that each component path factor is
  exactly the unordered factor on its suppressed kernel edge.  The remaining
  literal branch factor is now also split, for general perturbation parameter
  `t`, into the relabelled branch-vertex weights and all length-zero direct
  edge factors.
- `PerronWright.Enumeration.NormalizedKernelIntegral`: combines the literal
  core-path assembly with the branch-vertex and kernel-edge relabellings to
  express every actual connected minimum-degree-two graph of positive
  surplus as an exact integral over a bounded normalized finite multigraph.
  The construction supplies the genuine unordered endpoint table and assigns
  length zero precisely to direct branch edges; no abstract kernel-weight
  interface is assumed.  What remains is to regroup these exact integrals by
  finite kernel shape and path lengths and then extract the Perron--Wright
  singular asymptotics.
- `PerronWright.Enumeration.ExactCubicKernelIntegral`: specializes the
  normalized integral to an actual cubic core.  It proves the exact branch
  and edge counts `2 * ell` and `3 * ell`, relabels the concrete graph onto
  the canonical normalized cubic finite multigraph, supplies its genuine
  unordered endpoint table and path lengths, proves every normalized vertex
  has literal degree three (with loops counted twice), and gives the exact
  path-kernel integral for arbitrary real `t`.  The remaining cubic task is
  to regroup these integrals over the finitely many kernel shapes and length
  assignments and then perform the singular coefficient analysis.
- `PerronWright.Enumeration.KernelLengthRegroup`: assigns every actual
  admissible two-core a bounded normalized endpoint table and the genuine
  number of suppressed degree-two vertices on each kernel edge, and gives an
  exact finite fibre decomposition by that datum.  At this coarse stage the
  inner summand deliberately retains the literal leaf-pruning terminal marks,
  so no attached-tree classification is assumed.
- `PerronWright.Enumeration.MarkedPathFactor`: defines the literal suppressed
  path integral with one genuine terminal mark at every internal core vertex.
  It proves that all-one marks recover the existing path kernel, including
  length-zero direct edges, and that simultaneous reversal of endpoints,
  Hamilton order, and ordered marks leaves the contribution unchanged.
- `PerronWright.Enumeration.MarkedPathOperatorPower`: for one common internal
  mark, packages its complete vertex profile as
  `mark * exp(-t*d)` and proves the literal marked path is exactly the matrix
  coefficient of `(t K M_profile)^n` applied to the terminal `tK` column.
  This supplies the previously missing finite-path-to-operator bridge while
  making neither a path-length sum nor a resolvent assertion.
- `PerronWright.Enumeration.MarkedCoreFactorization`: factors the literal
  marked two-core integrand into its branch block and its actual degree-two
  components, justifies the conditional product integration, and transports
  every component through a genuine Hamilton ordering to the marked path
  factor.  The public interface records only the resulting exact integral,
  the branch relabelling, and endpoint alignment; all auxiliary Fubini and
  reindexing lemmas remain private.
- `PerronWright.Enumeration.DecoratedKernelRegroup`: packages each actual
  marked terminal two-core into a minimal normalized datum carrying path
  lengths, oriented endpoints, branch marks, and ordered internal path marks.
  The unordered kernel table is derived rather than duplicated.  It proves
  the exact decorated integral for every graph and regroups the connected
  weight over the finite image of the actual finite graph family, without
  asserting that the ambient continuous decoration space is finite.
- `PerronWright.Enumeration.TreeRootComponents`: in a finite tree, deleting
  the root separates distinct root neighbors, and each resulting component
  has exactly one neighbor of the root. Integral factorization for the full
  rooted-tree recursion remains open.
- `PerronWright.Enumeration.TreeRootPartition`: root neighbors are equivalent
  to the deleted-root components; these components form a finite partition
  and each induced component remains a tree. Graph-weight and integral
  factorization of these blocks is still open.
- `PerronWright.Enumeration.TreeRootFinRelabel`: for a tree on `Fin (n+1)`,
  each block after deleting vertex zero is represented by a genuinely
  relabelled tree on `Fin |B|`, with proved component support and tree
  properties. Its weighted product/integration formula is still open.
- `PerronWright.Enumeration.TreeRootVertexFactor`: the zero-field vertex
  factors of an actual finite tree split exactly into the root factor and
  a product over deleted-root component blocks; each non-root tree edge
  lies within one block.
- `PerronWright.Enumeration.TreeRootEdgeFactor`: the actual finite-tree
  edge-factor product likewise splits into root-neighbor edges and internal
  edges of the deleted-root blocks, with the latter rigorously relabelled.
  The product-measure integral split and all-size EGF recursion remain open.
- `PerronWright.Enumeration.TreeRootKernelFactor`: each real root-neighbor
  edge factor is exactly the corresponding kernel value, so the entire
  actual finite-tree edge product has the root-kernel × block-internal
  factorization needed before integration.
- `PerronWright.Enumeration.TreeRootIntegrandFactor`: the complete actual
  finite-tree integrand factors pointwise as root vertex weight × root
  neighbor kernels × deleted-root block integrands. Product-measure
  integration and the all-size coefficient recursion remain open.
- `PerronWright.Enumeration.TreePartitionIntegral`: an explicit measurable
  equivalence regrouping actual finite coordinates by Finpartition blocks,
  proved measure-preserving for product measures, together with the exact
  integral-of-block-products identity. The tree-specific integration step
  is supplied by the next module.
- `PerronWright.Enumeration.TreeRootBlockIntegral`: after fixing the root
  type, the genuine zero-field finite-graph integral over all other types
  factors exactly over the connected blocks obtained by deleting the root;
  root-neighbor kernel factors are assigned to their unique blocks. The
  remaining work is the labelled-tree sum and all-size coefficient recursion.
- `PerronWright.Enumeration.TreeRootBlockNeighbor`: for an actual tree, each
  root-deleted block contains exactly one root neighbor, and its entire
  conditional root-kernel product is exactly that single kernel factor.
- `PerronWright.Enumeration.TreeRootBlockRelabel`: fixing that unique root
  neighbor, the genuine block integrand is exactly relabelled as its single
  parent kernel factor times the zero-field integrand of the actual induced
  block tree on `Fin |B|`; all vertex and edge products are transported
  explicitly.  A product-measure-preserving coordinate equivalence also
  transports the full block integral to these standard finite coordinates.
- `PerronWright.Enumeration.FixedRootedGraphProfile`: integrates the genuine
  zero-field weight of any fixed labelled rooted graph into a continuous
  root-type profile and proves that adjoining and integrating one parent
  kernel factor is exactly the model's existing kernel-action operator.
  Applied to each actual root-deleted tree block, this closes the full block
  integral as a kernel action on its concrete relabelled tree profile.
- `PerronWright.Enumeration.RootedProfileRelabel`: proves that the genuine
  continuous zero-field profile of a fixed rooted graph is invariant under
  simultaneous finite relabelling of the graph and its distinguished root.
  The complementary coordinates are reindexed by an explicit equivalence and
  the iid product measure is transported using the existing product-coordinate
  theorem. Consequently, after summing over every labelled tree of a fixed
  size, the total rooted profile is independent of the chosen root label.
- `PerronWright.Enumeration.TreeRootBranchDecomposition`: constructs both
  directions of the exact finite equivalence between a labelled tree on
  `Fin (n+1)` and a partition of the non-root labels carrying one independently
  rooted labelled tree on each block.  The assembled graph is proved to be a
  tree, both inverse laws are proved through the dependent branch family, and
  the genuine fixed-tree integral and rooted-tree numerator are rewritten as
  the root vertex factor times the product of the actual block kernel actions.
  Thus the remaining tree step is only the finite summation of independent
  rooted branches and its identification with the already-proved labelled
  exponential formula.
- `PerronWright.Enumeration.LabelledRootBranchSum`: relabels a rooted tree on
  an arbitrary partition block as a tree on `Fin |B|` together with its root
  label, reindexes the complete finite sum, and uses the proved rooted-profile
  permutation invariance to identify it exactly with `|B|!` times the genuine
  coefficient of the type-resolved rooted-tree series.  This closes the
  concrete block weight required by the labelled exponential formula.
- `PerronWright.Enumeration.RootedTreeFormalIdentity`: performs the remaining
  dependent product-of-sums reindexing over genuine root-deleted branches,
  applies the actual kernel action to every block profile, cancels the exact
  factorial normalization, and proves coefficientwise that the genuinely
  enumerated type-resolved rooted-tree series satisfies
  `T = X exp(-d) exp(KT)`.  This is an equality of formal power series derived
  from literal labelled-tree integrals, not an assumed recurrence.
- `PerronWright.Enumeration.RootedTreeFormalUniqueness`: proves directly from
  the coefficient recurrence for a substituted exponential that its degree
  `n` coefficient only depends on the input through degree `n`.  Strong
  induction then shows that the genuine labelled-tree series is the unique
  zero-constant formal fixed point of `T = X exp(-d) exp(KT)`.  No convergence
  radius or analytic coefficient identification is assumed in this step.
- `PerronWright.Enumeration.RootedTreeComplexFormal`: complexifies the genuine
  type-resolved labelled-tree series coefficientwise, proves that
  complexification commutes with the compact-kernel action and with the formal
  rooted-tree right-hand side, and obtains the complex fixed-point equation.
  It also proves uniqueness of its zero-constant complex formal solution.  The
  next module identifies the Taylor series of the actual local analytic tree
  branch with this formal fixed point.
- `PerronWright.Enumeration.RootedTreeAnalyticBridge`: converts the
  one-variable Banach-valued Taylor expansion to a genuine power series,
  proves compatibility with the compact-kernel action, and proves rather than
  assumes that analytic exponential composition is formal substitution into
  `exp`.  Applying `dslope` to the actual zero-field implicit branch yields
  the complex rooted-tree fixed point; formal uniqueness therefore identifies
  its complete Taylor series with the literal labelled-tree enumeration.
- `PerronWright.Enumeration.RootedTreePhysicalSeries`: chooses the canonical
  one-variable formal multilinear representative of that enumerative power
  series, rewrites the actual analytic germ with exactly this Taylor series,
  and constructs the formal Picard iterates.  It proves that after `n`
  iterations every coefficient below degree `n` has stabilized to the actual
  labelled-tree coefficient, and proves pointwise nonnegativity and
  monotonicity of the genuine finite partial sums.  The endpoint domination
  by the corresponding physical Picard iterate is deliberately not assumed.
- `PerronWright.Enumeration.RootedTreeDomination`: proves that missing
  endpoint bridge.  A finite scalar truncation lemma bounds formal
  substitution into `exp` by the genuine exponential of the truncated
  input; after pointwise kernel evaluation this gives
  `S_(N+1) <= Phi_w(S_N)` and hence `S_N <= V_N` for the actual physical
  Picard iterates.  No radius of convergence or probabilistic extinction
  statement is used as an input.
- `PerronWright.Enumeration.RootedTreeRadiusLower`: evaluates that finite
  domination at the critical parameter to prove a uniform sup-norm bound
  of one for every genuine labelled-tree coefficient.  Coefficientwise
  complexification is isometric, so the canonical Banach-valued Taylor
  series has convergence radius at least one.  This is derived from the
  actual finite enumeration and physical Picard bounds, rather than assumed
  as an analytic input.
- `PerronWright.Enumeration.RootedTreeSeriesPhysical`: sums the literal
  Banach-valued rooted-tree Taylor series on its full convergence ball and
  proves there that it satisfies the genuine compact-BJR tree equation.
  On the real subcritical interval the sum is real, lies pointwise in
  `[0,1]`, and equals the unique bounded physical fixed point obtained by
  monotone iteration.
- `PerronWright.Enumeration.RootedTreeRadiusExact`: combines the enumerative
  lower bound with the proved critical nonanalyticity obstruction.  If the
  radius exceeded one, the full-ball residual identity would extend the
  genuine tree series analytically through the critical point; hence its
  convergence radius is exactly one.
- `PerronWright.Enumeration.RootedTreeEndpointSum`: proves the missing
  critical-boundary statement rather than inferring it from the radius.  The
  actual nonnegative labelled-tree partial sums at activity one converge in
  the uniform norm to the constant profile one.  An explicit finite-subset
  argument upgrades this sequential convergence to genuine unconditional
  `HasSum` statements for both the real coefficients and the complex formal
  multilinear series at `z = 1`.
- `PerronWright.Enumeration.RootedTreeClosedDisk`: extends the actual complex
  labelled-tree series to every activity in the closed unit disk, using only
  finite-sum domination by the preceding nonnegative endpoint series.  It
  proves uniform convergence and continuity on the closed disk.  The genuine
  one- and two-vertex coefficients are extracted from the finite tree
  equation and shown strictly positive; their phase defect yields the strict
  bound `‖T(z)‖ < 1` at every nontrivial point of the unit circle, together
  with a uniform margin on compact arcs avoiding `1`.
- `PerronWright.Enumeration.FieldRootedTreeFinite`: builds the genuine
  complex-field type-resolved weight of every finite rooted labelled tree
  directly from the graph integral and proves analytic dependence on the
  field.  Root deletion, block integration, relabelling, and the parent
  kernel action are carried out for the actual finite integrands; summing the
  resulting branch profiles gives the concrete finite combinatorial input
  for the field-dependent formal tree equation.  No convergence at the
  complex critical boundary is asserted at this finite stage.
- `PerronWright.Enumeration.FieldRootedTreeFormal`: completes that finite
  decomposition at every order.  The literal field-weighted labelled-tree
  series satisfies the full formal tree equation coefficient by coefficient,
  and it is the unique zero-constant formal fixed point.  This is an actual
  finite-enumeration identity, not an assumed generating-function interface.
- `PerronWright.Enumeration.FieldRootedTreeAnalyticGerm`: identifies the
  Taylor series of the genuine joint analytic implicit branch at the origin
  with the preceding field-weighted labelled-tree series for every
  sufficiently small complex field.  The result is deliberately local: it
  does not assert convergence or continuation at the critical boundary.
- `PerronWright.Enumeration.CoreForestAttachments`: for a fixed ordered core,
  defines the literal finite data of labelled rooted-tree blocks together
  with their incident core vertices, performs the dependent product-of-sums
  reindexing, and proves the exact labelled-exponential coefficient formula
  for their total compact-BJR weight.  The module does not assume the still
  separate classification of arbitrary connected graphs by these data.
- `PerronWright.Enumeration.CoreAttachmentAssembly`: explicitly assembles a
  fixed ordered core and genuine labelled rooted-tree attachment data into a
  finite simple graph.  The core, off-core partition, every branch, and every
  root edge are recovered from the assembled graph; the construction is
  injective, connected, and preserves the exact paper surplus.  In the
  converse direction it proves that the complement of the greatest two-core
  is a forest whose components all meet the core.
- `PerronWright.Enumeration.CoreAttachmentForward`: closes the missing
  structural direction for every connected finite graph of positive paper
  surplus.  Maximal leaf pruning is identified explicitly with the induced
  greatest two-core, the ambient edge set is split into core, off-core, and
  crossing edges, and the forest Euler identity shows that the number of
  crossing edges equals the number of off-core components.  The genuine
  oriented boundary edges are then put in an explicit equivalence with the
  unordered crossing edges; since every off-core component is met, the
  boundary-to-component map is bijective.  Thus every component outside the
  greatest two-core has exactly one core edge, without postulating a fibre or
  selecting a fictitious graph-to-decoration inverse.
- `PerronWright.Enumeration.CoreAttachmentSplitForward`: turns that uniqueness
  into actual forward attachment data when the labels are already split as
  `Fin q ⊕ Fin n` with the core on the left.  It constructs the genuine
  off-core component partition, its induced rooted trees and unique core
  incidences, and proves that assembling these recovered data returns the
  original graph literally.  No choice fibre is substituted for the forward
  classification.
- `PerronWright.Enumeration.CoreAttachmentArbitrary`: removes the split-label
  restriction.  It deterministically orders the literal greatest two-core and
  its complement, proves that the relabelled graph has exactly the left labels
  as its greatest two-core, applies the genuine forward construction, and
  proves exact recovery after assembly.  Thus an arbitrary `Fin k` graph is
  classified up to an explicit proved relabelling, not an assumed bijection.
- `PerronWright.Enumeration.CoreAttachmentWeightRelabel`: defines the literal
  annealed weight on any finite vertex type and proves invariance under a
  genuine graph isomorphism by explicitly reindexing the iid product measure.
  In particular, the deterministic core/off-core split preserves the paper's
  labelled graph weight exactly.
- `PerronWright.Enumeration.CoreAttachmentWeightFactor`: reindexes the actual
  edge and vertex products of an assembled core with rooted-tree attachments,
  factors the iid product integral block by block, and identifies every block
  integral with the genuine kernel action on its rooted-tree profile.  For a
  fixed ordered core it proves both the exact weight of each attachment datum
  and the finite sum over all data, the latter closing directly with the
  previously proved labelled-forest exponential coefficient formula.
- `PerronWright.Enumeration.CoreAttachmentFieldWeightFactor`: proves the same
  fixed-core factorisation for the genuine complex external-field weights.
  Each literal finite graph integral is split into its core block and true
  field-rooted attachment profiles, and the finite sum over all attachments
  is identified exactly with the complex branch-series exponential
  coefficient.  No field-dependent graph-weight interface is assumed.
- `PerronWright.Enumeration.CoreAttachmentWeightArbitrary`: applies the fixed
  attachment factorization to the deterministic split of an arbitrary
  labelled connected positive-surplus graph.  Its original annealed weight is
  proved equal to the literal core-type integral for the genuine attachment
  datum extracted by `forwardSplitCoreAttachment`; no graph-to-decoration
  classification bijection is assumed.
- `PerronWright.Enumeration.CoreAttachmentCoreIdentity`: proves that the
  greatest two-core of every explicit admissible core-with-rooted-forest
  assembly is exactly its displayed core summand.  The hard inclusion is
  obtained from a proved two-leaves theorem for finite forests and the unique
  parent edge of each attachment block.  This is the inverse fact needed to
  replace abstract classification-fibre multiplicities by explicit choices
  of the original core-label subset.
- `PerronWright.Enumeration.CoreAttachmentChooseClassification`: indexes the
  possible core/off-core sizes by the finite natural antidiagonal and the
  original core labels by literal `q`-element subsets of `Fin k`.  For every
  fixed admissible ordered core and attachment datum, increasing relabelling
  gives an explicit equivalence between those subsets and its concrete
  original-label assembly fibre.  The inverse is the literal greatest
  two-core finset, so the fibre cardinal is proved to be exactly
  `Nat.choose k q`, with no factorial or automorphism correction.
- `PerronWright.Enumeration.CoreAttachmentGlobalClassification`: packages
  the preceding subsets, admissible ordered cores, and rooted-forest data
  over the antidiagonal and proves an explicit equivalence with
  `fixedSurplusGraphs k ell`.  Its inverse deterministically takes the actual
  greatest two-core, the increasing core/complement split, and the genuine
  forward attachment.  Fixed-size and cross-size injectivity prove that the
  fibres cover the graph set without overlap, supplying the exact finite
  classification used by the following weighted reindexing.
- `PerronWright.Enumeration.CoreAttachmentGlobalWeightSum`: reindexes the
  full fixed-surplus graph sum through that explicit global equivalence for
  both the genuine real graph weight and the genuine complex external-field
  weight.  For each ordered core and attachment, invariance under the actual
  relabelling isomorphism makes the literal core-label-subset sum constant;
  `card_coreLabelSubset` then supplies exactly `Nat.choose k q`.  The
  remaining attachment sum is identified with the previously proved
  exponential coefficient integral for the complex-field weight and for the
  real weight at `t = 1`.  The module also gives the corresponding real
  zero-field and complex-field connected-weight identities, without an
  abstract weight interface or an assumed fibre multiplicity.
- `PerronWright.Enumeration.UnicyclicCore`: identifies the admissible ordered
  cores in attachment surplus `ell = 0` exactly with connected 2-regular
  finite simple graphs, and proves that every such core has at least three
  vertices.  This closes the graph-theoretic entry point for the unicyclic
  layer without assuming a cycle classification or labelled multiplicity.
- `PerronWright.Enumeration.UnicyclicCycleIso`: proves from first principles
  that every connected 2-regular simple graph on `Fin q` is isomorphic to
  `cycleGraph q`, and hence classifies every admissible surplus-zero core as
  a cycle.  The proof obtains an actual cycle copy, uses two-core closure and
  connectedness to prove that its vertex map is surjective, recovers reverse
  adjacency from the two equal finite neighbor-set cardinalities, and upgrades
  the resulting relation embedding with `RelIso.ofSurjective`.  Thus no cycle
  classification theorem is postulated.
- `PerronWright.Enumeration.UnicyclicCycleMultiplicity`: realizes an oriented
  labelled `q`-cycle as a permutation with cycle type `{q}` and proves that
  forgetting its orientation has the literal two-element fibre
  `{sigma, sigma⁻¹}`.  Mathlib's cycle-type cardinality then gives `(q-1)!`
  oriented cycles, while the proved range of the forgetting map satisfies
  `range.card * 2 = (q-1)!` and, equivalently,
  `range.card * (2*q) = q!`.  Thus the `1/(2q)` multiplicity is derived
  without division or an assumed fibre-size interface.
- `PerronWright.Enumeration.UnicyclicCycleRange`: proves that the standard
  full cycle `finRotate` forgets to `cycleGraph`, transports it under explicit
  permutation conjugation, and characterizes the orientation-forgetting
  range exactly as the connected 2-regular labelled graphs.  Combining this
  with `UnicyclicCore` gives the literal finite-set identity
  `graphRange q = admissibleAttachmentCores q 0` for `q ≥ 3`.
- `PerronWright.Enumeration.UnicyclicCycleWeightTrace`: evaluates the genuine
  complex finite-graph weight of `cycleGraph q` as the direct profile cycle
  trace by exposing one cycle coordinate, applying product-law Fubini, and
  integrating the resulting path recursively as an operator power.  It then
  combines this identity with the proved unoriented labelled-cycle
  multiplicity and the exact `graphRange` classification to identify the
  `q!`-normalized sum over all admissible surplus-zero cores with
  `profileSimpleCycleTerm M tau (q-3)`.  Thus the full `1/(2q)` simple-cycle
  factor is derived from literal finite graph weights, without an assumed
  weight-sum interface.
- `PerronWright.Enumeration.UnicyclicCompositionCoeff`: defines literal
  fixed-core profile composition directly from a `C(S,ℂ)`-valued rooted-tree
  power series: remove its compulsory leading variable, evaluate the tail at
  each core type, multiply over the core vertices, and integrate against the
  genuine core edge weight.  The proved rooted-tree formal equation identifies
  its coefficients with the exact attachment-exponential integral.  Summing
  over all admissible cycle cores and cancelling the labelled factorials proves
  that the genuine complex-field unicyclic connected weight divided by `k!`
  is exactly this composition coefficient.  A monomial-profile specialization
  independently recovers the direct simple-cycle trace term through the proved
  labelled-cycle subtype identity; no attachment or composition interface is
  assumed.
- `PerronWright.Enumeration.FixedSurplusCompositionCoeff`: removes the
  surplus-zero restriction from that exact identity.  For every attachment
  surplus `ell`, the genuine complex connected weight with paper parameter
  `ell + 1`, divided by `k!`, is proved equal to the size-`k` coefficient of
  the finite sum of literal fixed-core rooted-profile compositions.  The
  proof uses the existing all-core attachment classification and proves the
  factorial cancellation directly; it introduces no kernel asymptotic
  interface.
- `PerronWright.Enumeration.CubicKernelSubdivision`: introduces the
  parameter-free finite data for the next exact reindexing step: a cubic
  edge-labelled kernel, admissible degree-two path lengths, and one label
  equivalence covering all branch and internal slots.  Loop lengths and
  zero-length parallel-edge restrictions encode precisely the simplicity
  constraints.  Loop orientation bits are kept explicit, preventing the
  usual two-to-one reversal ambiguity from being hidden in an interface.
- `PerronWright.Enumeration.CubicKernelSubdivisionCount`: proves the first
  exact cardinalities of that data: the subdivision-slot type has precisely
  `k` elements, its exact label equivalences are counted by `k!`, and the
  explicit loop-orientation choices are counted by `2 ^ (# loops)`.  These
  are multiplicative integer identities, so no premature natural-number
  division or symmetry-factor cancellation is assumed.
- `PerronWright.Enumeration.CubicKernelReconstruction`: reconstructs the
  literal labelled graph determined by admissible cubic-kernel subdivision
  data.  Consecutive positions on every subdivided kernel edge give exactly
  `k + ell` edge slots; admissibility makes their emitted unordered endpoint
  pairs injective and loopless.  Consequently the reconstructed simple
  support on `Fin k` has exactly `k + ell` edges.  Connectivity and degree
  control are supplied by the next module; the inverse classification is
  deliberately not assumed here.
- `PerronWright.Enumeration.CubicKernelConnectivity`: proves directly that
  subdividing a connected cubic kernel produces a connected simple graph and
  that every reconstructed vertex has degree at least two.  Together with
  the exact edge count above, `reconstructedGraph_admissible` now packages
  precisely the connected/minimum-degree-two/fixed-surplus output needed by
  the inverse-classification layer.
- `PerronWright.Enumeration.CubicKernelInverseGeometry`: embeds the literal
  endpoint occurrences of each cubic-kernel branch vertex injectively into
  the reconstructed incident edges.  Summing the resulting branch lower
  bounds together with the internal degree-two bounds saturates the global
  handshake identity.  Hence every internal subdivision label has degree
  exactly two and every branch label has degree exactly three, equal to its
  kernel degree.  Consequently degree-two vertices are exactly the internal
  path labels, while degree-three (equivalently branching) vertices are
  exactly the branch labels.  This is the geometric entry point for, but does
  not assume, the still-missing inverse classification.
- `PerronWright.Enumeration.CubicSubdivisionComponentRecovery`: identifies
  the induced degree-two geometry of every admissible reconstruction exactly.
  Internal labels are adjacent precisely when they are consecutive positions
  on one normalized kernel edge; different kernel edges cannot meet inside
  the degree-two graph.  Consequently the positive-length kernel edges are
  canonically equivalent to the connected components of that graph.  Both
  directions and the recovered-edge uniqueness are proved from the literal
  subdivision table, without a component-classification interface.
- `PerronWright.Enumeration.CubicSubdivisionSuppressionRecovery`: completes
  the edge-label recovery split.  Zero-length normalized kernel edges are
  exactly the direct branch edges of the reconstructed graph, while
  positive-length edges are the degree-two components above.  The two
  equivalences combine into an explicit recovered suppressed-edge labelling;
  positive component cardinalities and the zero-length endpoint table are
  recovered exactly.
- `PerronWright.Enumeration.CubicSubdivisionPositiveEndpointRecovery`:
  recovers the missing endpoint table for every positive-length kernel edge.
  The first and last boundary stubs identify the two original branch labels;
  combining this with the zero-length case proves equality of the entire
  recovered branch-endpoint table with the input kernel table.
- `PerronWright.Enumeration.CubicPositiveEdgePathIso`: upgrades each recovered
  positive-edge index equivalence to a graph isomorphism from the canonical
  finite path, records its two boundary endpoints, and packages path rigidity:
  any competing coordinate is either the canonical order or its reversal,
  while agreement at the first endpoint forces pointwise equality.
- `PerronWright.Enumeration.CubicSubdivisionLengthRecovery`: defines the
  intrinsic length of a suppressed edge as the cardinality of its degree-two
  component, with length zero on direct branch edges.  Under the canonical
  recovered edge labelling this intrinsic vector agrees pointwise with the
  input subdivision profile, and equality of the recovered vectors determines
  the complete admissible length profile in fixed kernel-edge coordinates.
- `PerronWright.Enumeration.CubicLoopOrientationAction`: constructs the
  literal involution which reverses all internal labels on one loop edge.
  Branch labels and every other edge are fixed, the chosen loop order is
  reversed, and applying the operation twice restores every label.  Thus the
  Boolean loop-orientation symmetry is represented by an actual operation,
  not only by a cardinality factor.
- `PerronWright.Enumeration.CubicLoopOrientationGraph`: lifts that label
  involution to the emitted edge table.  Reversing a subdivided loop merely
  permutes its consecutive edge slots, so the reconstructed edge finset and
  hence the complete labelled simple graph are exactly unchanged.
- `PerronWright.Enumeration.CubicLoopOrientationFreeness`: proves that each
  loop reversal is an involution, reversals at distinct loop labels commute,
  and every individual reversal is fixed-point-free on admissible labelled
  subdivision data.  These are the local algebraic facts needed to assemble
  the Boolean loop-orientation action and count its orbit exactly.
- `PerronWright.Enumeration.CubicLoopOrientationBooleanAction`: assembles all
  loop reversals into a coordinatewise Boolean action whose composition law
  is symmetric difference.  Every nonempty orientation set acts without a
  fixed point, the action map on a fixed subdivision datum is injective, and
  its orbit has exactly `2^(number of loop edges)` elements.  What remains in
  the fixed-coordinate fibre problem is to prove that this orbit exhausts the
  entire fibre of the reconstructed labelled graph.
- `PerronWright.Enumeration.CubicFixedCoordinateFibre`: proves that every
  simultaneous Boolean loop reversal preserves the complete reconstructed
  labelled graph, and packages path rigidity as an explicit Boolean choice on
  every recovered positive edge.  Once the first boundary coordinate is
  anchored the reversal alternative disappears.  An explicit assembly theorem
  then selects the unique finite set of reversed loops and identifies the
  second labelling with the corresponding Boolean action.  Thus the remaining
  global converse is isolated to aligning the recovered edge/component
  coordinates of two data, including the parallel-edge ambiguity; no
  fixed-coordinate or graph-invariance direction remains open.
- `PerronWright.Enumeration.CubicRecoveredCoordinateConverse`: completes the
  converse once the recovered branch and positive-edge component coordinates
  have been fixed.  Path rigidity constructs a unique loop-reversal set, even
  for kernels with parallel edges, and proves that its Boolean action is the
  second subdivision labelling.  The only remaining global fibre issue is now
  the construction and transport of those recovered coordinates themselves,
  including the parallel-edge permutation.
- `PerronWright.Enumeration.CubicRecoveredCoordinateAlignment`: constructs
  canonical branch and kernel-edge coordinate permutations from equality of
  reconstructed labelled graphs.  The edge permutation passes through the
  intrinsic suppressed-edge type, so parallel edges remain distinct.
  Subdivision lengths and endpoint tables are preserved.  Its equivalence of
  subdivision slots follows the aligned endpoint order on non-loops and leaves
  loop coordinates unreversed for the separate Boolean loop action.
- `PerronWright.Enumeration.CubicRecoveredCoordinateGlobalFibre`: transports
  the positive degree-two components and their ordered path coordinates
  through that intrinsic alignment, including parallel kernel edges.  The
  anchored first coordinate removes the non-loop reversal alternative, and
  the recovered-coordinate converse then proves that the complete labelled
  fibre is exactly one unique Boolean orbit of loop reversals.
- `PerronWright.Enumeration.CubicReconstructionFibreBound`: encodes every
  reconstruction fibre by the two recovered coordinate permutations and the
  unique set of reversed kernel loops.  The code is injective, so each fibre
  is finite and has the explicit bound
  `(2*ell)! * (3*ell)! * 2^(number of kernel loops)`.  This is a genuine
  multiplicity bound; it does not replace the still finer endpoint-compatible
  symmetry quotient by an assumed exact factor.
- `PerronWright.Enumeration.CubicSubdivisionClassification`: identifies the
  cubic members of the literal positive-surplus admissible-core class exactly
  with reconstructed subdivisions of connected edge-labelled cubic kernels.
  It also restates the proved fixed-kernel fibre bound over a literal target
  graph, without asserting an unproved automorphism factor.
- `PerronWright.Enumeration.CubicReconstructionWeight`: proves pointwise that
  the actual weight of one reconstructed graph is exactly the path-kernel
  integral encoded by the same kernel endpoint table and subdivision-length
  profile; no replacement data or multiplicity claim is used.
- `PerronWright.Enumeration.CubicReconstructionFieldWeight`: constructs the
  canonical decorated-kernel datum from the subdivision labels themselves.
  It identifies both constant-marked graph weights and arbitrary real-field
  graph weights with their literal decorated-kernel integrals, so the field
  factorization is also a theorem rather than an interface assumption.
- `PerronWright.Enumeration.CubicKernelCoordinateRelabel`: begins the exact
  global-presentation quotient needed for the Wright symmetry factor.  It
  synchronously relabels kernel vertices, kernel edges, endpoint tables,
  admissible length profiles, path directions, subdivision slots, and their
  labels, while proving degree, connectedness, loop-count, and endpoint-order
  invariance.  It does not infer an exact fibre cardinality from the earlier
  upper bound.
- `PerronWright.Enumeration.CubicKernelCoordinateReconstruction`: completes
  the graph-level transport under simultaneous kernel-coordinate relabelling.
  Explicit vertex and edge-slot equivalences handle both direct and reversed
  path orientations; every emitted unordered subdivision edge is unchanged,
  so the reconstructed labelled simple graph is literally equal, not merely
  isomorphic.  No quotient-cardinality claim is made at this stage.
- `PerronWright.Enumeration.CubicGlobalPresentationSymmetry`: passes from a
  fixed kernel to the dependent sigma type of all edge-labelled cubic-kernel
  presentations.  Coordinate transport followed by any set of loop-path
  reversals preserves the reconstructed labelled graph, and the dependent
  choice type has the exact cardinality
  `(2*ell)!*(3*ell)!*2^(number of loops)`.  This counts symmetry codes only;
  injectivity and exhaustion of the global reconstruction fibre remain
  separate proof obligations.
- `PerronWright.Enumeration.CubicKernelCoordinateActionLaws`: proves that the
  branch/edge relabelling construction is an honest action, including the
  orientation-sensitive path-index and subdivision-slot transports.  It
  supplies identity and composition laws for kernels, length profiles,
  subdivision data, branch labels, path labels, and global presentations;
  all dependent equalities are proved rather than hidden behind a new cast
  interface.
- `PerronWright.Enumeration.CubicGlobalPresentationActionLaws`: transports
  loop subsets through coordinate relabelling and proves that this transport
  commutes with path reversal.  The dependent coordinate-plus-loop codes now
  have explicit identity and composition operations whose action on global
  presentations satisfies the corresponding laws.
- `PerronWright.Enumeration.CubicGlobalPresentationFibre`: constructs the
  canonical branch and intrinsic-kernel-edge permutations between two global
  presentations of the same labelled reconstructed graph.  It proves that
  these coordinates carry the first endpoint table and normalized kernel to
  the second, and packages the resulting coordinate-plus-loop action as the
  explicit map into the global reconstruction fibre.
- `PerronWright.Enumeration.CubicGlobalPresentationAlignedCast`: moves one
  presentation into the globally recovered coordinates of another and then
  performs the necessary dependent cast along the proved kernel equality.
  The cast preserves the reconstructed graph, branch labels, and complete
  length profile, and makes the recovered branch-coordinate permutation
  literally the identity.  These are proved transport facts, not a quotient
  or proof-irrelevance assumption hidden behind the fibre count.
- `PerronWright.Enumeration.CubicRecoveredKernelEdgeNaturality`: proves that
  intrinsic positive-component edges and zero-length direct edges commute
  with coordinate relabelling and with the dependent kernel cast.  After the
  global alignment, both recovered edge and branch permutations are the
  identity, the dependent path-index transport preserves its numerical
  coordinate, and the target datum is reached by one unique set of loop
  reversals.  The required `HEq` transports are explicit theorems.
- `PerronWright.Enumeration.CubicGlobalPresentationFibreEquiv`: proves that
  the coordinate-plus-loop symmetry map is both injective and surjective
  onto the complete reconstruction fibre.  It supplies an explicit inverse
  code, an actual equivalence, a finite structure induced by any base
  presentation, and the exact fibre cardinality
  `(2*ell)!*(3*ell)!*2^(number of loop labels)`; this is no longer only an
  upper bound or orbit heuristic.
- `PerronWright.Enumeration.CubicGlobalWeightedRegroup`: converts that exact
  fibre cardinality into finite weighted-sum identities.  Summing any
  reconstructed-graph invariant over all global cubic presentations gives
  the literal sum over admissible labelled cubic cores multiplied by the
  proved fibre size; weighting each presentation by the reciprocal fibre
  size recovers the graph sum exactly.  No automorphism or orbit factor is
  left as an interface.
- `PerronWright.Enumeration.CubicPresentationProfileRegroup`: then removes
  the subdivision-label fibre exactly.  For each fixed labelled cubic
  kernel it identifies subdivision data with a length profile and one of
  precisely `k!` slot labellings, and combines this with the global fibre
  factor to obtain the exact profile coefficient
  `k!/((2*ell)!*(3*ell)!*2^(number of loops))`, including its literal
  constant-marked kernel-integral specialization.
- `PerronWright.Enumeration.CubicKernelPathGeneratingSeries`: identifies a
  cubic length profile with the admissible part of the finite antidiagonal
  of all kernel-edge length assignments, realizes the unrestricted
  antidiagonal as the coefficient of the finite product of one-edge marked
  path series, and proves on a strict subcritical profile ball that each
  one-edge sum is the constructed path-resolvent kernel.  Thus the
  finite-product resolvent formula is now an exact power-series identity;
  the simple-graph restrictions remain visible as an explicit admissibility
  predicate instead of being hidden in an unrestricted product.
- `PerronWright.Enumeration.BoundedKernelPathGeneratingSeries`: extends the
  finite path-product series from cubic kernels to every bounded kernel
  endpoint table.  Its coefficients are the literal antidiagonals of all
  internal-length assignments, its sum on a strict subcritical profile ball
  is the genuine finite product of path-resolvent kernels, and the cubic
  specialization agrees definitionally with the preceding construction.
- `PerronWright.Enumeration.ComplexProfilePathCoefficient`: identifies every
  abstract one-edge coefficient with the literal complex-profile integral
  of the corresponding finite path.  It proves reversal symmetry, packages
  the coefficient canonically over unordered endpoint pairs, and converts
  each bounded-kernel product coefficient into the exact finite sum of
  products of literal path integrals.
- `PerronWright.Enumeration.ComplexProfileCorePathFactorization`: factors the
  literal complex weight of an arbitrary minimum-degree-two core into its
  branch block and independent degree-two path components.  It then
  integrates and canonically relabels those factors, proving that each
  component is exactly the corresponding path-series coefficient and that
  the resulting finite expression carries the expected one-dimensional
  formal power series.  All coordinate changes are proved measure
  preserving; no factorization identity is assumed.
- `PerronWright.Enumeration.CubicActualProfileIntegral`: specializes that
  factorization to an actual admissible subdivision of a labelled cubic
  kernel.  After the proved branch and kernel-edge relabellings, the literal
  finite-graph weight is exactly the canonical product of branch profiles
  and path coefficients integrated over the kernel coordinates.  This
  closes the coordinate gap between reconstructed graphs and the analytic
  resolvent amplitude.
- `PerronWright.Enumeration.CubicActualAdmissibleCoefficientBridge`: performs
  the exact finite regrouping from actual admissible cubic cores to labelled
  kernels and their admissible length profiles, including the factorial and
  loop-orientation multiplicities.  Consequently the cubic fixed-surplus
  composition coefficient is literally the finite admissible profile
  integral coefficient; this is an equality of the genuine graph weights,
  not a newly postulated enumerator.
- `PerronWright.Enumeration.CubicProfileCoefficientBounds`: derives a common
  geometric bound for every one-edge path coefficient directly from the
  Perron-weighted path-operator power estimate.  Counting the finite length
  antidiagonal then gives an explicit choose--geometric majorant for every
  admissible cubic profile coefficient and proves absolute summability on
  each strict subcritical profile ball.  This is the normal-convergence
  input for identifying the full composition Taylor series.
- `PerronWright.Enumeration.PositiveSurplusCubicCoefficientReindex`: proves
  directly from cubic reconstruction that every positive-surplus cubic core
  has at least `2*ell` vertices, rewrites the conditional ambient core sum
  as the genuine cubic-admissible subtype sum, and shifts the size index to
  `q = 2*ell+d`.  The resulting finite PowerSeries coefficient identity is
  the exact reindexing used by the full Taylor argument.
- `PerronWright.Enumeration.PositiveSurplusCubicFixedDegreeAnalytic`: realizes
  every fixed internal-degree coefficient as the finite composition FMS of
  the actual cubic admissible cores, with the exact labelled-EGF factorial.
  The auxiliary point of the type space is obtained internally from the
  probability measure and does not appear in the public statement; finite
  degree ranges inherit the corresponding summed FMS exactly.
- `PerronWright.Enumeration.PositiveSurplusCubicProfileAnalytic`: defines the
  full cubic profile contribution as the literal `tsum` of genuine
  admissible degree coefficients.  A finite inclusion--exclusion resolvent
  is used only internally to prove equality and analyticity throughout the
  strict unit profile ball; the public object retains its direct enumerative
  meaning.  The finite-product Fubini step now uses absolute summability in
  the ambient Banach algebra and no longer imposes a spurious
  finite-dimensional hypothesis.
- `PerronWright.Enumeration.CubicAdmissibleResolventCoefficientBridge`:
  reindexes the absolutely summable length assignments by total degree,
  interchanges the finite kernel integrals with their genuine `tsum`, and
  proves that the literal admissible profile series is exactly the analytic
  admissible path-resolvent sum on every strict subcritical profile ball.
  Its convergence is derived from the proved geometric bound rather than a
  finite-dimensional or abstract summability assumption.
- `PerronWright.Enumeration.PositiveSurplusCubicTailOrder`: combines the
  explicit choose--geometric coefficient majorant with a geometric tail to
  show that removing degrees below `N` leaves order
  `‖w‖^(2*ell+N)` after any analytic profile vanishing at the origin.  This
  is the exact vanishing order needed to identify every coefficient of the
  full cubic composition series, without assuming uniform convergence as a
  separate interface.
- `PerronWright.Enumeration.PositiveSurplusCubicFullTaylor`: merges the
  fixed-degree FMS, the high-order tail, and the exact `q=2*ell+d`
  reindexing.  It proves that the complete Taylor series of the literal
  admissible cubic profile functional is precisely the genuine cubic
  fixed-surplus composition series, coefficient by coefficient.
- `PerronWright.Enumeration.PositiveSurplusCubicFieldLocalBridge`: defines the
  actual complex-field cubic-part EGF and pulls the full profile Taylor
  theorem back along the genuine rooted-tree branch.  Its final wrapper
  keeps the distinction explicit: the total normalized connected
  coefficient is the cubic-part EGF coefficient plus the separately named
  noncubic contribution; no equality between the cubic part and the total
  weight is asserted.
- `PerronWright.Enumeration.PositiveSurplusCubicGlobalContinuation`: obtains
  the normalized tree profile internally, uses the literal profile series as
  the away chart and the canonical pole-removed admissible amplitude as the
  fold chart, proves their exact resolvent equality on the overlap, and
  glues them over one Cartesian-Delta product.  Its Taylor germ is the
  actual normalized cubic-part EGF; neither the global continuation nor the
  tree profile is supplied as an assumption.
- `PerronWright.Enumeration.PositiveSurplusCubicTransferData`: derives the
  transfer input directly from that genuine continuation.  It expands the
  local fold chart through order `3*ell+1`, packages the finite Puiseux
  polynomial explicitly, and proves that the remaining global analytic
  function is one half-step lower.  Thus the coefficient-transfer datum is
  constructed rather than postulated.
- `PerronWright.Enumeration.PositiveSurplusCubicCoefficientAsymptotic`:
  applies the Cartesian-Delta transfer theorem to the constructed datum,
  keeps all finitely many Puiseux correction terms explicit, and proves the
  normalized cubic coefficient has relative error
  `O(‖g‖ + k^(-1/2))` on one genuine complex field ball.  The nonvanishing
  of the exact leading pure-power coefficient is proved from the positive
  cubic constant and Gamma coefficient rather than assumed.
- `PerronWright.Enumeration.PositiveSurplusCubicFieldWeightAsymptotic`:
  converts the normalized coefficient theorem to the genuine labelled
  cubic contribution.  Exact EGF normalization, the quantitative Gamma
  coefficient correction, and Stirling's relative correction give the
  physical Wright scale with the same uniform
  `O(‖g‖ + k^(-1/2))` error.  The declaration deliberately remains a cubic
  summand theorem until the noncubic remainder transfer is closed.
- `PerronWright.Enumeration.CubicKernelForbiddenLengthCorrection`: classifies
  every failure of cubic-profile admissibility by one of two finite concrete
  witnesses: a loop of internal length zero or one, or two parallel kernel
  edges both of length zero.  It splits each unrestricted antidiagonal
  coefficient exactly into admissible and forbidden parts, proves that every
  forbidden witness pins an edge at length at most one, and records the
  resulting extra factor of the local fold coordinate after normalization.
- `PerronWright.Enumeration.PositiveSurplusCubicKernelInhabitant`: constructs,
  for every positive excess `ell`, an explicit connected labelled cubic
  multigraph on `2*ell` vertices and `3*ell` edge labels.  The construction
  is a cycle together with an opposite matching (with the three parallel
  edges handled uniformly when `ell = 1`), so nonemptiness of the finite
  cubic-kernel type is a theorem rather than an assumption.
- `PerronWright.Enumeration.FixedSurplusCubicNoncubicSplit`: partitions the
  literal fixed-surplus profile coefficient and the corresponding connected
  weight exactly into cubic and noncubic contributions.  It also proves the
  strict edge gap for every noncubic kernel and converts that gap into an
  explicit extra fold-coordinate factor; no analytic remainder estimate is
  postulated by this split.
- `PerronWright.Enumeration.BoundedKernelPathAmplitude`: removes the simple
  path-resolvent pole from every edge of an arbitrary bounded endpoint
  table and proves that their finite product is jointly analytic in the
  field and fold coordinate.  On the punctured germ it is exactly
  `X^(number of kernel edges)` times the literal resolvent product; combined
  with the strict noncubic edge gap, cubic normalization leaves an explicit
  analytic factor `X`.
- `PerronWright.Enumeration.NoncubicBoundedKernelRemainder`: multiplies the
  pole-removed path product by the genuine branch-profile factors for an
  arbitrary bounded kernel.  The strict noncubic edge deficit then gives an
  exact cubic-normalized factorization `X * R`, with `R` jointly analytic;
  the same statement is assembled over every finite fixed-size noncubic
  core family without assuming an all-length regrouping.
- `PerronWright.Enumeration.NoncubicVariableKernelRegroup`: suppresses the
  degree-two paths of each literal noncubic core into its canonical bounded
  endpoint table and intrinsic length assignment, proves the exact complex
  profile-integral identity, and regroups the finite fixed-size core sum by
  the genuine finite fibres of that map.  The fibre multiplicity remains a
  literal cardinal here; its closed symmetry formula is supplied by the
  subsequent global-presentation classification.
- `PerronWright.Enumeration.CubicKernelResolventAmplitude`: specializes the
  edgewise normalization to a labelled connected cubic kernel, multiplies
  it by the literal branch-profile product, and proves an analytic
  continuous-function-valued numerator.  On the punctured germ this
  numerator is exactly `X^(3*ell)` times the genuine path-resolvent
  integrand, while its joint-base value is computed explicitly from the
  Perron residue kernel.
- `PerronWright.Enumeration.CubicKernelIntegratedResolventAmplitude`: pulls
  every normalized edge kernel back to the finite product of branch
  coordinates and integrates with the genuine product type measure.  The
  resulting scalar amplitude is jointly analytic, is exactly
  `X^(3*ell)` times the integrated raw resolvent product on the punctured
  germ, and retains an explicit finite integral at the joint base point.
- `PerronWright.Enumeration.PositiveSurplusWrightConstant`: evaluates that
  base-point integral exactly.  Cubic incidence turns all endpoint residues
  into vertex cubes, finite-product Fubini supplies `beta^(2*ell)`, and the
  edge normalization leaves `sqrt(beta)^ell`.  The positive-surplus EGF and
  Wright constants are then literal finite sums over labelled connected
  cubic kernels with the already proved factorial and loop-orientation
  multiplicities; no constant is introduced as an assumed interface.
- `PerronWright.Enumeration.PositiveSurplusCubicConstantPositivity`: exposes
  real forms of both finite cubic constants, proves that the analytic complex
  constants are their canonical casts, and derives strict positivity for
  every positive excess from the explicit connected cubic-kernel inhabitant
  and positivity of the Gamma transfer factor.
- `PerronWright.Enumeration.PositiveSurplusWrightTransferMain`: separates the
  exact pure-power coefficient and factorial normalizations, combines the
  Gamma coefficient scale with quantitative Stirling, and proves that the
  resulting labelled main term is the physical Wright constant times
  `exp(-k) * k^(k+3*ell/2-1/2)`.
- `PerronWright.Enumeration.PositiveSurplusCubicIntegratedAmplitude`: sums
  the pole-removed integrated amplitudes over the finite labelled cubic
  kernel type with their exact inverse presentation multiplicities.  The
  sum is jointly analytic, has the evaluated Wright amplitude at the fold
  point, and is exactly `X^(3*ell)` times the unrestricted integrated
  resolvent sum on the punctured germ; the simple-graph exclusion remains
  an explicit finite coefficient correction.
- `PerronWright.Enumeration.CubicForbiddenAnalyticCorrection`: expands the
  simple-graph exclusion by finite inclusion--exclusion.  Every nonempty
  forbidden pattern fixes at least one path length, so its pole-removed
  intersection is jointly analytic and vanishes on the critical axis.
  Analytic vertical division therefore factors the complete forbidden
  correction by one explicit `X`, leaving the admissible cubic numerator
  with the same nonzero leading Wright amplitude.
- `PerronWright.Enumeration.CubicForbiddenCorrectionBridge`: identifies each
  analytic inclusion--exclusion intersection with the literal simultaneous
  forbidden-length event, proves the finite indicator identity assignment by
  assignment, and integrates it.  Consequently the analytic admissible
  resolvent is exactly the unrestricted path sum with all and only the
  non-simple reconstructions removed.
- `PerronWright.Transfer.PositiveHalfIntegerRate`: proves, for every fixed
  positive half-integer singular exponent and in particular
  `3*ell/2`, that the exact binomial coefficient normalized by its Gamma
  main term is `1+O(1/n)`.  The result is derived from the half-power base
  estimate and the exact exponent-raising recurrence, so the leading
  positive-surplus transfer constant is quantitative rather than merely
  asymptotic.
- `PerronWright.Transfer.HalfStepHierarchy`: compares every lower Puiseux
  coefficient with the exact leading `3*ell/2` coefficient and proves the
  uniform half-step loss `O(n^(-j/2))` at vertical degree `j`.  Thus the
  finite singular polynomial is controlled by one theorem, with no separate
  even/odd calculation.
- `PerronWright.Analysis.AnalyticVerticalTaylor`: iterates Banach-valued
  analytic division in the distinguished fold coordinate.  It gives every
  finite vertical Taylor expansion with coefficient functions analytic in
  the field and a jointly analytic remainder, retaining the joint structure
  required for field-uniform Puiseux transfer.
- `PerronWright.Enumeration.CubicSubdivisionConnectivityConverse`: proves the
  reverse connectivity implication without a positivity assumption on the
  surplus.  It collapses every reconstructed internal label to the first
  endpoint of its kernel edge, proves that each reconstructed adjacency maps
  to reachability in the kernel support, and lifts reconstructed paths along
  this collapse.  Thus a connected reconstructed graph has connected
  normalized kernel support; this direction is no longer part of the inverse
  classification gap.
- `PerronWright.Enumeration.ActualCubicLengthProfile`: constructs the
  admissible `CubicKernelLengthProfile` carried by every actual connected
  cubic positive-surplus two-core.  Component edges receive their literal
  number of degree-two vertices and direct branch edges receive length zero.
  The total-length identity follows from `coreCoordinateEquiv`; a loop is
  proved to contain at least two internal vertices using its two distinct
  boundary stubs; and injectivity on zero-length endpoints follows from the
  original graph being simple.  The theorem retains the concrete branch and
  edge relabellings and their endpoint and length identities for the eventual
  inverse construction.
- `PerronWright.Enumeration.ActualCubicSubdivisionForward`: completes the
  forward reconstruction of every actual connected cubic positive-surplus
  core.  It orients each degree-two component compatibly with the normalized
  kernel endpoints, assembles all branch and internal slots into one global
  vertex-label equivalence, and proves by exact edge-finset comparison that
  the resulting subdivision datum reconstructs the original labelled graph.
- `PerronWright.Enumeration.UnicyclicFixedCoreAnalytic`: proves that the
  formal profile-composition series is the genuine Taylor series of the
  analytic finite-graph weight for every fixed core.  The proof constructs
  the finite multilinear vertex product, transports each profile coordinate,
  integrates it through an explicit continuous linear functional, and proves
  the one-variable Cauchy-product coefficient law from iterated derivatives.
  The compulsory `X^q` factor and rooted-tree tail are matched exactly; no
  analytic-composition coefficient identity is assumed.
- `PerronWright.Enumeration.UnicyclicFixedLengthAnalytic`: sums those genuine
  fixed-core Taylor series over the finite type of admissible cycle cores of
  one fixed length `q ≥ 3`, including the exact `q!`⁻¹ labelled-EGF
  normalization.  The already proved cycle multiplicity identity then
  identifies the resulting analytic function with the actual
  `profileSimpleCycleTerm`; no infinite cycle-length sum is used.
- `PerronWright.Enumeration.UnicyclicFiniteLengthSumAnalytic`: sums the
  fixed-length analytic identities over every finite initial range.  Thus the
  actual truncated simple-cycle series has exactly the corresponding finite
  sum of labelled fixed-core composition Taylor series, without an
  interchange of infinite sums.  The remaining passage to the full series
  is isolated to a geometric-tail order estimate at the origin.
- `PerronWright.Enumeration.UnicyclicTailOrder`: proves that geometric-tail
  estimate for the actual infinite simple-cycle sum.  If the rooted profile
  has zero constant coefficient, the terms with cycle length at least
  `N + 3` are `O(‖w‖^(N+3))` at the origin.  The proof derives this directly
  from the genuine operator-cycle majorant and summability, rather than
  assuming an interchange of Taylor expansion and an infinite sum.
- `PerronWright.Enumeration.UnicyclicFullAnalytic`: combines the actual
  termwise derivative formula with uniform subcritical profile and velocity
  bounds on one small disk.  The complete infinite profile simple-cycle
  series is therefore analytic at the origin for every analytic rooted
  profile with zero constant coefficient.
- `PerronWright.Enumeration.UnicyclicCoefficientReindex`: converts the
  antidiagonal core/off-core definition of the genuine unicyclic composition
  coefficient into the finite cycle-length truncation used analytically.
  Core sizes below three vanish by admissibility, and core sizes above the
  requested coefficient vanish by the explicit `X^q` factor.
- `PerronWright.Enumeration.UnicyclicFullTaylor`: combines the finite-cycle
  Taylor identities, the genuine infinite-cycle tail estimate, and full
  analyticity.  It proves that every Taylor coefficient of the actual
  infinite simple-cycle series is exactly the literal unicyclic
  profile-composition coefficient; no exchange of two infinite sums is
  assumed.  Along an actual analytic field-rooted tree branch, a second
  theorem then rewrites those coefficients as the genuine complex-field
  connected unicyclic graph weights divided by the labelled factorial.
- `PerronWright.Enumeration.TreeCoefficientSeries`: assembles all literal
  continuous type-resolved finite rooted-tree coefficients into a genuine
  `C(S, ℝ)`-valued formal power series and proves coefficientwise that its
  type integral is the existing scalar vertex-rooted tree EGF.
- `PerronWright.Enumeration.TreeFormalEquation`: defines the actual kernel
  action coefficientwise on `C(S, ℝ)`-valued power series and the precise
  formal right-hand side `X exp(-d) exp(KT)` using power-series substitution.
  The genuine rooted-tree series has zero constant term after applying the
  kernel, so this substitution is formally admissible; its constant and
  degree-one coefficients are proved to be the required zero and genuine
  single-vertex profile.  The all-size identity is completed in
  `RootedTreeFormalIdentity`.
- `PerronWright.Enumeration.LabelledPartitionExp`: constructs an explicit
  equivalence between a finite labelled partition and its marked block plus
  a partition of the complement, proves the exact marked-block recurrence
  for weighted labelled partitions, and independently proves the matching
  derivative recurrence for coefficients of a substituted formal
  exponential.  A second explicit erase/insert equivalence now groups the
  marked-block sum by cardinality and derives the exact binomial
  multiplicities.  The derivative recurrence is also factorial-normalized
  exactly, yielding the same binomial marked-block recurrence coefficient by
  coefficient.  Strong induction then proves the complete labelled
  exponential formula for an arbitrary zero-constant formal series directly
  from finite set partitions.  This formula is now specialized to the actual
  coefficientwise compact-BJR kernel action on the genuine type-resolved
  rooted-tree series, and its pointwise form after multiplication by the
  genuine root-vertex factor is identified with the next coefficient of the
  formal rooted-tree right-hand side.  The concrete identification and final
  coefficientwise equation are completed in `RootedTreeFormalIdentity`.
- `PerronWright.Transfer.CoefficientCauchy`: Cauchy's exact circle-integral
  formula identifies the integrand used in the developing dented-domain
  contour argument with the Taylor coefficient of a holomorphic function;
  uniqueness of an actual local power series identifies that Taylor
  coefficient with its supplied coefficient sequence. This is specialized
  to the exact algebraic singularities and polynomial prefactors already
  formalized, including exact circle formulas for pure powers and their
  polynomial prefactors at every fixed radius below one.
- `PerronWright.Transfer.LogarithmicCoefficient`: packages the Taylor series
  of `-log(1-z)`, proves as a germ that
  `-(1/2) log(sqrt(1-z)) = -(1/4) log(1-z)` on the principal sheet, and obtains
  the exact coefficient `1/(4n)` (with the zero constant-term convention) for
  the pure unicyclic fold singularity.
- `PerronWright.Transfer.BanachCauchy`: the same exact Cauchy coefficient
  formula for arbitrary complex Banach-valued analytic functions, needed
  for the field-derivative transfer.  Its uniform Cartesian dented-domain
  completion is now proved in `CartesianTransfer`.
- `PerronWright.Transfer.BanachContourBounds`: the actual radial sides,
  small circle, outer arc, and assembled norm bound have been proved for
  arbitrary complex Banach-valued remainders; the outer arc is also proved
  negligible against any algebraic scale.  The later Cartesian modules
  match these bounds to the Taylor coefficient by an explicit deformation.
- `PerronWright.Transfer.BanachRectangle`: Cauchy--Goursat and exact grid
  cancellation for complex Banach-valued rectangular contour integrals.
  These identities are the local building blocks of the completed
  Cartesian mixed-center deformation.
- `PerronWright.Transfer.BanachDeltaCauchy`: the actual Banach-valued
  logarithmic-sector Cauchy--Goursat identity for the transformed
  coefficient integrand, including the denominator-free hypothesis form
  when the outer local radius is below one. Its horizontal and vertical
  sides are identified with genuine radial and angular Cauchy integrands.
  The global mixed-center gluing is completed by `CartesianGlobalContour`.
- `PerronWright.Transfer.BanachCartesianDetour`: replaces the inadmissible
  small circle (which crosses the deleted Cartesian cone) by a three-segment
  U-shaped contour lying entirely inside the proved Cartesian Δ-domain.
  Both truncated 3--4--5 rays and the detour have direct Banach norm bounds,
  and their assembled local keyhole contribution has the required
  `O(n^(-a-1))` scale.  The following Cartesian contour modules identify it
  with the Taylor coefficient and complete the outer deformation.
- `PerronWright.Transfer.BanachCartesianContourIdentity`: thickens each of
  the five admissible local-keyhole segments to an explicit affine rectangle
  inside the Cartesian Δ-domain and applies Banach-valued Cauchy--Goursat
  on all five rectangles.  The resulting fifteen closing sides give an exact
  finite identity between a fixed Taylor circle and the local Cartesian
  keyhole, hence an exact Taylor-coefficient identity, with no contour
  deformation postulated as an interface.  The external closing term is
  subsequently bounded and cancelled in `CartesianTransfer`.
- `PerronWright.Transfer.CartesianOuterArcGeometry`: constructs the fixed
  major circular arc through the two truncated Cartesian rays without
  choosing an argument branch.  Both endpoints are explicit; the entire arc
  lies in the punctured Cartesian Δ-domain, and its modulus is uniformly at
  least `1 + M/2`.
- `PerronWright.Transfer.CartesianOuterArcParam`: fixes the principal endpoint
  angle and parametrizes that entire major arc by one explicit angular
  interval, with the correct lower-to-upper closing orientation.  The
  associated Banach-valued coefficient integral has a proved exponential
  bound and is little-o of every real algebraic scale.
- `PerronWright.Transfer.CartesianGlobalContour`: joins that outer arc to the
  five affine keyhole pieces by six explicit smooth radial homotopies.  The
  angular contributions telescope to the exact orientation-correct identity
  `circle integral + local keyhole + fixed outer arc = 0`, without assuming
  any contour-deformation interface.
- `PerronWright.Transfer.CartesianTransfer`: combines that exact global
  identity with Cauchy's formula and the local/outer estimates.  It proves
  the exact finite-index coefficient identity, derives the fixed outer-arc
  bound from the same Delta-domain power hypothesis, proves the outer
  remainder is little-oh at the natural scale, and obtains the final
  Banach-valued `O(n^(-a-1))` Taylor-coefficient estimate without adding an
  unproved contour or boundary-bound interface.
- `PerronWright.Transfer.BanachAngularIBP`: exact integration by parts
  for a complex Banach-valued periodic function against an angular
  Fourier mode, including its arbitrary finite iteration and the
  derivative-to-coefficient norm bound.
  This is an alternative Fourier tool; the generic Cartesian transfer is
  already complete, while verifying its power-bound hypothesis for each
  graph-specific analytic remainder remains open.
- `PerronWright.Transfer.BanachLocalPowerDerivative`: from a genuine
  holomorphic disc and a boundary power bound, Cauchy's estimate yields
  explicit bounds for all Banach-valued derivatives at the disc center.
  The corresponding containment is available for the Cartesian dent; this
  module is another way to establish the graph-specific remainder bounds
  required by the completed transfer theorem.
- `PerronWright.Transfer.DeltaDecay`: the actual fixed-radius outer arc of
  the developing keyhole contour is proved negligible against every
  algebraic coefficient scale.  The Cartesian implementation now supplies
  the mixed-center deformation and the full uniform Banach transfer bound.
- `PerronWright.Analysis.ScalarFieldResponse`: the first derivative of the
  analytic critical parameter along the paper's scalar field (g_t) vanishes
  at (t=1), by the Perron-weighted cancellation of (1-d).
- `PerronWright.Analysis.ScalarFieldBridge`: the complex scalar field agrees
  with the original real field for positive real (t), and the finite
  connected graph weight satisfies its exact scalar-field identity.
- `PerronWright.Analysis.ScalarFieldTaylor`: holomorphy of the scalar critical
  parameter near (t=1) and its quadratic-order bound, derived from the
  proved zero first derivative; the exact coefficient is proved in
  `ScalarRadiusSecond` below.
- `PerronWright.Analysis.ScalarFieldReal`: on the positive real (t)-slice
  near (1), the same analytic critical parameter is real and strictly
  positive, via the proved conjugation symmetry of the critical pair.
- `PerronWright.Analysis.ScalarFieldSecond`: the exact second derivative of
  the paper's complexified scalar field at (t=1) is the constant function
  `-1`.
- `PerronWright.Analysis.ScalarRadiusSecond`: differentiating the actual
  critical-pair tree and Perron equations twice proves the exact analytic
  critical-parameter curvature `ρ''(1)=α²/β`. The identification of this
  parameter with the least-tree convergence radius is still pending.
- `PerronWright.Analysis.ScalarLogRadiusTaylor`: the actual analytic critical
  parameter satisfies `log ρ(1+y) = (α²/(2β))y² + O(|y|³)` in a complex
  neighborhood of zero; on the nearby real slice this logarithm is the
  ordinary real logarithm of the positive critical parameter. Its
  identification with the least-tree convergence radius remains pending.
- `PerronWright.Analysis.CriticalWindowRadiusConversion`: converts that local
  logarithmic Taylor theorem into the precise uniform critical-window factor.
  For every fixed `L ≥ 0`, eventually in `k` and uniformly under
  `sqrt(k)|t-1| ≤ L`, it proves
  `ρ(t)^(-k)/exp(-α²k(t-1)²/(2β)) = 1 + O_L(k^(-1/2))`, with an
  explicit positive-radius real slice and both relative- and absolute-error
  forms.  Thus the Gaussian conversion is no longer a remaining interface.
- `PerronWright.Analysis.TreeFold`: a genuine jointly analytic local solution
  curve for the actual compact-kernel tree equation, parametrized by the
  Perron coordinate; its critical-point tangent has zero (z)-component and
  Perron profile (u). This does not yet give the square-root chart.
- `PerronWright.Analysis.TreeFoldCurvature`: the actual tree equation along
  that curve has second radius derivative exactly `-β` at the critical point,
  establishing the nondegenerate fold curvature without an assumed formula.
- `PerronWright.Analysis.TreeFoldSquareRoot`: the actual zero-field rooted-tree
  branch has a proved analytic `X=√(1-z)` chart with
  `T(0)=1` and `T'(0)=-√(2/β)·u`, obtained by factorization and local analytic
  inversion, not posited as a singularity hypothesis.
- `PerronWright.Analysis.TreeFoldUniformField`: the genuine centered fold curve
  solves the field-dependent tree equation; the radius component has zero
  first derivative in the fold coordinate for every sufficiently small complex
  field, and consequently admits an analytic quadratic factorization in that
  coordinate for each fixed field. This factorization is **pointwise in the
  field**; `TreeFoldJointDivision` below strengthens it to a jointly analytic
  factor.
- `PerronWright.Analysis.CriticalNoAnalyticBranch`: differentiates the actual
  zero-field tree equation along a hypothetical ordinary-activity analytic
  branch through `(1,1)`.  Perron-functional invariance would force its
  nonzero value on the constant function to vanish, giving a contradiction.
  Thus critical nonanalyticity is proved from the model rather than assumed;
  together with the enumerative radius lower bound, this is the obstruction
  needed for the matching radius upper bound.
- `PerronWright.Analysis.TreeFoldUniformCurvature`: the second derivative in
  the fold coordinate is a holomorphic function of the complex field, equals
  `-β` at zero field, and therefore remains nonzero for all sufficiently
  small complex fields. Consequently every sufficiently small field has a
  nondegenerate analytic quadratic factor in the fold coordinate. This
  controls the leading coefficient.
- `PerronWright.Analysis.TreeFoldJointDivision`: a fully proved Banach-parameter
  analytic division theorem gives a jointly holomorphic quadratic factor for
  the actual centered fold radius, with base value `β/2`. Joint square-root
  inversion is carried out in `TreeFoldJointChart` below.
- `PerronWright.Analysis.AnalyticVerticalDivision`: upgrades the scalar
  division mechanism to arbitrary complex Banach targets.  A jointly analytic
  map minus its restriction to the horizontal slice is proved to be the
  vertical coordinate times a jointly analytic quotient; the vanishing-slice
  specialization is used to freeze the residue in the marked path resolvent.
- `PerronWright.Analysis.MarkedPathResolvent`: constructs the actual analytic
  marked-path operator along the joint fold chart, derives its normalized
  analytic rank-one spectral data from the already-proved Perron eigenpair,
  and splits the inverse path operator into an explicit simple pole and an
  analytic complementary part.  Kernelization is proved from the continuous
  columns of the original compact kernel.  The resulting fixed residue is
  exactly `u(x)u(y)/sqrt(2*beta)`, and the remainder is jointly analytic; no
  abstract resolvent or kernel-representation interface is assumed.  Its
  joint profile is now definitionally the same canonical physical fold
  profile used by `NormalizedFoldActivity`, so the local resolvent expansion
  and the global normalized Delta continuation no longer depend on two
  unrelated `Classical.choose` witnesses.
- `PerronWright.Analysis.MarkedPathResidue`: differentiates the genuine
  analytic eigenpair and uses kernel symmetry to cancel the eigenvector
  derivative.  It proves the exact diagonal pairing of the pole residue with
  the vertical tree-profile derivative is `-1`, the normalization that yields
  the unicyclic singular coefficient `-1/2`; no eigenvalue-derivative formula
  is assumed as an interface.
- `PerronWright.Analysis.AnalyticVerticalPrimitive`: constructs, coefficient
  by coefficient, a jointly analytic primitive in one distinguished complex
  coordinate for any Banach-valued analytic germ.  The primitive vanishes on
  the horizontal slice and its vertical Fréchet derivative recovers the
  original germ.  Radius control and the powerset coefficient regrouping are
  proved internally; no parameter-dependent primitive theorem is assumed.
- `PerronWright.Analysis.MarkedCycleSingularity`: pairs the genuine raw
  marked-path kernel with the vertical tree-profile velocity.  The exact
  residue theorem gives the scalar pole `-1/X`; analytic vertical division
  absorbs the moving residue into a jointly analytic remainder, and the
  coefficientwise primitive supplies its normalized analytic antiderivative.
  The raw Neumann expansion still contains the finite path-length-one and
  path-length-two analytic corrections; their removal is deliberately left
  to the direct simple-cycle bridge rather than hidden in this module.  No
  determinant or logarithm interface is assumed.
- `PerronWright.Analysis.SimpleCycleResolventBridge`: differentiates the
  literal fixed-kernel simple-cycle trace series term by term and proves that
  it is one half of the raw resolvent trace after removing both the
  length-one loop term and the length-two double-edge term.  The same two
  finite corrections are then constructed as genuine jointly analytic
  functions on the compact-BJR fold chart.  Consequently the candidate
  simple-cycle continuation has exact pole `-1/(2X)` plus an analytic
  remainder and a normalized analytic regular primitive.  The module does
  not yet assert equality with a joint field-dependent complex cycle EGF.
- `PerronWright.Enumeration.JointSimpleCycleEGF`: defines the direct complex
  profile simple-cycle series, proves finite cyclicity, strict-subcritical
  normal convergence and termwise differentiation, and identifies its
  derivative along the actual joint tree profile with the resolvent
  continuation.  The separate combinatorial attachment-to-profile identity
  is supplied by `UnicyclicCycleWeightTrace`.
- `PerronWright.Enumeration.ProfileSimpleCycleFrechet`: upgrades the scalar
  directional calculation to the actual Fréchet derivative on the profile
  Banach space.  A geometric operator-norm majorant normally sums the
  finite-cycle derivatives, identifies the resulting continuous linear map
  with the concrete resolvent formula, and proves that the full profile
  simple-cycle series is complex Fréchet differentiable on the open unit
  profile ball.  This is holomorphy in the Banach-calculus sense.  The module
  does not silently infer mathlib's power-series predicate `AnalyticOnNhd`
  from general Banach-domain differentiability.  It also proves directly that
  restriction along any scalar analytic profile curve that is strictly
  subcritical at the base point is analytic there in mathlib's power-series
  sense.
- `PerronWright.Enumeration.ProfileSimpleCyclePowerSeries`: supplies the
  missing Banach-domain power-series argument without an assumed analytic
  interface.  The degree-`n+3` coefficient is an explicit continuous
  multilinear cycle functional whose diagonal is exactly the existing
  length-`n+3` simple-cycle term.  A mixed-profile Perron-gauge estimate gives
  a uniform coefficient bound and radius at least one.  The resulting formal
  multilinear series sums to `profileSimpleCycleSeries` on the open unit
  profile ball, yielding an actual `HasFPowerSeriesOnBall` theorem at the
  origin and `AnalyticOnNhd` throughout that ball.
- `PerronWright.Enumeration.SimpleCyclePhysicalRayBridge`: places that direct
  power series on the genuine zero-field physical fold ray.  For all
  sufficiently small real `X > 0`, the canonical fold profile is proved equal
  to the rooted-tree series at `1-X²`, has norm strictly below one, and hence
  lies in the analytic profile-series ball.  The explicit multilinear series
  sums to the direct simple-cycle series there, and its complex `X`-derivative
  is exactly the independently constructed marked-resolvent continuation.
  This identifies the singular derivative without assumptions.  It does not
  yet pin the additive constant in a logarithmic primitive: that requires a
  chosen logarithm on a punctured sheet together with a direct-series value or
  normalized limit at one comparison point.
- `PerronWright.Enumeration.SimpleCycleRayPrimitive`: integrates the proved
  physical-ray derivative identity.  On a short positive real fold ray the
  genuine direct simple-cycle series is exactly `-(1/2) log X` plus the
  jointly analytic regular primitive and a constant.  The constant is
  constructed from the zero-derivative theorem on the connected interval;
  it is not supplied as an interface.  This renormalized positive-ray
  constant is exactly the paper's `H₁`; no closed-form numerical evaluation
  is needed for the singular expansion.
- `PerronWright.Enumeration.SimpleCycleLogContinuation`: packages the same
  primitive as an analytic function on the punctured local slit disk.  Its
  derivative is the exact resolvent continuation, and its restriction to the
  positive physical ray is the genuine direct simple-cycle series; no claim
  that the direct series converges on the whole complex continuation domain
  is introduced.
- `PerronWright.Enumeration.ZeroFieldUnicyclicSingularity`: identifies the
  continuation with the genuine zero-field unicyclic EGF on the positive
  physical ray and isolates the paper's constant `H₁`.  It proves the exact
  form `-(1/2) log X + H₁ + R(X)` with `R` analytic, `R(0)=0`, and
  `R(X)=O(X)`, while retaining the slit-disk analytic continuation and its
  resolvent derivative.
- `PerronWright.Enumeration.ZeroFieldUnicyclicActivitySingularity`: transports
  that singular expansion from the fold coordinate `X` to the normalized
  activity `w = 1-X²` on a local Cartesian-Delta domain.  It constructs the
  analytic regular term and continuation, proves the exact decomposition
  `F(w)=-(1/4) log(1-w)+E(w)+H₁`, the bound
  `E(w)=O((1-w)^(1/2))`, and agreement with the genuine zero-field unicyclic
  EGF on the positive physical ray.
- `PerronWright.Enumeration.ZeroFieldUnicyclicDeltaContinuation`: upgrades
  physical-ray agreement to equality on the full complex overlap by the
  identity theorem, builds the closed-unit-disk-away chart from the genuine
  profile series, and glues the two charts.  The resulting analytic function
  is defined on a complete Cartesian-Delta domain, equals the genuine
  zero-field unicyclic EGF throughout the open unit disk, and retains the
  exact logarithmic expansion and square-root-order local remainder.
- `PerronWright.Enumeration.ZeroFieldUnicyclicCoefficientAsymptotic`: upgrades
  the local germ bound to a uniform square-root power bound on a smaller full
  Cartesian-Delta domain and applies the proved transfer theorem.  It closes
  the zero-field unicyclic coefficient asymptotic in the explicit form
  `[w^n]G(w) = 1/(4n) + O(n^(-3/2))`, with the genuine EGF identified on the
  whole unit disk and no analytic-continuation hypothesis left as an
  interface.
- `PerronWright.Enumeration.ZeroFieldUnicyclicConnectedWeight`: closes the
  final enumerative identification behind that analytic estimate.  It proves
  that the Taylor coefficient of the genuine zero-field unicyclic EGF is
  exactly `complexFieldConnectedWeight 0 n 1 / n!`, then transports the
  `1/(4n) + O(n^(-3/2))` estimate directly to the literal connected-graph
  weights rather than leaving it as a statement about an auxiliary analytic
  function.
- `PerronWright.Enumeration.ZeroFieldTreeLocalSingularity`: starts the
  surplus-zero case directly in the fold coordinate.  It proves that the
  scalar vertex-rooted fold profile has value `1` and derivative `-γ` at the
  critical point, derives the exact differential germ
  `-2X + 2γX² + X³Q(X)`, and constructs a normalized analytic primitive
  without assuming one.
- `PerronWright.Enumeration.ZeroFieldTreeIntegratedSingularity`: integrates
  that differential germ without introducing Taylor data as an interface.
  Analytic order proves the normalized primitive has the exact local form
  `-X² + (2γ/3)X³ + X⁴R(X)` with analytic `R`.  Matching the one remaining
  additive constant to the genuine unrooted-tree Taylor series is supplied
  by the next module.
- `PerronWright.Enumeration.ZeroFieldTreeEGFMatching`: constructs the genuine
  analytic unrooted-tree sum directly from the literal coefficients of
  `treeEGF 0`, proves convergence on the open unit disk, and upgrades the
  formal rooted/unrooted derivative identity to the analytic sums there.
  Matching on the positive physical fold ray then gives the actual EGF the
  expansion `C-X²+(2γ/3)X³+X⁴R(X)`.
- `PerronWright.Enumeration.ZeroFieldTreeDeltaContinuation`: promotes that
  physical-ray identity by analytic uniqueness to the genuine complex lens.
  It constructs a local Cartesian-Delta continuation in the normalized
  activity coordinate and proves there the transfer-ready identity
  `C-(1-w)+(2γ/3)sqrt(1-w)³+(1-w)²E(w)`, with analytic `E`.
- `PerronWright.Enumeration.ZeroFieldTreeGlobalContinuation`: applies the
  exact dissymmetry functional to the unconditional normalized rooted profile,
  proves its derivative from the genuine fixed-point equation, and identifies
  it with the literal unrooted-tree EGF on the unit disk.  This gives a full
  Cartesian-Delta continuation.  On its local fold chart the continuation has
  the exact cubic expansion
  `C-(1-w)+(2γ/3)X³+(1-w)²R(X)`, where `X=sqrt(1-w)` and the genuine
  fold-coordinate remainder `R` is analytic at zero; no global remainder
  bound is postulated.
- `PerronWright.Enumeration.ZeroFieldTreeCoefficientAsymptotic`: derives the
  global `O(|1-w|²)` remainder estimate from that local analytic remainder and
  compactness away from the singularity.  Cartesian transfer gives an
  `O(n⁻³)` error for the literal tree EGF, hence a little-oh error on the
  `n^(-5/2)` scale, while the cubic fold term has Wright's constant
  `γ/(2√π)`.
- `PerronWright.Enumeration.ZeroFieldTreeConnectedWeightAsymptotic`: proves
  that these Taylor coefficients are literally the finite connected-tree
  weights divided by `n!`, then combines the quantitative half-integer
  coefficient estimate with quantitative Stirling.  The result is the actual
  zero-field Perron--Wright formula with main term
  `(γ/√2) n⁻² (n/e)^n` and relative error `O(n^(-1/2))`; since
  `γ/√2=β^(-1/2)`, this is precisely the `r=0` constant in the paper.
- `PerronWright.Enumeration.ScalarFieldRootedTreeRadius`: defines the formal
  multilinear series of the literal field-weighted rooted-tree coefficients
  and proves that the terminal normalized Cartesian-Delta profile has exactly
  this Taylor series after rescaling activity by the analytic critical radius.
  Its auxiliary square-root obstruction derives (rather than assumes) the
  sharp upper bound on a Taylor radius from a nonzero fold derivative.  On one
  complex field ball the normalized series therefore has radius exactly one,
  and the genuine unnormalized series has radius exactly
  `‖RadiusResponse.radius M hM g‖ₑ`; the scalar activity change is handled by
  an independently proved exact radius-scaling identity.
- `PerronWright.Enumeration.FieldTreeGlobalDissymmetry`: applies the genuine
  tree dissymmetry functional to the jointly analytic normalized rooted
  profile.  On one Cartesian-Delta × field-ball product it proves joint
  analyticity, the actual residual equation, and
  `∂_w G(w,g)=(∫Theta(w,g)dμ)/w`; the zero-field slice is the literal tree EGF.
- `PerronWright.Enumeration.FieldTreeEGFMatching`: defines the literal complex
  field tree EGF and its critical-radius normalization.  A finite-dimensional
  Fubini argument proves the rooted-profile coefficient identity, yielding
  `rooted = X·derivative(unrooted)` and finally a genuine fixed-field Taylor
  series theorem for the same global `G`; no coefficient bridge is assumed.
- `PerronWright.Enumeration.FieldTreeJointFoldExpansion`: applies the genuine
  dissymmetry functional to the joint field/fold profile.  The rooting
  derivative proves that the linear fold term vanishes, analytic vertical
  division gives a joint expansion
  `C(g)+A2(g)X^2+A3(g)X^3+X^4 R(g,X)`, and comparison with the proved
  zero-field primitive identifies `A2(0)=-1` and `A3(0)=2*gamma/3`.  The
  statement is kept on the chosen square-root sheet and introduces no
  global square-root identity.
- `PerronWright.Enumeration.FieldTreeDeltaRemainder`: identifies that local
  joint fold germ with the same global Cartesian-Delta continuation whose
  Taylor series is the literal normalized field-tree EGF.  On a smaller
  positive-opening Delta-domain it obtains a uniform remainder bound
  `B*|w-1|^2` on one common complex field ball.  The away estimate uses
  compactness only of the zero-field spine and then an open thickening; no
  compactness of the infinite-dimensional field ball is assumed.
- `PerronWright.Enumeration.FieldTreeUniformCoefficientAsymptotic`: applies
  the family-uniform Cartesian transfer theorem with the field ball merely as
  an index type.  It chooses one field radius and common constants `K,N`
  before all fields, and bounds the literal normalized tree coefficient minus
  `A3(g)[w^n](1-w)^(3/2)` by `K*n^(-3)`, with
  `A3(0)=2*gamma/3`.
- `PerronWright.Enumeration.FieldTreeConnectedWeightAsymptotic`: proves the
  exact identity between that normalized coefficient and the literal complex
  field connected-tree weight.  Differentiability of `A3` at zero, the
  explicit half-integer coefficient estimate, and quantitative Stirling then
  give one relative `O(n^(-1/2))` bound throughout every fixed shrinking
  field window, with the Perron--Wright constant simplified to
  `beta^(-1/2)`.  It also keeps the two perturbation scales separate on one
  fixed complex neighbourhood, proving the stronger local error
  `O(‖g‖+n^(-1/2))`; this is the interface needed for arbitrary windows
  tending to the critical point.
- `PerronWright.Enumeration.TreePerronWrightFormula`: specializes the joint
  complex-field estimate to the physical scalar deformation and the literal
  finite-graph quantity `CompactBJRModel.connectedWeight t k 0`.  It identifies
  the analytic critical activity with the genuine rooted-tree FMS radius,
  proves its cubic logarithmic expansion, and obtains the tree
  Perron--Wright formula uniformly on every fixed critical window
  `|t-1| <= L*k^(-1/2)`, with one common relative `O(k^(-1/2))` constant.
  Its radius form now also covers every prescribed nonnegative sequence
  `eta(k) → 0`, uniformly for `|t-1| <= eta(k)`, with the paper's separated
  relative error `O(eta(k)+k^(-1/2))`.
- `PerronWright.Enumeration.FieldUnicyclicLocalBridge`: defines the literal
  complex-field unicyclic EGF and its normalization by the genuine critical
  activity.  It proves the exact coefficient identity with
  `complexFieldConnectedWeight g n 1`, identifies that literal Taylor germ
  with the direct simple-cycle chart of the global tree profile, and derives
  the normalized local logarithmic fold primitive without presupposing a
  global determinant or continuation.
- `PerronWright.Enumeration.FieldUnicyclicGlobalContinuation`: constructs the
  genuine joint Cartesian-Delta continuation of that literal germ without a
  Fredholm determinant.  It thickens only the compact zero-field spine,
  fixes the local primitive's field-dependent additive constant at the common
  real overlap anchor, proves equality with the direct cycle chart on every
  overlap component from equality of derivatives, and glues the two charts.
  The result preserves the literal FMS Taylor series on one common complex
  field ball and never treats that infinite-dimensional ball as compact.
- `PerronWright.Enumeration.FieldUnicyclicCoefficientAsymptotic`: applies the
  family-uniform Cartesian transfer theorem to the genuine joint unicyclic
  continuation.  It obtains one pair of constants and one threshold before
  the field parameter, proves the uniform expansion
  `1/(4n) + O(n^(-3/2))`, and transports it through the exact Taylor bridge
  to the literal quantity `complexFieldConnectedWeight g n 1`.
- `PerronWright.Enumeration.UnicyclicPerronWrightFormula`: converts the
  normalized unicyclic coefficient to the literal labelled weight and the
  exact Wright constant `sqrt(2*pi)/4`.  Besides the square-root-window
  radius and Gaussian formulas, its local form is uniform on one fixed
  complex field neighbourhood: because the logarithmic leading coefficient
  is field-independent, the relative error remains `O(n^(-1/2))` there.
  Consequently its genuine-radius formula also holds on every nonnegative
  shrinking window `eta(k) → 0`, in particular with the uniform bound
  `O(eta(k)+k^(-1/2))` used in the full theorem.
- `PerronWright.Transfer.QuantitativeStirling`: proves the effective
  factorial normalization needed to return from EGF coefficients to labelled
  weights.  It obtains the logarithmic remainder in `[0,1/(12n)]`, the
  explicit relative bound
  `|n!/(sqrt(2πn)(n/e)^n)-1| ≤ 1/(6n)`, and hence relative `O(1/n)`;
  no quantitative Stirling estimate is left as an external interface.
- `PerronWright.Analysis.TreeFoldJointChart`: from the actual centered fold
  radius, an analytic square root and Banach-space local inverse construct
  the joint field/`X` profile solving the exact tree equation at
  `z = ρ(g)(1-X²)`. The base profile and its derivative
  `-√(2/β)u` are proved, not posited; the later field-tree continuation
  modules globalize this chart to the required Cartesian-Delta product.
- `PerronWright.Analysis.TreeFoldPhysicalGluing`: proves a bilateral local
  inverse for the joint fold coordinate, identifies its overlap with the
  actual centered fold curve, and selects the same joint chart on the
  positive real zero-field physical least branch near the critical point.
  Full dented-domain continuation is supplied by the later normalized-profile
  gluing and field-tree Delta modules.
- `PerronWright.Analysis.AnalyticFiniteAmplitude`: isolates the finite
  analytic algebra used after a kernel contribution has been written as an
  analytic amplitude times its explicit pole.  Finite products remain
  analytic, and any edge count `e < 3*ell` leaves an exact additional factor
  `X` after normalization to the cubic pole order.  The module does not
  assume that graph contributions already possess this representation.
- `PerronWright.Analysis.TreeOuterNeumann`: Perron domination gives a
  geometric bound on the actual complex weighted kernel action, a convergent
  Neumann series, and invertibility of the implicit derivative at every
  strictly subcritical real physical tree fixed point. Complex continuation
  from these points onto the full dented domain is still open.
- `PerronWright.Analysis.RootedTreeUnitCircleGerm`: extends the literal
  closed-disk tree sum locally across every noncritical point of the unit
  circle.  Radial continuity first proves the boundary tree equation; the
  strict unit-circle norm margin and the proved Neumann inverse then give a
  jointly analytic, locally unique `(z,g)` germ, which is proved to agree
  with the actual labelled-tree series on the interior side.
- `PerronWright.Analysis.RootedTreeClosedDiskPartial`: strengthens the
  noncritical invertibility input from the unit circle to the entire closed
  unit disk.  Positivity of the genuine rooted-tree coefficients gives the
  interior estimate `‖T(z,x)‖ ≤ ‖z‖`; together with the already proved strict
  boundary margin this yields `‖T(z)‖ < 1` whenever `‖z‖ ≤ 1` and `z ≠ 1`.
  The actual residual equation and the weighted Neumann theorem then prove
  that its derivative in the unknown profile is invertible at every such
  point, without postulating a closed-disk implicit-function interface.
- `PerronWright.Analysis.RootedTreeClosedDiskGerm`: applies the proved
  Banach analytic implicit-function theorem at every noncritical point of the
  closed unit disk and shrinks the result to one explicit joint activity/field
  product box.  The box simultaneously retains analyticity, the actual tree
  residual, equality with the literal rooted-tree series on its open-disk
  zero-field slice, and local residual uniqueness along the full zero-field
  spine.  These are derived from the closed-disk derivative theorem rather
  than supplied as an atlas interface.
- `PerronWright.Analysis.RootedTreeClosedDiskJointAtlas`: applies compactness
  to those pointwise germs on any compact subset of the closed unit disk
  avoiding `1`.  A finite subcover supplies one common field radius.  A
  convex-geometric argument moves every intersecting pair of half-radius
  charts to a common open-disk seed, so the proved joint uniqueness theorem
  gives equality on their full product overlap.  Thus the finite compatible
  atlas is derived without a unit-circle-only hypothesis.
- `PerronWright.Analysis.RootedTreeClosedDiskGlobal`: glues that finite atlas
  on the union of its half-radius activity balls.  It produces one open
  neighborhood of the prescribed compact closed-disk set, one uniform complex
  field ball, and one jointly analytic tree profile satisfying the genuine
  residual.  The profile equals the literal rooted-tree series on the
  open-disk zero-field slice and retains local residual uniqueness along its
  full zero-field spine.
- `PerronWright.Analysis.AnalyticCoeffOrder`: proves the generic analytic
  coefficient principle used at the infinite-cycle limit: if an analytic
  Banach-valued germ is `O(‖z‖^N)`, then all Taylor coefficients of degree
  below `N` vanish.
- `PerronWright.Analysis.RootedTreeUnitGermBall`: extracts an explicit
  positive-radius ball from each noncritical unit-circle germ.  On that ball
  the zero-field slice is analytic, solves the exact tree equation, and
  agrees with the literal series wherever the ball meets the open unit disk.
  An analytic identity-principle theorem proves compatibility of any two
  such germs on a connected ball overlap meeting the disk.
- `PerronWright.Analysis.RootedTreeUnitFiniteCover`: upgrades the pointwise
  boundary germs to a finite compatible atlas on every compact subset of the
  unit circle avoiding `1`, then glues that atlas to one analytic zero-field
  tree continuation on an open neighborhood.  The glued continuation solves
  the exact tree residual and equals the literal rooted-tree series on the
  interior side.  A cutoff formulation covers the full unit-circle arc
  `delta <= dist z 1`, which is the outer interface needed by a later dented
  domain construction.
- `PerronWright.Analysis.RootedTreeUnitJointField`: retains the full complex
  field parameter in the finite unit-circle atlas.  Local implicit
  uniqueness first produces genuine joint equality near an interior seed;
  Banach-space analytic uniqueness then propagates it across each convex
  product overlap.  Finite minimization supplies one positive field radius,
  and the compatible charts glue to one jointly analytic tree solution on
  `U × B(0,ε)` for every compact unit-circle set avoiding the critical
  point.  The glued profile also retains the original implicit-function
  residual uniqueness at every point of its full zero-field spine.  Thus the
  joint overlap is not inferred merely from its zero-field slice.
- `PerronWright.Analysis.TreeJointOverlapUniqueness`: proves the precise
  uniqueness mechanism needed to glue the unit-away continuation to a fold
  chart.  Two jointly analytic solutions of the genuine tree residual on an
  open preconnected overlap agree everywhere once both meet the literal
  rooted-tree series at one real subcritical interior point.  Implicit-function
  uniqueness first gives equality on a genuinely open joint neighborhood,
  after which Banach-space analytic continuation propagates it across the
  overlap.  A second theorem now starts at an arbitrary complex seed: equality
  at that seed plus the proved local residual uniqueness of one profile gives
  the same propagation.  The module does not assume the geometry guaranteeing
  that the fold and unit-away domains overlap.
- `PerronWright.Analysis.TreeSubcriticalAnalytic`: every real strictly
  subcritical physical tree fixed point has a jointly analytic local
  `(z,g)` solution with local uniqueness. The existence statement follows
  from the proved monotone iteration without an extra branch assumption;
  uniform continuation around the unit circle remains open.
- `PerronWright.Analysis.TreeMonotone`: the literal normalized zero-field
  tree map and its monotone iteration from zero, bounded by one and by every
  nonnegative fixed point.
- `PerronWright.Analysis.TreeContraction`: for every `0 ≤ w < 1`, a
  Perron-weighted geometric increment bound proves uniform convergence of
  that iteration to the least nonnegative fixed point in `C(S, ℝ)`. The
  correspondence with the rooted-tree power series remains open.
- `PerronWright.Analysis.TreeRealComplexBridge`: the real normalized tree map
  is exactly the real slice of `TreeCritical.residual`; a real fixed point is
  therefore a zero of the complex residual. For sufficiently small
  nonnegative `w`, the least fixed point from monotone iteration agrees with
  the analytic zero-tree branch. This is a local identity only: it does not
  yet identify the full interval of real tree values, the rooted-tree
  coefficients, or the actual convergence radius.
- `PerronWright.Analysis.TreeEndpoint`: the normalized zero-field tree
  equation at `w = 1` has the unique real continuous solution `V = 1`, by
  a strict exponential inequality and Perron-weighted integration.
- `PerronWright.Analysis.TreeEndpointConvergence`: compactness of the kernel
  action, the just-proved endpoint uniqueness, and Dini's theorem show that
  the monotone zero-field tree iteration converges uniformly to `1` at
  `w = 1`.  The later `RootedTreeSeriesPhysical` module identifies this
  iteration with the literal finite rooted-tree generating series throughout
  the real subcritical interval.
- `PerronWright.Analysis.TreePhysicalBranch`: for real `0 ≤ w < 1` sufficiently
  near `1`, the actual least fixed point from tree iteration agrees with a
  proved analytic square-root chart evaluated at `√(1-w)`. The proof combines
  endpoint convergence, local uniqueness of the fold curve, and the sign of
  the physical Perron coordinate to select the positive square-root branch.
  The later enumerative modules match this branch with the literal finite
  rooted-tree coefficients and prove that their actual convergence radius is
  exactly one.
- `PerronWright.Transfer.Base`: the complex analytic expansion of the pure
  power singularity `(1-z)^(-s)`, its exact Gamma coefficient formula for
  real `s > 0`, and the leading asymptotic `n^(s-1)/Gamma(s)`, including
  the explicit half-power constant `1/sqrt(pi*n)`; this does not yet include
  general dented-domain remainder transfer or uniform error rates.
- `PerronWright.Transfer.NegativeHalf`: exact coefficient relations and
  fully proved asymptotic equivalents for `(1-z)^(1/2)` and
  `(1-z)^(3/2)`, with constants `-1/(2√π)` and `3/(4√π)` respectively.
- `PerronWright.Transfer.Polynomial`: exact finite-convolution coefficients
  for real polynomial prefactors `P(z) * (1-z)^(-s)`, and the normalized limit
  `P(1)/Gamma(s)` for every real `s > 0`, giving the leading asymptotic
  when `P(1) != 0`.
- `PerronWright.Transfer.NegativeHalfPolynomial`: the normalized shift and
  finite-convolution theorem for any exponent with a proved nonzero
  coefficient limit, specialized to polynomial prefactors of
  `(1-z)^(1/2)` and `(1-z)^(3/2)` with exact leading constants.
- `PerronWright.Transfer.HalfCoefficientRate`: a Gamma log-convexity proof
  gives the explicit relative bound `|sqrt(pi*n)·[z^n](1-z)^(-1/2)-1| ≤ 1/n`
  for `n ≥ 2`, upgrading the leading equivalence to a quantitative rate.
- `PerronWright.Transfer.NegativeHalfRate`: exact algebraic coefficient
  relations propagate this quantitative relative `O(1/n)` bound to the
  `(1-z)^(1/2)` and `(1-z)^(3/2)` terms.
- `PerronWright.Transfer.ShiftGeneral`: the fixed-shift ratio has relative
  `O(1/n)` error whenever the generalized binomial coefficients have no
  zero; in particular this covers both positive half-integer powers.
- `PerronWright.Transfer.PrefactorShiftRate`: for any fixed polynomial
  prefactor, its exact coefficient divided by the corresponding pure-power
  coefficient differs from `P(1)` by `O(1/n)`, including the two positive
  half-integer powers.
- `PerronWright.Transfer.PrefactorRate`: combining the pure-power and
  fixed-shift rates proves normalized `O(1/n)` coefficient error for every
  fixed polynomial prefactor of the three half-integer powers.
- `PerronWright.Transfer.ShiftError`: an exact fixed-shift coefficient ratio,
  its first-order limit, and the resulting `1 + O(1/n)` shift error for every
  fixed positive real exponent and fixed shift.
- `PerronWright.Transfer.KeyholeBounds`: the precise Gamma/Laplace bounds
  for keyhole radial sides and the small-circle contour bound at radius `1/n`.
  These are contour estimates, not yet a complete dented-domain transfer theorem.
- `PerronWright.Transfer.DeltaGeometry`: explicit keyhole-ray geometry and
  exponential Cauchy-denominator bounds for rays and a common outer circle;
  the fixed rays are also proved to lie in a Cartesian dent of slope below
  `4/3` while they remain within the radial margin;
  contour deformation and assembly remain outstanding.
- `PerronWright.Transfer.DeltaDiscGeometry`: a proved proportional-disc
  separation estimate between unit-disc centers and a Cartesian excluded
  cone, including closed Cauchy discs inside the resulting Δ-domain.
- `PerronWright.Transfer.CartesianDeltaSqrt`: proves directly from the
  Cartesian dent that `1-w` lies in the principal complex slit plane and
  therefore defines the canonical analytic coordinate
  `X(w)=sqrt(1-w)` throughout that normalized `w`-domain. Its square is
  exactly `1-w` and it is nonzero on the dented domain. This constructs the
  selected square-root sheet without a branch hypothesis. Its composition
  with the field-dependent critical activity is carried out in
  `NormalizedFoldActivity`.  The zero-field fold profile is now identified
  with the actual rooted-tree series on a genuine complex lens; the resulting
  joint-field overlap and gluing with the unit-away continuation are carried
  out in `NormalizedOverlapGluing`.
- `PerronWright.Transfer.CartesianDeltaSqrtPower`: identifies every natural
  power of the canonical fold coordinate with the corresponding principal
  half-integer power of `1-w`, and its inverse with the matching negative
  half-step singularity.  Later Puiseux transfer can therefore treat all
  vertical Taylor degrees uniformly, without a parity split or a branch
  assumption.
- `PerronWright.Analysis.NormalizedFoldActivity`: constructs the genuine
  analytic base change `(w,g) ↦ (ρ(g)w,g)` from the proved critical radius
  and composes the joint fold chart with the canonical Cartesian-Delta
  coordinate `sqrt(1-w)`. On one explicit open product, a single positive
  radius simultaneously controls the activity map and the fold profile,
  keeps `ρ(g)` nonzero, and proves the exact field-dependent tree equation at
  activity `ρ(g)w`. No square-root sheet or residual equation is assumed as
  an interface.  The physical real near-critical identity is promoted by the
  analytic identity theorem to equality of the zero-field normalized fold
  profile and the actual rooted-tree series on the convex complex lens
  `ball(0,1) ∩ ball(1,r²)`.
- `PerronWright.Analysis.NormalizedUnitAway`: pulls the genuine joint
  unit-away continuation back through `(w,g) ↦ (ρ(g)w,g)`. The exact pullback
  is open, its normalized profile is jointly analytic and solves the actual
  tree residual, and its zero-field interior slice remains the literal
  rooted-tree series.  Local residual uniqueness is transported through the
  normalized activity map using continuity alone, without assuming a local
  inverse.  Compactness of each unit-circle arc away from `1`
  supplies one positive annular thickness and one field radius whose product
  lies in this pullback, without imposing any geometric shape on the original
  continuation neighborhood.
- `PerronWright.Analysis.NormalizedOverlapGluing`: constructs, rather than
  assumes, a genuine overlap between the normalized fold and unit-away
  continuations.  It chooses a nontrivial unit-circle point
  `ζ = exp(iθ)` arbitrarily close to `1`, moves it a controlled radial
  distance into the open unit disc, and proves that the resulting complex
  seed lies simultaneously in the fold lens and the uniform unit-away
  thickening.  Openness then yields a nonempty open preconnected product
  `ball(w₀,s) × ball(0,s)` contained in both domains.  Equality with the
  rooted-tree series at the complex zero-field seed, local residual
  uniqueness, and analytic continuation prove that the two joint profiles
  agree throughout this product.  No overlap geometry or branch equality is
  assumed as an interface.
- `PerronWright.Analysis.AnalyticTwoChartGluing`: isolates the exact
  sheaf-style step needed after the full overlap has been established.  Two
  analytic maps agreeing on the intersection of two open charts are glued by
  a literal piecewise definition, with proved equality on each chart;
  pointwise residual equations are inherited on the union.  This module adds
  no compactness, connectedness, or continuation hypothesis of its own.
- `PerronWright.Analysis.NormalizedClosedDiskFoldGluing`: constructs the
  normalized continuation on a neighborhood of the compact part of the
  closed unit disk kept away from `1`.  For explicitly nested fold radii, it
  proves the relative overlap geometry actually needed downstream: every
  connected component of the smaller fold/thickening overlap meets the
  zero-field lens inside the larger overlap.  It makes no false or stronger
  claim that the raw maximal overlap is connected.  A second, sharper form
  proves that every such component contains the same real anchor `1-delta`;
  this fixes field-dependent additive constants in later scalar primitives
  without any compactness assumption on the field ball.
- `PerronWright.Analysis.NormalizedClosedDiskFoldTerminal`: combines that
  relative component theorem, analytic uniqueness, and two-chart gluing.
  It produces an unconditional jointly analytic normalized tree profile on
  the union of an explicitly shrunken fold product and an explicitly
  shrunken closed-disk-away product, agrees with the genuine profile on each
  chart, and satisfies the actual tree residual throughout.  The strict
  radius margin used for continuation is part of the proved conclusion; no
  overlap or gluing interface is postulated.
- `PerronWright.Analysis.NormalizedDeltaProfile`: extracts unconditionally
  from the terminal two-chart gluing one uniform Cartesian-Delta product
  `cartesianDelta eta 0 × ball 0 s`.  On this product the activity map and
  normalized profile are jointly analytic, the critical radius is nonzero,
  and the actual tree residual vanishes.  The resulting profile retains its
  `EqOn` identification with the normalized fold profile on the full local
  fold product needed for subsequent singular expansions.  Analytic
  uniqueness also identifies its zero-field slice with the literal
  rooted-tree series throughout the whole open unit disk.
- `PerronWright.Transfer.BanachDeltaLocalDerivative`: combines that genuine
  disc containment with Banach-valued Cauchy estimates to bound arbitrary
  derivatives of a power-bounded holomorphic remainder near `1`. Relating
  the Cartesian cone to the paper's argument-defined Δ-domain and applying
  the estimate to the actual generating remainder remain open.
- `PerronWright.Transfer.DeltaContour`: actual integrals along the keyhole's
  radial, inner-circle, and outer-arc pieces, each with a quantitative norm
  bound, and their sum bound. The radial estimate now follows directly from
  a power bound on the Cartesian Δ-domain and proved ray inclusion. The
  Cauchy deformation identity remains open.
- `PerronWright.Transfer.DeltaCauchy`: Cauchy--Goursat on a logarithmic
  sector around `z=1`, proving the genuine four-boundary identity there.
  Matching this local sector to the mixed-center coefficient contour remains
  open; no full Δ-transfer identity is claimed.
- `PerronWright.Transfer.DeltaMixedContour`: the exact rectangular
  Cauchy--Goursat identity and cancellation of internal edges across a finite
  rectangular grid, a proved subdivision tool for the remaining mixed-center
  keyhole deformation.
- `PerronWright.Transfer.DeltaSideParam`: exact identification of logarithmic
  rectangle edges with the radial and `z=1`-centered circular path integrands.
- `PerronWright.Transfer.UniformCartesianTransfer`: upgrades the scalar or
  Banach-valued Cartesian transfer estimate to an arbitrary family with one
  common power bound.  Its conclusion chooses `K` and the eventual threshold
  before the family index, deriving both from the exact contour identity and
  explicit local-keyhole/outer-arc bounds; the index type has no compactness
  assumption.

The final umbrella build and `Audit.lean` are run after every terminal-chain
change.  Lean's `#print axioms` for the compact Perron--Wright theorem and its
analytic, combinatorial, and transfer dependencies reports only
Lean/mathlib's standard logical axioms `propext`, `Classical.choice`, and
`Quot.sound`.

## Completion status

The regular compact-type case of Theorem 3.6 is formalized.  The public
terminal theorem is
`PerronWright.CompactPerronWrightTheorem.compactPerronWright_theorem`.
For a `CompactBJRModel`, the only additional regular-critical hypothesis is
`IsRegularCritical`, whose fields are exactly `(B1)` and `(B2)`.  The model
itself contains the baseline compact BJR data: a probability law with full
support and a continuous symmetric nonnegative kernel on a compact metric
Borel type space.

The theorem constructs the analytic critical radius, identifies its physical
real branch with the genuine rooted-tree FMS convergence radius, proves
positivity and the quadratic logarithmic expansion
`alpha^2/(2*beta) * (t-1)^2 + O(|t-1|^3)`, and proves the literal finite-graph
Perron--Wright formula for every fixed surplus cutoff `R`.  In the arbitrary
shrinking-window conclusion, the relative-error constant is chosen before the
nonnegative sequence `eta -> 0`; only the eventual threshold may depend on
that sequence.  The separate fixed-window conclusion uses the literal window
`|t-1| <= L*k^(-1/2)` and relative error `O_{R,L}(k^(-1/2))`.

No positive-surplus enumeration or analytic-transfer statement is assumed as
an interface.  The proof includes the exact variable-kernel reconstruction
fibre, coordinate multiplicity and weighted regrouping; the cubic main term;
the all-length noncubic admissible series; its local and global analytic
continuations; the one-fold-lower noncubic coefficient bound; and the finite
induction joining tree, unicyclic, and positive-surplus cases.  The source
contains no `sorry`, `admit`, project-defined `axiom`, or `opaque` proof
constant.

## E-drive build

On filesystems without Git ownership metadata, Lake's dependency check needs
temporary `safe.directory` entries for the project's dependency repositories.
Run `Build.ps1` from this directory.  It sets these entries only in the
current process; it does not modify global Git configuration.

## Compact probability extension: proved foundations and remaining work

Authoritative project: `E:\PerronWrightFormalization`. The old C-drive copy
has not been changed or removed.

The probability sources live in `PerronWright/Probability`. They concern the
literal annealed compact BJR graph, with independent sampled types and edge
probabilities `1 - exp(-t*kappa(x,y)/n)`. They do not silently replace it by
a finite-type or homogeneous special case.

Proved so far:

- `IndependentEdges`, `AnnealedGraph`, `AnnealedTypedGraph`: normalized
  finite independent-edge laws and the joint type-and-edge probability law;
  actual graph/type marginals and expectation identities. The joint law
  retains types so empirical marks refer to the same sampled graph.
- `ComponentBlocks`, `ComponentCounts`: bijections with genuine connected
  components and ordered distinct component tuples, including literal size
  and surplus constraints. The factorial observable is not an independently
  supplied combinatorial count.
- `SelectedConfiguration`, `ExactFactorialExpectation`: exact selected
  isolated-configuration probabilities and the finite-`n` raw factorial
  expectation formula. Unconstrained edges are integrated out and the edge
  odds factorization is proved. The subsequent enumerator-times-residual
  reduction and residual asymptotic are still pending.
- `ConnectedTypeLaw`, `ConnectedTypeTails`: the actual fixed-size/surplus
  weighted connected-graph type law, its normalization and eligible-graph
  support, the exact field-tilting and centered Laplace identities, genuine
  exponential integrability, and upper/lower Chernoff probability bounds in
  terms of the literal enumerator ratio.
- `ConnectedTypePositivity`, `ConnectedTypeDomination`: eventual positive
  zero-field normalizers are derived from the completed enumeration theorem.
  Field domination proves positivity for every real continuous field, with
  one eventual size threshold for a bounded surplus range. The crude
  exponential bound here is not claimed as centered profile concentration.
- `EmpiricalTypeMarks`: actual empirical probability measures of component
  types, measurability, exact vertex-average test integrals, and the genuine
  Perron probability law in the same mark space.
- `CriticalScaling`: nonnegative critical times agreeing eventually with
  `1 + lambda*n^(-1/3)`, and the literal floor sizes with normalized error
  and convergence proofs.
- `ComponentPointProcesses`, `PointProcessNormalization`: actual finite
  unmarked/marked component point measures, measurable random-measure laws,
  and the paper's starred size coordinate `beta^(1/3)*n^(-2/3)*|C|`. These
  are measurability results for the evaluation sigma algebra, not yet a
  local-vague convergence theorem.
- `ProjectiveKernel`, `ProjectiveQuadratic`: the literal `(QP)` feature
  representation, uniform kernel-series convergence, the actual four-term
  centered product-measure integral, its absolutely convergent feature-square
  identity, and deterministic bounds. No scale-matched exponential-moment
  estimate is assumed.
- `FactorialDensity`: the paper's literal candidate factorial density, its
  positivity, square-completed exponent, uniform cubic bound, and exponent
  rescaling. Identifying this with Brownian excursion factorial densities
  remains a separate proof obligation.

`ProbabilityAudit.lean` prints dependencies of the proved probability
results, while `Audit.lean` continues to audit the entire enumeration chain.

Validation of this milestone (2026-10-02): all 18 probability modules are
included in the umbrella, and `Build.ps1 PerronWright` completed successfully
(4233 jobs). Both audit files compiled. The full audit checked 1179 printed
declarations; its only dependencies were `propext`, `Classical.choice`, and
`Quot.sound`, with no unexpected axiom. The source scan over
`PerronWright/**/*.lean` found no `sorry`, `admit`, project `axiom`, or
`opaque` declaration.

Remaining obligations at the initial probability-foundations milestone
(see the later progress records below):

1. Uniform centered profile Laplace/concentration estimates and their
   summable, scale-matched quadratic exponential control.
2. Exact enumerator/residual decomposition and compact annealed residual
   asymptotics under `(QP)`, including the finite-population corrections.
3. Uniform fixed-size factorial asymptotics on every compact positive-size
   window, with the literal floor sizes and fixed surplus tuple.
4. Local moment bounds, determinacy, and local-vague point-process convergence.
5. Construction/identification of the Brownian-excursion/Poisson-surplus Aldous
   process and its Wright-constant factorial densities, without an assumed
   Brownian identification interface.
6. Empirical Perron-mark concentration and the marked process limit.

In particular, the existence of the finite point-process laws and the
candidate density is not a proof of their convergence. No terminal
probabilistic theorem with placeholder proofs is declared.

## Full Chapter 3 target (active)

The scope now includes every main result in `03_statements.tex`:

- `thm:Perron-Wright`: the regular compact branch is complete; the
  irreducible finite-type branch remains to be proved in its stated scope.
- `prop:AW-density`: the literal candidate density and its window bounds
  are proved; Brownian-excursion realization, density identification, and
  restricted-process determinacy remain.
- `thm:local-main`: both deterministic finite-type and annealed compact
  `(QP)` models, including the uniform floor-size factorial asymptotic and
  the unmarked and empirically marked process limits.
- `thm:countable-realization`: actual growing finite supports, integer
  counts, spectral normalization, and the factorial/unmarked/marked
  local limits with total-variation marks.
- `thm:countable-unrenormalized`: the original-kernel graph, including
  the `lambda + theta` spectral-drift conclusion and its zero-drift case.

The finite model in the paper assumes irreducibility, not primitivity.
In particular a bipartite irreducible kernel need not satisfy compact
assumption `(B2)`. No finite branch is claimed by silently strengthening
the hypothesis or applying an invalid compact-model adapter. Likewise
the countable type space is not assumed compact.

New proved foundations in this phase:

- `FieldLogRadiusTaylor`, `ProfileEnumeration`, `ProfileLaplace`: actual
  field-radius derivative and increment bounds; arbitrary continuous-field
  tree/unicyclic/cubic/noncubic enumeration; genuine centered Laplace and
  two-sided Gaussian probability bounds for the actual connected-type law.
  The normalized-enumerator correction is the proved additive `log 3`,
  not an assumed stronger vanishing bound.
- `FreshTypeAveraging`, `AnnealedResidualFixedBlock`: independent unused
  type averaging, the actual selected-and-isolated ambient graph event,
  its exact internal-edge odds formula, and the fixed-configuration
  enumerator-weight/residual factorization. Ordered multi-component
  relabeling, normalization, and residual asymptotics remain separate.
- `FactorialWindowBounds`, `FactorialWindowMass`: uniform density bounds
  and actual Lebesgue/counting window integrals, with weighted series
  summable at every real argument. These are not yet Brownian identification
  or point-process convergence theorems.
- `FixedTypeGraph`, `CriticalParameterDrift`,
  `SpectralNormalizationGraphLaw`: actual deterministic-type graph laws
  and factorial identities; the effective parameter tends to
  `lambda + theta`; the normalized and unnormalized graph laws are exactly
  equal after the effective-parameter substitution. Uniform varying-
  parameter limit theorems are still required.
- `FiniteTypeCounts`, `IntegerTypeAssignment`, `SlowGrowingIndex`,
  `GrowingTypeCounts`: literal corrected floor counts and vertex
  assignments, a proved monotone diagonal selection, exhaustive growing
  supports, and the uniform critical-scale minimum population condition.
  No finite-support realization is accepted as an external interface.

All project changes remain in `E:\PerronWrightFormalization`; the old
C-drive copy remains untouched. The full Chapter 3 objective is not marked
complete while any terminal result above or any nontrivial dependency
remains unproved.

Further verified foundations (same phase):

- `GrowingTypeApproximation`, `GrowingTypePositive`,
  `CountableTypeRealization` close the actual countable support construction:
  every positive `n` has strictly positive counts on its retained support,
  totals are exactly `n`, types are assigned to actual `Fin n` vertices,
  and their literal Dirac empirical measures are probability measures.
  The full atomic absolute-variation sum tends to zero and the scaled
  minimum is proved uniformly over the growing support.
- `CountableKernel`, `CountableIntegral`, `CountableCompact`,
  `CountableSymmetric`, `CountablePositive`, `CountablePerron`,
  `CountableSimplicity`, `CountablePerronQuantities` construct the actual
  atomic `L²(mu)` integral operator. Compactness follows from finite-rank
  output truncations and probability tails; symmetry follows from Fubini.
  Literal spectral-radius criticality and a strict lower kernel bound give
  the proved unique positive normalized Perron vector, its actual
  probability law, and positive `alpha` and `beta`. None is a model field
  supplying an unproved spectral conclusion.
- `AnnealedTupleResidualCounting`,
  `AnnealedTupleResidualExchangeability`,
  `AnnealedTupleResidualPatternFormula` derive the literal
  `(n)_K / product(k_i!)` factor and the selected-type/internal-pattern
  integral from actual ordered distinct components, proved relabeling,
  and the actual annealed graph law. Identification with product
  connected-type laws and residual asymptotics are still subsequent work.
- `ProfileSquareMoment`, `ProfileSquareSeries` prove scale-matched
  exponential-square moments, including a genuinely countable feature
  series with summable norm-square budget. The proof controls the whole
  support via the proved Laplace bounds, not an assumed unrestricted
  Gaussian-tail estimate.

These close substantial dependencies but do not yet prove the remaining
terminal local asymptotics, Brownian identification, or process limits.

### Integrated probability and countable-spectral milestone (2026-10-02)

The next complete umbrella build succeeded with 4290 jobs. The full audit
checked 1197 printed declarations and the probability audit checked 102;
both compiled and reported only `propext`, `Classical.choice`, and
`Quot.sound`. The project source scan found no `sorry`, `admit`, mathematical
`axiom`, or `opaque` declaration.

New integrated results:

- `AnnealedTupleResidualConnectedLawProduct`, `...GraphTuple`, `...Weights`,
  `...Coordinates`, and `...Formula` close the exact multi-component
  connected-law bridge. The actual component-count expectation equals the
  literal selection factor, enumerator product, and expectation of the
  actual finite-`n` residual under independent connected-type laws.
  The normalization, graph-pattern bijection, coordinate measure
  preservation, Fubini, and residual integrability are proved, including
  possibly zero kernel entries. Residual *asymptotics* remain subsequent
  work.
- `ProfileScaleMatched`, `ProfileFiniteCollection`,
  `ProjectiveFiniteCollection`, `ProjectiveKernelClosure`, and
  `ProfileCollectionScaleMatched` prove the actual pooled projective
  quadratic exponential bounds. The original `(QP)` hypothesis implies
  a proved representation of the literal residual kernel; the BJR-scale
  exponential moment tends to one under `k_total <= C N^(2/3)`.
  Individual and total sizes need not diverge: bounded and mixed cases
  are covered, with no assumed unrestricted Gaussian estimate.
- `BinomialInversion`, `FactorialCountDeterminacy`,
  `FactorialGeneratingSeries`, `FactorialWindowCountDeterminacy`,
  `CountFamilyDeterminacy`, and `FactorialTailBounds` prove exact joint
  count-law recovery from factorial moments, the generating-series
  integrability bridge, uniqueness of a whole count-family law from its
  finite-dimensional laws, and the next-factorial-moment tail bound.
  These are actual analytic determinacy/uniform-tail results, not a
  declaration of local-vague point-process convergence or Brownian
  identification.
- `CountableApproximationOperator`, `...Weights`, `...Spectral`,
  `...Finite`, `...Perron`, `...Vectors`, `...Empirical`, and
  `CountablePerronQuantitiesApproximation`, `...Moments` derive genuine
  finite-law spectral and Perron approximations from full atomic
  absolute-variation convergence. The positive integer-count empirical
  construction has actual operator-norm convergence, actual spectral
  radius tending to one, convergent positive normalized Perron
  functions, and all power moments (including `alpha`, `beta`).
  The construction is indexed by `n+1` vertices to exclude the zero
  probability-law case; no random-graph limit is asserted by this
  spectral construction alone.

The remaining terminal obligations are still explicit: the full
irreducible finite-type enumeration branch, deterministic and compact
annealed residual/local factorial asymptotics, the point-process
convergence criterion and its application, the actual Brownian-excursion
and Poisson-surplus realization/density identification, empirical marked
process limits, and the countable local limits and diagonal transfer.
Only the regular compact enumeration terminal theorem is currently
complete. The full Chapter 3 goal remains active.

### Finite irreducibility, empirical marks, and residual-error milestone

The next umbrella build succeeded with 4312 jobs. `Audit.lean` checked
1208 printed declarations and `ProbabilityAudit.lean` checked 136; both
reported only `propext`, `Classical.choice`, and `Quot.sound`.

- `FiniteIrreducibleModel`, `FiniteIrreducibleSpectral`,
  `FiniteIrreducibleAbsolute`, `FiniteIrreduciblePerron`,
  `FiniteIrreduciblePerronQuantities`, and `FiniteIrreducibleComplement`
  prove the actual finite-model positive simple Perron eigenfunction and
  the complementary inverse from the paper's literal irreducibility and
  spectral-radius assumptions. They do not assume primitivity or exclude
  the eigenvalue `-1`. `FiniteIrreducibleBipartite` verifies the actual
  two-type bipartite critical example with that eigenvalue. The complete
  finite enumeration theorem still requires its analytic continuation and
  enumeration bridge.
- `CountablePerronLawApproximation` proves full atomic absolute-variation
  convergence of the actual finite Perron probability laws. The resulting
  estimate is uniform over all measurable events. This is not yet the
  random-graph total-variation marked limit.
- `EmpiricalMarkConcentration`, `EmpiricalWeakNeighborhood`, and
  `EmpiricalMarkWeakConcentration` prove concentration of actual empirical
  `ProbabilityMeasure` marks in every genuine weak neighborhood of the
  actual Perron law, under the actual connected and pooled product laws.
  Pooled sizes may be mixed; only their total must diverge. The finite-test
  weak-neighborhood criterion and measurable weak-open sampling events
  are proved, not assumed. Density transfer to graph components remains
  subsequent work.
- `FreshTypeCumulantExpansion`, `AnnealedResidualCumulantExpansion`,
  `FreshTypeEmpiricalIdentities`, and `FreshTypePerronCentering` derive the
  exact selected residual logarithm, its actual third-order cumulant
  expansion, and its deterministic fourth-order error. The quadratic
  part is exactly the centered pooled projective observable already
  controlled by the `(QP)` results; Perron row/column cancellations and
  selected-label coordinate identities are proved.
- `FinitePopulationLog` proves the literal falling-factorial selection
  expansion, including the simplified quadratic/cubic correction.
  `AnnealedResidualCriticalError` proves the actual eligible-component
  edge bound and vanishing of the deterministic cumulant/odds envelope
  on `K <= C N^(2/3)`, without assuming a residual asymptotic.

These integrated results are dependencies toward the probability main
theorems, not substitutes for them. In particular, the actual residual
expectation limit, the local factorial asymptotic, Brownian-excursion
identification, process limits, and countable graph transfer remain open.

### Literal finite analytic bridge and actual profile-functional milestone

The next umbrella build succeeded with 4335 jobs. `Audit.lean` checked
1224 printed declarations and `ProbabilityAudit.lean` checked 159; both
reported only `propext`, `Classical.choice`, and `Quot.sound`.

- The finite irreducible bridge constructs the literal weighted discrete
  probability model and its actual compact self-adjoint L2 operator of norm
  one. Its complex Perron functional, augmented inverse, and analytic local
  tree-equation germ are proved. A canonical finite metric realization is
  also constructed. The bipartite example is explicitly proved not to satisfy
  B2; no primitivity hypothesis or invalid regular-compact adapter is used.
  The selected critical pair, physical least branch, global continuation,
  and full finite enumeration endpoint are subsequent obligations.
- `AnnealedProfileFunctionalContinuous`, `AnnealedProfileFunctionalSampled`,
  and `AnnealedProfileFunctionalConcentration` prove actual weak-continuity,
  label reindexing, and joint probability concentration of degree, kernel
  pair, second and third exposure moments, variance, and third cumulant at
  their six literal Perron values. Measurability is proved directly on the
  sampling space, without assuming a weak/Giry sigma-algebra identification.
- `BoundedConcentrationTransfer` proves the actual expectation transfer from
  bounded probability errors plus exponential control. With the true QP
  series bound, `PooledResidualExponential` proves L1 convergence of the
  actual quadratic exponential factor on the full critical size scale.
- `CriticalResidualScaling` proves exact limiting thermal and cubic
  coefficients for the literal critical time and normalized size sequences.
- `MixedFactorialTail` proves actual finite-state truncation and next-moment
  tail bounds. `FactorialCountConvergence` proves actual tightness directly
  from moment convergence. Its first weak-convergence result has an explicit
  stronger uniform summable moment bound; it is not counted as the weaker
  target-determinacy-only criterion needed by the paper.

These are integrated proved dependencies, not completed probability or
finite-enumeration main theorems. All five Chapter 3 targets remain tracked
separately in the table above; only the regular compact enumeration terminal
theorem is currently complete.

### Actual critical windows, weak point measures, and finite critical pairs

The umbrella build passed 4373 jobs. The refreshed full audit checked
1251 printed declarations; the probability audit checked 220. Both reported
only `propext`, `Classical.choice`, and `Quot.sound`.

- `FactorialCountConvergenceCriterion` proves actual count-law convergence
  from mixed factorial moment convergence and the target law's determining
  series alone. No uniform all-source determining series is assumed.
- The actual critical time and literal floor sizes give positive connected
  normalizers, existing placements, the required square-root field bounds,
  Stirling normalization, and the single-component local enumeration limit.
- The actual profile-functional exponent and finite corrections have been
  identified and controlled under the genuine connected product law.
- Six new finite irreducible analytic modules prove the actual critical
  pair, algebraically simple positive eigenvalue one, actual spectral radius
  one, first profile/radius responses, and actual Hessian Taylor remainders.
  This still does not identify the physical least branch or prove the full
  finite enumeration endpoint; the eigenvalue `-1` remains allowed.
- The genuine finite integer point-measure space has compact bounded-count
  subsets. Actual first-mass bounds give tightness of actual laws, and weak
  point-measure convergence gives literal count convergence at sets with
  zero frontier mass. This is not yet graph-process convergence.

These are verified dependencies. The Chapter 3 terminal status table above
remains unchanged until the actual main-result statements are proved.

### Actual compact local formula and genuine window-law tightness

The umbrella build passed 4486 jobs. The refreshed full audit checked
1340 printed declarations; the probability audit checked 352. Both reported
only `propext`, `Classical.choice`, and `Quot.sound`.

- `CompactAnnealedFactorialUniform` proves the actual annealed compact part
  of the local factorial theorem: uniformity on every fixed positive size
  window and every bounded surplus tuple, from the paper's B1/B2 and QP.
  Arbitrary moving floor coordinates, residuals, normalizers, placements,
  Stirling factors and uniformity are derived, not assumed.
- `CompactAnnealedFactorialBound` gives actual integer-tuple expectation
  bounds. `CompactAnnealedFactorialWindowIntegral`, `CriticalFloorCells`
  and `CompactAnnealedFactorialGridIntegral` prove measurability, density
  window-integral convergence, exact floor-cell volumes and exact finite
  grid-cell graph-count integrals. These do not assume a Riemann-sum limit.
- `ComponentWindowPointMeasures` and `ComponentWindowCounts` construct
  the actual graph component law on the weak-Borel integer point-measure
  space and prove exact restriction and first-mass counting identities.
  `ComponentWindowTightness` proves actual unmarked and starred window-law
  tightness and relative compactness from the graph factorial bound,
  including the finite prefix of graph sizes.
- `FinitePointMeasureMeasurable`, `FinitePointMeasurePolish` and
  `FinitePointMeasureCountDeterminacy` prove measurable Borel-cell counts,
  a genuine Polish point-measure space, and actual probability-law
  uniqueness from finite count laws or determining factorial moments.
- The five `AnnealedMarkedResidual` modules prove the actual residual
  weighting is a probability law, all-time integrability and positivity,
  joint weak mark concentration, and residual-weighted continuous test
  convergence to the actual Perron probability law. The six subsequent
  marked-factorial modules prove actual typed-graph exchangeability,
  the exact ordered component formula and its moving-floor joint mark-test
  limit; the constant-one test recovers the actual unmarked expectation.
- Thirteen finite irreducible analytic modules additionally identify the
  literal zero-field labelled rooted-tree series radius as one, its
  physical least branch, and the joint normalized fold profile on a
  complex lens. Their separate 83-declaration audit is standard-only.
  No B2/primitive assumption is added, and the eigenvalue -1 is allowed.

- Ten more finite irreducible modules prove exact positive profile tilts,
  conjugacy of actual labelled tree coefficients and radii, and identify
  the genuine small-real-field least branch with a common analytic fold
  chart. Their separate 46-declaration audit is standard-only.
- Thirteen further finite irreducible proof modules construct the actual
  joint complex-field rooted-tree continuation on one Cartesian Delta
  product, prove its exact complex-field series radius and identify the
  genuine series sum throughout the open unit disk. Their separate
  63-declaration audit is standard-only. Strict closed-disk majorization
  comes from actual positive degree-one/two coefficients, not B2. The
  final finite connected-graph enumeration and coefficient transfer remain
  pending.
- `ComponentWindowFactorialCounts` and `CompactWindowFactorialMoments`
  prove all literal window falling factorial moments, including order zero.
  `FactorialCountLimitExistence` proves existence and uniqueness of a law
  from actual factorial moment convergence, not from an assumed target.
  `CompactWindowCountLaw` applies it to the actual window component number:
  its unique probability law is constructed, all moments are the density
  integrals, and the entire sequence converges weakly to it.
- The two mixed-cell counting modules prove exact genuine joint cell-count
  identities and integrability for arbitrary disjoint Borel size cells and
  finite surplus sets, with no assumed factorial-moment identification.
- `CompactSizeCellFactorialLimits`, `CompactSizeCellMomentBounds` and
  `CompactJointCellCountLaw` prove all actual mixed factorial limits, the
  literal density-series bound and the unique weak limit of actual joint
  disjoint-cell count laws. Zeroth order is proved explicitly, and no
  target-law realization is supplied as an assumption.
- Six further marked-window modules prove actual uniform coupled mark
  tests and their genuine entire-window factorial integrals. Expected total
  mark-test deviation tends to zero, and the probability of any actual
  window component (or distinct tuple) lying outside the Perron weak
  neighborhood tends to zero. This is not merely an auxiliary residual-law
  statement and does not yet assert the full marked process limit.
- `PointMeasureBoundary` and `CompactWindowBoundary` derive open-strip
  Portmanteau first-moment bounds and almost-sure absence of every fixed
  size-boundary atom in actual window-law subsequential limits, including
  the two window endpoints. Count continuity is a proved consequence, not
  a new model assumption.
- `FiniteBooleanCellRefinement` and `CompactOverlappingCellCountLaw`
  handle arbitrary overlapping finite size-surplus queries by a proved
  Boolean atom partition and an exact count-law pushforward identity.
  Their unique limiting count law is not an assumed interface.
- `PointMeasureCountMapping` proves the required discontinuous count
  mapping theorem from almost-sure frontier nullity; the actual graph
  boundary estimate supplies that condition.
- Ten finite irreducible path/pole modules prove the literal path-weight
  series sum, the Perron resolvent residue, cycle singularity, actual
  cubic integrated amplitude and forbidden/noncubic extra powers. Their
  separate 237-declaration audit is standard-only. The final connected
  EGF identification and coefficient transfer are still pending.
- `WindowCountGenerators` proves that the literal rational size/surplus
  cells generate the Borel sigma algebra and identify actual point laws.
  `CompactWindowPointLawLimit` combines actual graph tightness, actual
  boundary estimates and actual query count-law limits to construct a
  unique weak limit of the entire unmarked compact-window point law.
  This is genuine point-law convergence, not only convergence of counts.
- Seven marked-window law modules use literal empirical probability
  measures with their actual weak topology and Borel space. Bounded
  continuous point-measure tests transfer in L1 to canonical Perron
  marking. `CompactWindowMarkedLawLimit` proves the actual entire-sequence
  marked-window weak limit, without source-convergence or concentration
  hypotheses supplied as interfaces.
- `WindowSizeRescaling` transports the true component-selection predicate,
  atom family and source law under positive size rescaling. The literal
  `beta^(1/3)` starred unmarked window law therefore also has a unique
  proved weak limit.
- `CompactWindowLimitCellMoments` identifies all mixed factorial moments
  of actual cell counts under the actual limiting point law with the
  literal density integrals, including order zero. Genuine boundary-null
  count mapping and uniqueness supply the identity, not a target process
  moment assumption.
- Twelve further finite irreducible cubic EGF modules connect the literal
  labelled cubic contribution to the actual resolvent, its full Taylor
  series, a common joint complex-field Delta continuation and quantitative
  uniform coefficient transfer. Their separate 66-declaration audit is
  standard-only. The true cubic-part labelled asymptotic has relative error
  `O(norm(g) + k^(-1/2))`, with no B2 assumption. It is explicitly not
  substituted for the full connected enumerator; the noncubic all-length
  remainder and the total finite terminal remain pending.

The compact local factorial part is now complete. This does not complete
the entire local/main process theorem, the actual Brownian--Poisson
factorial density identity, the literal finite enumeration endpoint or
the countable graph-limit endpoints. Those remain tracked above.

### Actual finite positive-surplus enumeration and global vague-law tightness

The umbrella build passed 4593 jobs. The refreshed full audit checked
1411 printed declarations; the probability audit checked 402. Both reported
only `propext`, `Classical.choice`, and `Quot.sound`.

- Five finite irreducible scalar-response modules prove the actual physical
  radius, its real analyticity and positivity, the exact first and second
  responses, and the cubic remainder for `log rho(t)`. The Gaussian-window
  conversion has a proved uniform relative `O(k^(-1/2))` bound.
- Fourteen further finite irreducible enumeration modules connect the actual
  all-length noncubic contribution to its joint field continuation and
  quantitative coefficient bound. Added to the actual cubic contribution,
  they prove the literal connected enumerator for every surplus `r >= 2`,
  its shrinking-field physical-radius formula, and its Gaussian critical
  window formula, uniformly over finite surplus ranges. No B2/primitivity
  assumption is added. The actual finite tree and unicyclic cases are still
  pending and are not counted as complete.
- `MarkedWindowSizeRescaling` and `CompactStarredMarkedWindowLawLimit`
  transport the actual empirical-marked atom family and its source law;
  both starred fixed-window point laws now have unique proved weak limits.
  The limiting empirical mark is the actual canonical Perron probability.
- `CompactGlobalTestLawLimit` proves unique limits of every literal finite
  family of global compact-support test integrals.
- Five global-chart modules construct a genuinely Polish compatible-chart
  space, prove tightness of the actual graph chart laws, assemble their
  compatible compact-support values into an actual Riesz measure, and prove
  that every compact restriction is a finite integer Dirac sum. Assembly
  is genuinely vague continuous. The source-law pushforward identity then
  proves tightness and actual weakly convergent subsequences of the global
  graph point-process law, not merely limits of individual counts. This
  checkpoint does not yet claim global full-sequence uniqueness.
- Three Gaussian-skeleton modules construct a real probability law from
  the actual consistent finite Gaussian laws using conditional kernels and
  the Ionescu--Tulcea construction. Their literal rational-time process is
  jointly Gaussian, with covariance `min(s,t)` and the genuine increment
  laws; this is not a postulated Brownian process.
- Gaussian fourth moments, dyadic-grid geometry and Borel--Cantelli prove
  the actual almost-sure all-level geometric increment bound. Three
  deterministic dyadic-extension modules prove convergence, exact grid
  matching and continuity from those bounds. The actual rational values
  agree simultaneously with their dyadic approximation limits; this
  agreement is proved rather than assumed as a modification interface.
- `ContinuousPathReflection` proves continuity of the literal running
  infimum on `[0,t]`, nonnegativity and continuity of reflection, and its
  uniform `2 epsilon` stability. Parabolic drift preserves those proved
  path properties. Excursion enumeration, Poisson marking and the actual
  Aldous factorial-density identity are separate pending obligations.
- `BrownianContinuousModification` constructs the actual continuous
  extension on the sampled Gaussian probability space. It proves
  almost-sure path continuity, measurability at every real time, equality
  with all original rational coordinates on one full-measure set, and
  the actual zero-time normalization. Arbitrary real-time finite Gaussian
  laws are a subsequent obligation and are not assumed.
- `BrownianGaussianLinearTests` proves the exact characteristic integral
  of every finite rational-time real linear combination, from its actual
  Gaussian law and literal minimum-kernel variance.
- `BrownianParabolicReflection` applies the proved running-minimum
  operation to the actual sampled continuous process. One actual
  full-measure set gives continuous nonnegative reflected paths and open
  positive sets simultaneously for all real drift parameters. This is
  not an assumed Brownian reflection or an Aldous process identity.

### Continuous Brownian realization, finite unicyclic terminal and global uniqueness

The umbrella build passed 4618 jobs. A fresh full audit checked 1434
printed declarations and the probability audit checked 418, with no
unexpected axioms or diagnostics. Both use only `propext`,
`Classical.choice`, and `Quot.sound`. The project-source forbidden-token
scan had no hits outside the explicit audit files.

- `InitialTopologyLawDetermination` proves actual measure determination
  by finite cylinders, including the generated Borel sigma-algebra.
  `GlobalPointChartSurjective` proves that every actual locally finite
  integer point measure is assembled by the compatible-chart space.
  `CompactGlobalPointLawLimit` then proves uniqueness of all actual global
  subsequential limits and full-sequence weak convergence. No candidate
  limit or law-determination hypothesis is postulated.
- `ProperLocalPointMap` proves continuity and integer-atomicity of actual
  proper point-measure pushforwards. `GlobalPointSizeRescaling` proves the
  literal positive size dilation is proper, matches the finite component
  Dirac sum exactly (including `n = 0`), and transports the actual source
  laws to unique global scaled and starred weak limits.
- `BrownianContinuousLinearTests` passes the genuine rational Gaussian
  characteristic identities to real-time linear tests by proved dyadic
  approximation and dominated convergence. `BrownianContinuousGaussianLaw`
  identifies all real finite-dimensional laws and proves the actual
  `IsBrownianReal` witness, covariance `min(s,t)` and independent increments.
  Brownian existence is a conclusion here, not a hypothesis.
- Fourteen finite irreducible unicyclic modules prove the actual
  simple-cycle power-series identity, its joint field continuation and
  uniform coefficient error. `FiniteIrreducibleUnicyclicTerminal` proves
  the actual `connectedWeight t k 1` physical-radius and Gaussian formulas,
  with the literal constant `sqrt(pi/8)`. The shrinking-window error
  constant is chosen before the window sequence. No compact B2/primitivity
  hypothesis is imposed on this finite irreducible branch.

Global convergence to a constructed unique law is not yet identification
with the literal Brownian--Poisson Aldous process. Its excursion construction
and Wright density identity remain separate obligations.

### Full finite enumeration, global empirical marking and actual area rates

The umbrella build passed 4664 jobs at this checkpoint. A fresh full
audit checked 1488 printed declarations and the probability audit checked
464; both exited successfully with no diagnostics or unexpected axioms.
All printed dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`. The literal Chapter 3 status table above distinguishes
completed main statements from remaining identification/graph-limit work.

- `FiniteIrreduciblePerronWrightTerminal.finite_perronWright` combines the
  genuine tree, unicyclic and total positive-surplus enumerators into the
  full finite irreducible theorem. Its Wright constants are exactly the
  compact branch's classical family. The radius is the actual rooted-tree
  series radius, and the shrinking-window constant precedes every chosen
  window sequence. The common Gaussian error is uniform over every bounded
  surplus range, including surplus zero. Period-two kernels remain allowed.
- `CompactGlobalMarkedPointLawLimit` proves actual full-sequence empirical-
  marked vague-law convergence to the explicit constant-Perron marking of
  the genuine global unmarked limit. Its compatible Polish charts handle
  empty ground spaces and assemble actual finite integer Dirac restrictions.
  `GlobalMarkedPointSizeRescaling` proves exact source pushforwards, marking/
  dilation commutation, and the literal starred finite atom identity. Both
  global starred laws are thus proved, without assuming Aldous identification.
- `BrownianPathLaw` constructs the actual compact-open Polish--Borel path
  probability law, from a proved measurable path representative of the
  constructed Gaussian process. `BrownianPathReflectionLaw` proves genuine
  continuous reflection/drift maps, their actual probability pushforwards,
  joint field measurability and all-time/all-parameter raw-process agreement.
- `PoissonCountKernel`, `PoissonFactorialMoments` and `PoissonMixedCountLaw`
  construct actual finite independent Poisson counts, prove their all-order
  mixed factorial moments, and construct genuine random-rate joint laws.
  `CountablePoissonKernel` proves the infinite-product count law is measurable
  in its actual rates, hence supplies a genuine countable marking kernel.
  `BrownianReflectedAreaCounts` discharges rate measurability for actual
  reflected Brownian integrals, including variable interval endpoints.
  `BrownianUnderGraphIntensity` proves the bounded region's planar Lebesgue
  mass is exactly this area and is finite. These facts do not yet construct
  the full spatial PPP or prove excursion factorial densities.
- `CountableVariationMarks` gives the actual probability measures on
  `Nat` the full absolute atomic-variation metric (twice conventional total
  variation). `CountablePerronMarkConvergence` proves genuine finite Perron
  mark convergence in this metric. No compactness, local compactness or
  Polish-space property is asserted for this mark space.

The entire Chapter 3 goal remains active. Only the completed branches in
the status table are counted as main-result endpoints; auxiliary proved
lemmas and subsequential limits are not substituted for the remaining
literal statements.

### Literal finite probability interfaces and actual bounded spatial Poisson laws

The umbrella build passed 4689 jobs with no diagnostics at this checkpoint.
The fresh full audit checked 1524 declarations and the probability audit
checked 500; both exited successfully with no unexpected axioms or
diagnostics. The forbidden-source scan was empty. Independent leaf audits
also checked the newly frozen finite exact formulas, finite profile estimates,
and Brownian component/area construction using only the standard three
logical axioms.

- `FiniteIrreducibleTypedGraphLaw` and
  `FiniteIrreducibleTypePlacementMultiplicity` use the real independent-edge
  fixed-type graph and actual type-fibre embeddings. The selection factor
  is the literal product of descending factorials. Type-preserving ambient
  permutations prove genuine placement invariance.
- `FiniteIrreducibleConnectedOddsFactorialFormula` proves the exact ordered-
  component factorial expectation for every actual integer type assignment.
  The formula contains only actual type counts, the count-based isolation
  budget, and products of genuine connected simple-graph edge-odds sums.
  The denominator of an edge hazard is the ambient population, not the
  component size. No special rounding assignment is imposed.
- `FiniteIrreducibleProfileEnumeration`, `FiniteIrreducibleProfileRadius`,
  and `FiniteIrreducibleProfileLaplace` prove the actual arbitrary-field
  enumeration/radius/Laplace estimates. `FiniteIrreducibleEmpiricalConcentration`
  then proves actual weak-neighbourhood concentration of the empirical
  type probability measure. The model-only terminal chooses its own
  positive normalizers and thresholds. Period-two kernels remain allowed;
  no compact regular-critical adapter, B2 or QP is assumed in this branch.
- `BrownianWindowExcursions`, `BrownianWindowExcursionEndpoints`,
  `BrownianActualWindowExcursions`, and `BrownianWindowExcursionAreas`
  construct the real positive-window connected components, their measurable
  endpoints, nonrepeating rational representatives, and their strictly
  positive actual component integrals. They agree with the constructed
  raw Brownian process on a single proved full set. These are clipped
  bounded-window components, not a substituted full-time excursion process.
- `FinitePoissonPointLaw` constructs an actual Poisson number of iid
  locations as a weak-Borel finite integer atomic random measure.
  `FinitePoissonPointLaplace` proves its measurable-test Laplace formula
  directly from independent integration and the exponential series.
  `FinitePoissonIntensityLaw` and `FinitePoissonIntensityLaplace` realize
  any genuine finite spatial intensity, including zero, and prove its
  exact first intensity and Laplace functional. `BrownianUnderGraphPoissonLaw`
  applies them to literal unit planar Lebesgue measure under each bounded
  reflected path; its actual point count is Poisson at the proved area rate.

Still required at that checkpoint for the literal Chapter 3 terminals:
deterministic finite depletion/residual asymptotics, the joint spatial/global
Brownian excursion construction and Wright density identification, and the
constructive countable graph-limit transfers. Later checkpoints below
supersede parts of these obligations without assuming their conclusions.

### Actual spatial count identification and deterministic population averages

The umbrella build passed 4709 jobs with no diagnostics. A fresh full
axiom audit checked 1592 dependency outputs and the probability audit
checked 568; both exited successfully with no diagnostics or unexpected
axioms. The six new spatial count/identification leaves have a separate
complete named-declaration audit, including the axiom-free declaration.
The forbidden-source scan was empty. Only `propext`, `Classical.choice`,
and `Quot.sound` occur in the audited dependencies.

- `FinitePoissonIidCellFactorials` proves disjoint-cell factorials by a
  genuine labelled-injection bijection and actual independent-coordinate
  integration. `FinitePoissonCellFactorialMoments` integrates against the
  actual Poisson count mixture and normalizes the true finite intensity.
  `FinitePoissonDisjointCellCounts` discharges absolute summability by
  exponential series and uses proved count inversion to identify the
  full finite count law with the independent Poisson product. Independence
  is a conclusion, never an assumption about the spatial law.
- `BrownianUnderGraphDisjointCounts` applies those results to literal unit
  planar intensity. `BrownianClippedExcursionSpatialCells` proves that each
  retained component's actual time strip has the true excursion area as
  intensity, and that different retained strips are disjoint.
  `BrownianClippedSpatialMarkIdentification.spatial_count_law_eq_markLaw`
  uses genuine projective uniqueness to identify the entire rational
  spatial-count law with the already constructed countable area-rate
  marking law. This is for each actual path and a clipped bounded horizon;
  neither full-time excursions nor the Wright density formula are claimed.
- `FinitePoissonPositionKernel` proves measurability when both rate and
  location distribution vary. `BrownianUnderGraphSpatialKernel` supplies
  the actual jointly measurable intensity and normalized locations,
  including zero area, and the genuine spatial Markov kernel/joint laws.
  `BrownianUnderGraphSpatialJointLaw` proves the exact actual-source to
  continuous-path joint pushforward, preservation of the real Brownian
  driver, and intensity/Laplace identities in literal raw reflected paths.
- `FiniteIrreducibleDeterministicConnectedLawFormula` proves the exact
  arbitrary-count fixed-assignment factorial expectation under genuine
  connected-state product laws. Its normalizer cutoff is supplied by the
  actual finite Perron--Wright theorem. No ambient annealed replacement is
  made. The raw residual and its exact depletion/population/isolation/odds
  factorization retain every empirical-count discrepancy.
- `FiniteIrreducibleDeterministicDepletion` and
  `FiniteIrreducibleDepletionRounding` prove uniform all-profile log
  expansions and vanishing critical-size remainder for arbitrary
  deterministic counts `c_n(a) = n mu(a) + O(1)`. Actual independent
  connected-profile square moments and Pearson exponential averages are
  proved in `FiniteIrreducibleProfileFiniteCollection` and
  `FiniteIrreduciblePearsonProfile`, with model-only positivity cutoffs.
  `FiniteIrreducibleDepletionAveraging` proves genuine L1 convergence of
  the target-normalized leading depletion times population correction,
  not just a typical-profile bound. Period-two finite models remain allowed.

The goal remains active. The remaining literal main-result obligations
include complete deterministic residual/density assembly, full-horizon
unclipped Brownian--Poisson realization and Wright density identification,
and the constructive countable graph-limit transfers. Completed clipped
constructions or compact limits are not substituted for these terminals.

### Full-horizon Brownian growth, joint clipped marks and finite prefactors

The umbrella build passed 4719 jobs. The full audit checked 1659
dependency outputs (plus two axiom-free declarations), and the probability
audit checked 635 (plus one axiom-free declaration). Both exited with no
diagnostics or unexpected axioms. A separate complete 67-declaration audit
for the new tail, joint-mark and finite-prefactor slices also passed. The
forbidden-source scan was empty. Dependencies remain restricted to
`propext`, `Classical.choice`, and `Quot.sound`.

- `BrownianGrowingDyadicWindows` proves summable bad-event bounds on
  windows of length `2^N`, with amplitude `3^N`, from the actual Gaussian
  fourth moments. Borel--Cantelli controls every dyadic level on every
  sufficiently large window. `BrownianSubquadraticGrowth` uses actual
  dyadic chaining to prove almost-sure `B(t) / t^2 -> 0` on the full time
  horizon. `BrownianFullHorizonDrift` then proves continuity and drift to
  minus infinity on one genuine full-measure set for every scalar drift
  parameter. No tail-growth or excursion-return interface is assumed.
- `MeasurableMovingPointCounts` proves joint Borel measurability of moving
  cell counts in actual finite point measures.
  `BrownianClippedExcursionMovingCounts` applies it to the literal retained
  component cells. `BrownianClippedSpatialJointMarkLaw` identifies the
  entire rational count family jointly with the actual Brownian path and
  the original Gaussian source, by integrating the proved per-path law.
  The joint identity is still clipped; it is not a full-time density claim.
- `FiniteIrreducibleCriticalEnumerationNormalization` supplies literal
  factorial-divided Gaussian enumeration using actual finite
  Perron--Wright and Stirling results.
  `FiniteIrreducibleCriticalTuplePrefactor` proves the common prefactor
  relative limit for every integer size in a fixed positive critical
  window and all bounded surplus vectors. Literal floors and varying real
  size coordinates are handled in `FiniteIrreducibleCriticalFloorPrefactor`.
  The physical scalar time is not clipped, and no B2 or primitivity
  condition is added. This proves the numerical prefactor, not the pending
  full deterministic residual expectation.

All Chapter 3 main results remain the objective. Unclipped excursion
realization, the literal Brownian--Wright density identity, deterministic
finite residual assembly, and constructive countable graph-limit transfers
are still tracked as required work; the goal is not marked complete.

### Native finite isolation and literal edge-odds correction

The next umbrella checkpoint passed 4726 jobs with zero diagnostics.
The refreshed full audit checked 1755 dependency outputs (plus two
axiom-free declarations), and the probability audit checked 731 (plus
one axiom-free declaration). Both had zero diagnostics and no unexpected
axioms.
The complete 96-declaration audit of the seven new numerical/averaging
leaves passed with only the three standard axioms, and the forbidden-source
scan remained empty.

- `FiniteIrreducibleNativeProfileAveraging` identifies the exact pooled
  type fibres with actual integer profile counts and proves native
  critical-time Pearson exponential averages at scale `A/n`. It also
  transfers the proved deterministic population correction to those
  literal connected-product laws.
- `FiniteIrreduciblePerronCountExpansion` retains every linear, quadratic,
  and cubic fluctuation term and proves the exact Perron cancellation.
  `FiniteIrreducibleIsolationBounds` dominates all remaining fluctuations
  on every actual count vector by `A*Pearson/n` plus an explicit vanishing
  remainder. `FiniteIrreducibleIsolationAveraging` therefore proves actual
  L1 convergence of the exponentiated isolation fluctuation to one. The
  native terminal derives its own positive law normalizers from finite
  enumeration; it does not assume a profile or uniform-integrability lemma.
- `FiniteIrreducibleOddsCorrectionBounds` covers all types and eligible
  graphs, including literal zero kernel entries. Actual eligible support
  and edge-count identities yield a uniform critical-size odds bound.
  `FiniteIrreducibleOddsCorrectionMoments` proves its actual L1 and mean
  convergence, and `FiniteIrreducibleOddsCorrectionTerminal` supplies
  complete integer-window/raw-time instances and genuine finite-tail laws
  without a supplied positive-normalizer hypothesis.

These are separate proved factors, not an assumed theorem about their
product. The complete raw residual expectation and its final deterministic
finite density assembly are still required. All finite results above retain
literal irreducibility without B2 or a primitivity restriction.

### Deterministic finite local-main and full excursion marking

The next umbrella checkpoint passed 4749 jobs with zero diagnostics.
The full audit checked 2031 dependency outputs plus two axiom-free
declarations; the probability audit checked 1007 plus one axiom-free
declaration. The complete new-slice audit checked 276 public definitions
and theorems. All three audits exited cleanly with no unexpected axioms,
and the forbidden-source scan was empty. Dependencies are restricted to
`propext`, `Classical.choice`, and `Quot.sound`.

- `FiniteIrreducibleResidualNormalization` identifies the exact entire
  raw residual exponent on the literal pooled type fibres. The native
  Pearson exponential bound controls its almost-everywhere joint
  remainder, including the genuine zero-safe edge odds.
  `FiniteIrreducibleRawResidualUniform` proves actual joint normalized
  residual L1 and mean convergence uniformly over the whole critical
  integer window. Normalizer positivity is derived internally from finite
  enumeration, not supplied as a main theorem interface.
- `FiniteIrreducibleFactorialMainIdentity` gives the exact main exponential
  normalization of the paper density. Numerical prefactor convergence and
  literal-floor continuity estimates supply a common threshold for all
  bounded surplus vectors and all sizes in a positive bounded window.
- `FiniteIrreducibleLocalMainIdentity` factors the true deterministic
  independent-edge component factorial expectation, with the types held
  fixed. `FiniteIrreducibleLocalMainTerminal.eventually_uniform_paper_floor_factorial_density`
  closes the finite branch of Chapter 3 local-main part (i), directly at
  raw paper time and actual floor sizes. It allows every actual assignment
  with bounded O(1) fibre-count discrepancy from `n mu`, and retains
  literal irreducibility, including periodic/bipartite models. Directed
  ambient-size and varying-size corollaries are also proved.
- The full-horizon excursion components have finite genuine endpoints,
  zero at both endpoints, a measurable nonrepeating rational section, and
  measurable actual component-integral areas. The actual Brownian drift
  theorem discharges these properties on one full set for every drift
  parameter and anchor. Full areas agree exactly with all sufficiently
  large windows for any fixed finite set of anchors.
- `BrownianFullHorizonPoissonMarks`, `BrownianFullHorizonMarkJointLaw`
  and `BrownianFullHorizonMarkMoments` construct the full-area conditional
  countable Poisson law and actual Gaussian-source/path joint laws,
  preserving the real continuous Brownian driver. Inactive and duplicate
  anchors have zero counts. All finite conditional mixed factorial
  moments are proved, as is exact eventual finite-coordinate agreement
  with clipped-window mark laws; whole infinite mark-law equality at a
  single finite window is not asserted.
- `CountableProductProbabilityKernel` proves measurable infinite products
  of actual Markov kernels using genuine finite generating cylinders.
  `BrownianFullHorizonSpatialKernel`, `SpatialIntensity`, and
  `SpatialSupport` use actual independent unit-strip atom laws to build
  the full spatial sampler. Its summed random measure is measurable,
  almost surely sigma-finite and finite on upper bounded time sets; its
  exact conditional first intensity is unit planar measure restricted to
  the entire reflected under-graph. Complete Poisson/count and moving-cell
  identification remain separate pending work.

The fixed-size factorial-asymptotic part is now complete in both model
branches. The full Chapter 3 goal remains active: the Brownian--Wright
factorial-density identity, the remaining finite process/marked limits,
and constructive countable graph-limit terminals are still required.

### Deterministic marked process, full spatial counts and finite-support bridges

The umbrella checkpoint passed 4783 jobs with zero diagnostics. The full
audit checked 2265 dependency outputs plus two axiom-free declarations;
the probability audit checked 1241 plus one axiom-free declaration. The
complete new-slice audit checked 234 public declarations. All audits
exited cleanly, only the three standard axioms occurred, and the forbidden
source scan was empty.

- Actual deterministic marked factorial expectations converge uniformly
  for every continuous coupled empirical-mark test. Exact floor-cell
  integration yields all genuine marked window moments. Expected total
  mark deviation tends to zero, so every actual window component has its
  mark in any prescribed Perron weak neighborhood with probability
  tending to one.
- Actual fixed-assignment unmarked windows have all factorial moment
  limits, a unique component-number law limit, and tight point laws.
  Compatible compact chart laws construct genuine global vague weak
  subsequences. Actual marked chart laws are tight too; the proved global
  coupled-test transfer identifies every actual unmarked weak subsequence
  with its constant-Perron marked law along the same indices. This is not
  yet a claim of full spatial uniqueness.
- Independent full-time spatial atoms have the proved Poisson law on
  disjoint bounded Borel cells. The literal complete excursion-cell count
  family, jointly with the actual Brownian source, equals the full-area
  conditional mark law. Measurable bounded-time NNReal tests have the
  exact Poisson Laplace functional; all relevant random integrals are
  proved almost surely finite, and path/source joint formulas agree
  exactly with bounded spatial samplers.
- Actual retained countable supports construct critical finite models
  without a supplied finite-model criticality premise. Their actual
  Perron functions, second/third moments and embedded probability marks
  agree with the existing countable finite-law constructions. Their
  exact graph hazards are the paper's spectral-normalized hazards.
  The empirical assignment has exactly its actual empirical weights,
  and gives a critical finite model at every positive-count index.

The literal Brownian--Wright density identity, the remaining full spatial
uniqueness and constructive countable graph-limit transfer are still
required for completion of every Chapter 3 main result.

### Full finite spatial limits, varying time and actual countable interfaces

This newer umbrella checkpoint passed 4827 jobs with zero diagnostics.
The full audit checked 2529 dependency outputs plus three axiom-free
declarations; the probability audit checked 1505 plus two axiom-free
declarations. The complete new-slice audit checked 499 public declarations.
All three audits exited cleanly, only `propext`, `Classical.choice` and
`Quot.sound` occurred, and the forbidden proof-source scan was empty.

- Actual fixed finite unmarked and empirical-marked point laws now have
  unique full-sequence weak limits on every positive-size window and on
  the genuine global vague-Borel space. Literal size multiplication by
  `beta^(1/3)` preserves surplus and empirical marks and gives the exact
  starred laws and factorial-density Jacobian. This supersedes the earlier
  subsequence-only checkpoint; Brownian identification is still separate.
- Actual raw times with converging critical parameters have uniform
  full-window marked and unmarked factorial asymptotics, allowing arbitrary
  O(1) counts, assignments, floors and diverging size subsequences.
- The entire actual normalized countable independent-edge law equals its
  empirical critical finite-model graph law. Actual component marks are
  exact probability-measure pushforwards, and finite weak marks embed
  continuously into the genuine countable atomic-variation metric.
  The unnormalized law has the exact effective-parameter identity; the
  stated empirical spectral drift gives the `lambda + theta` shift at the
  actual `n+1`-vertex indexing.
- One positive-count actual realization can satisfy countably many proved
  eventual fixed-support refinements while retaining population variation,
  growing support and the scaled minimum-count condition. This constructive
  selection theorem is not itself the growing-support graph-limit theorem.
- Actual Gaussian fourth moments and dyadic chaining prove sublinear
  Brownian growth. Simultaneously for every drift and positive cutoff,
  complete long excursions lie in a bounded horizon and form a finite
  family, on one full-probability source set. Actual pinned Brownian bridges
  have the proved covariance, whole-process endpoint independence, finite
  Gaussian test laws and genuine exponential tilt measures. These are
  proved prerequisites, not an assumed positive-excursion area law.

The main goal remains active. The literal Brownian--Wright factorial
density identity, identification of the graph limits with that Brownian
law, and constructive growing-support graph-limit terminals are still
required to finish every Chapter 3 main result.

### Actual full Brownian process law, bridge area and fixed-support source limits

The latest complete umbrella build passed **4846 jobs with zero
diagnostics**. The full axiom audit checked 2715 dependency outputs plus
three axiom-free declarations; the probability audit checked 1691 plus
two axiom-free declarations. The new-slice audit checked all **685
distinct public declarations**. All three audits exited cleanly; the
only axioms were `propext`, `Classical.choice` and `Quot.sound`. The
repository-wide forbidden proof-word scan was empty.

- `BrownianExcursionPointProcessLaw` constructs the actual full
  Brownian size/surplus law in the existing vague-Borel point space.
  Under the original Gaussian joint source, its exceptional gate
  disappears almost surely, leaving the literal complete-excursion
  Dirac sum. `BrownianExcursionSpatialPointProcess` proves that actual
  full component-cell spatial Poisson counts realize precisely that
  law. `BrownianExcursionCompactWindows` proves every genuine compact
  window equals the global restriction as a finite weak-Borel point
  law. The process construction is complete; its Wright factorial
  density is not yet identified.
- `BrownianPinnedBridgeArea` proves the literal signed continuous
  bridge integral has Gaussian law with variance `T^3/12`, independently
  of the endpoint. Its variance is calculated from actual finite
  quadratures. `BrownianPinnedBridgeAreaTilt` proves the actual weighted
  path probability and the tilted area law for every real parameter.
  A signed bridge area is not identified with a positive-excursion area.
- `CountableVariationTopology` identifies the actual probability-mass
  encoding range with the closed positive unit simplex in real ell-one.
  It proves completeness, a countable dense span and Polishness, with
  the existing genuine atomic-variation metric unchanged. This does not
  assert compactness or local compactness of the countable mark space.
- `CountableFixedSupportRawTerminal` proves the actual fixed-truncation
  empirical-normalized graph factorial limits on the entire positive
  size window, with literal floors and finite surplus, including actual
  natural-type TV marks. Rounding has proved O(1/n) population error and
  vanishing critical-scale spectral drift. Equality of whole graph laws
  gives the genuine effective finite parameter converging to lambda.
  `CountableFixedSupportApproximation` also proves that retained spectral
  roots, alpha/beta, actual TV Perron marks and their literal density
  targets approach the original countable model.

Work is continuing on the actual growing-support local diagonal and
marked process transfer, and on the Brownian excursion/Palm/factorial
density identification. These remaining results are not replaced by
unproved nontrivial interfaces, and the all-Chapter-3 goal is not marked
complete.

### Actual growing-support local endpoints and literal TV window laws

The complete umbrella build passed **4864 jobs with zero diagnostics**.
The full audit checked 2845 dependency outputs plus three axiom-free
declarations; the probability audit checked 1821 plus two axiom-free
declarations. The new-slice audit checked all **815 distinct public
declarations**, including this checkpoint's 130 new public declarations.
All three audits exited cleanly with only the standard three axioms;
the repository-wide forbidden proof-word scan was empty.

- `CountableFixedSupportGrowingTerminal.exists_actual_growing_paper_local_main`
  constructs one actual exhaustive monotone support and literal positive
  integer counts. It proves every fixed-order floor local factorial
  formula for the original countable alpha/beta density, uniformly on
  each bounded parameter interval and positive size/bounded-surplus box.
  The same actual population measures have vanishing atomic variation
  and the paper's scaled minimum population condition.
- `CountableUnnormalizedLocalTerminal` proves the unnormalized local
  formula for that same realization whenever the actual empirical
  critical-scale spectral drift exists as required in the paper. Its
  parameter is exactly `lambda+theta`; the entire source graph law,
  rather than an edge marginal, is reparameterized.
- `CountableComponentWindowLaw` and `CountableFixedSupportWindowLaw`
  prove exact whole-law identities for actual empirical TV-marked windows.
  `FiniteVariationWindowLawLimit` proves their fixed finite-model
  full-sequence window convergence to literal constant Perron marking.
  Neither compactness nor local compactness of the countable TV mark
  space is asserted.
- `BrownianExcursionTuplePoissonWeights` proves every-order conditional
  independent complete-area Poisson weights and their actual-source
  nonnegative Tonelli formulas. `BrownianExcursionCampbellWeights` proves
  the genuine compact point-law first-moment Campbell identity.
  `BrownianBridgeAreaTiltPathLaw` identifies the full continuous bridge
  area tilt with the literal pinned parabolic driver, not with a
  positivity-conditioned excursion.

The growing-support unmarked/marked process limits, Brownian identification
of the graph limits, and the literal positive-excursion/Wright factorial
density identity remain required. This checkpoint completes the local
factorial parts of the two countable theorems, not all of Chapter 3.

### Actual growing window counts, TV profiles, and Brownian cyclic geometry

The complete umbrella build passed **4886 jobs with zero diagnostics**,
including a second build verification. This checkpoint integrates 22 new
proof modules and 184 public declarations. All three audits passed:
3027 dependency outputs plus five axiom-free declarations in the full
audit; 2003 plus four axiom-free declarations in the probability audit;
and all **999 distinct public declarations** (996 dependency outputs plus
three axiom-free declarations) in the new-slice audit. Only the standard
three axioms occur. The repository proof-word scan was empty.

- `GraphWindowSource` proves exact actual graph/window-law integral
  identities and genuine full-floor-cell integrals for arbitrary graph
  probability laws with `n+1` vertices. `GraphWindowFactorialLimits` proves
  their all-order window factorial moment limits, unique component-number
  weak limit, and actual point-law tightness from the precise numeric local
  formula. These composition premises are discharged in the countable
  model terminal, not assumed as new main-theorem interfaces.
- `CountableWindowCountLimit.exists_actual_growing_window_count_limits`
  proves normalized and unnormalized window component-number limits and
  point-law tightness for one actual positive integer realization. The
  unnormalized parameter is exactly `lambda+theta` under the actual
  empirical critical-scale spectral drift. This very same realization
  also has whole-window TV distance and intrinsic bad-mark probability
  tending to zero at the original countable Perron mark.
- `CountableTVWindowTerminal` derives the TV conclusions from genuine
  conjoined unmarked/marked requirements. An exact finite integer-window
  sum gives the whole-window distance bound; the intrinsic weak-Borel
  bad-point event equals the true graph component event and obeys the
  actual Markov bound. The variation mark space is not assumed compact.
- `BrownianExcursionRectangleFactorials` and
  `BrownianExcursionMixedCountFactorials` identify every-order intrinsic
  factorial counts, including different overlapping size windows and
  repeated surplus labels, with the original Gaussian source's complete
  excursion Poisson area weights. The expectation is a nonnegative
  extended integral; finiteness and Wright-density identification are
  not asserted without proof.
- `BrownianBridgeCyclicPathLaw` proves actual full continuous pinned-bridge
  cyclic invariance from finite Gaussian laws and projective uniqueness.
  `BrownianBridgeCyclicGeometry` and `BrownianBridgeCyclicArea` prove the
  literal modulo splice, joint measurability, minimum-shift nonnegativity,
  and exact signed-area-minus-minimum identity. A signed bridge is not
  substituted for a positivity-conditioned excursion.

Full spatial growing-support unmarked/TV-marked process convergence,
Brownian identification of the graph limits, and the positive-excursion
area/Wright/Aldous factorial density identities still require proofs.
Window-number convergence alone is not counted as full process convergence.
The all-Chapter-3 goal remains active and is not marked complete.

## Verified full spatial and bridge-minimum checkpoint (4,922 build jobs)

The official umbrella build completes with zero errors and warnings.
The full, probability and finite-process/spatial/bridge audits check
3,348, 2,323 and 1,315 distinct public declarations respectively.
This checkpoint adds 36 proof leaves and 316 public declarations to
the prior 4,886-job checkpoint. Every audited declaration is axiom-free
or depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The proof-source forbidden-placeholder scan has no matches.

- `GraphWindowWeightedIntegral`, `GraphWindowCellFactorials`,
  `GraphWindowBoundary`, `GraphWindowSpatialLimit` and
  `GraphWindowDensityMoments` prove literal weighted floor sums, joint
  cell-count laws, boundary nullity, unique full weak spatial window
  limits, and the actual limit's density mixed factorial moments.
- `GraphGlobalSpatialLimit` uses true compatible finite-window charts
  and continuous assembly to construct global subsequences. Laws of
  finite groups of compact-support tests identify all subsequences,
  proving unique full-sequence vague convergence of the actual source.
- `GraphWindowMarkTransfer` and `GraphWindowMarkedSpatialLimit` transport
  actual TV profile concentration to full-sequence empirical-marked
  window convergence, not just bounded-test convergence or a subsequence.
  The mark space is not assumed compact or locally compact.
- `CountableGlobalAndMarkedWindowLimit` selects just one exhaustive
  positive integer realization. It simultaneously retains full-population
  variation, scaled minimum population, every-order bounded-parameter
  local formulas, global unmarked convergence and all localized
  TV-marked weak limits. The same realization supplies the actual raw
  graph laws at `lambda+theta` under the stated actual spectral drift.
- Intrinsic finite point-measure factorial kernels and arbitrary coupled
  Borel tests retain all multiplicities and have the genuine full-area
  Poisson source identities. No Brownian density identity is assumed.
- The continuous bridge's actual earliest minimum and minimum-shift law
  are measurable. Whole-path Gaussian increment regression proves null
  ties on separated compact intervals; a countable rational cover proves
  the actual unique interior minimum. Its true shifted path is strictly
  positive everywhere inside the horizon, on a Borel probability-one set.
- `BrownianEndpointDriftTilt` proves the actual endpoint exponential
  density equals the full constant-drift path pushforward, via Gaussian
  finite laws and projective uniqueness, not a Cameron--Martin interface.

These are genuine checked advances, but the Brownian--Wright identity,
positive-excursion area identification and actual excursion Palm/deletion
formula are not yet proved. The goal of all Chapter 3 main results remains
active; a constructed unspecified limit is not called the Aldous law.

## Verified literal scaling and first-passage checkpoint (4,947 build jobs)

The complete umbrella build passed **4,947 jobs with zero errors or
warnings**. All three extended declaration audits passed:

- `Audit.lean`: **3,613** distinct checked declarations;
- `ProbabilityAudit.lean`: **2,588** distinct checked declarations;
- `Chapter3FiniteProcessSpatialBridgeAudit.lean`: **1,580** distinct
  checked declarations.

The only axiom dependencies were `propext`, `Classical.choice`, and
`Quot.sound`; axiom-free declarations are included in the counts. There
were no duplicate audit names. The proof-source forbidden-token scan
found no `sorry`, `admit`, `axiom`, or `opaque`. This checkpoint adds
61 proof modules and 581 audited public declarations relative to the
4,886-job checkpoint, including the preceding 4,922-job checkpoint.

- `CountableStarredGlobalSizeRescaling` implements the exact original
  beta^(1/3) proper size dilation of actual finite graph laws and their
  global limits, without redefining the source or assuming convergence.
- `CountableStarredTVWindowLimit` uses one actual growing integer
  realization for all previous population/local/global/profile bounds,
  the original starred global laws and every positive compact starred
  TV-marked window law. Marks stay the original empirical probabilities;
  the original Perron marking and raw `lambda+theta` shift are retained.
- `BrownianFirstPassageBridgeLaw` proves whole-path bridge/endpoint
  independence and exact finite-horizon first-passage survival integrals.
  `BrownianFirstPassageNegativeDrift` proves genuine finite downcrossing
  under negative drift from full-horizon sublinear Brownian growth.
- `BrownianBridgeMinimumAreaPositive` proves that the actual
  minimum-shift area is strictly positive almost surely. The five-module
  dilation chain proves the genuine bridge law's duration scaling and
  the exact T^(3/2) area-law scaling, not an assumed excursion scaling.
- `BrownianBridgeMinimumRotationLaw` proves actual minimum-time and
  minimum-shift-path equivariance and joint rotation invariance. A
  uniform minimum-time law and an independent product decomposition are
  still subsequent obligations.
- `BrownianFirstPassageReflection` proves law preservation by reflection
  at the actual first downcrossing capped at every finite horizon. Entire
  past/future path independence, finite-grid fiber invariance, mesh
  convergence and bounded-continuous-test dominated convergence are
  all proved; no stopping-time reflection or strong-Markov interface is
  assumed.
- `BrownianKilledGaussianAlgebra` proves the literal Gaussian density
  ratio and restricted Radon--Nikodym identity, plus the continuous
  bounded candidate survival factor. `BrownianBridgeSurvivalPointwise`
  proves monotonicity of the actual bridge probability and upgrades a
  continuous Gaussian-a.e. formula to every endpoint. These statements
  do not by themselves assert the killed Brownian kernel.

The Chapter 3 objective remains active. The main unfinished connection is
the actual positive-excursion/area--Wright identity and excursion Palm
deletion, hence the literal Aldous factorial density and identification
of all constructed process limits with the paper's Brownian law. No
unspecified limiting law is substituted for that named law.

## Verified actual killed laws and area moments checkpoint (4,966 build jobs)

The full umbrella build passed **4,966 jobs with zero errors or warnings**.
All three extended audits passed with no duplicate declaration names:

- `Audit.lean`: **3,814** distinct declarations;
- `ProbabilityAudit.lean`: **2,789** distinct declarations;
- `Chapter3FiniteProcessSpatialBridgeAudit.lean`: **1,781** distinct
  declarations.

Axiom-free declarations are included. The only dependencies are
`propext`, `Classical.choice`, and `Quot.sound`. The proof-source scan
found no `sorry`, `admit`, `axiom`, or `opaque`. This checkpoint adds
19 verified proof modules and 201 audited public declarations relative
to the 4,947-job checkpoint. New work not imported into the umbrella is
not included in this verified count.

- `BrownianKilledTransitionKernel` and `BrownianBridgeSurvivalLaw` prove
  the actual killed endpoint Gaussian difference density and the actual
  pinned bridge survival probability at every endpoint, including zero.
  Reflection, density uniqueness and the pointwise upgrade are proved;
  the candidate Gaussian algebra is no longer an assumed stochastic law.
- The five-leaf Haar/uniform-minimum chain proves that the actual minimum
  time is normalized Lebesgue-uniform and independent of the entire
  actual minimum-shift path. Both `pathLaw` and the true pinned bridge
  law have the exact joint product law, with arbitrary nonnegative Borel
  tests and literal interval probabilities.
- `BrownianPathExtremaTails` proves actual running-minimum and
  running-maximum Gaussian tails, an attained whole-interval norm
  supremum, and its bound `4 exp(-a^2/(2T))`. The same bound holds for
  actual whole forward-increment paths at every deterministic time.
- `BrownianKilledSemigroup` and `BrownianKilledSemigroupJointLaw` derive
  the actual killed kernel semigroup and full two-endpoint surviving
  joint kernel law from the proved entire past/future independence.
  Neither a strong-Markov nor a Chapman--Kolmogorov interface is assumed.
- The actual zero-endpoint bridge survival formula gives the literal
  minimum tail `exp(-2a^2/T)`. Layercake and Gaussian integrability give
  every exponential moment of the negative minimum. Young's inequality
  then proves every real exponential moment and all finite power moments
  of the genuine minimum-shift area, without assuming area/minimum
  independence. Actual Bochner moments scale with duration.
- `BrownianBridgeMinimumAreaFirstMoment` proves the genuine first area
  moment equals the unchanged `wrightConstant 1`. The reverse minimum
  time samples the shifted path under the proved uniform product law;
  Fubini and the actual Gaussian bridge area variance then prove
  `E[A_T^2] = 5 T^3 / 12`. `BrownianBridgeMinimumAreaSecondMoment`
  identifies `E[A_1^2]/2!` with the unchanged `wrightConstant 2`.
- The four-leaf cubic-compensation batch gives the actual ordered
  presentation and half-edge fibre counts, the factorial formula for
  **all** cubic configurations, and their linear recurrence. Every
  two-vertex cubic table is proved connected, so the actual first
  connected compensation sum is `5/24`, and the unchanged
  `wrightConstant 2` has that value. This is not a proof of the full
  connected nonlinear recurrence.

The exact complete Chapter 3 objective remains active. Outstanding links
are the full connected recurrence/all-order area--Wright identity,
actual positive-excursion conditioning, actual excursion Palm deletion,
and hence the literal Aldous factorial densities and the named Brownian
identification of the constructed finite/compact/countable graph limits.
All original model hypotheses and the original starred normalization
remain unchanged.

### Actual killed finite-dimensional laws and area kernel (4,982 jobs)

The complete umbrella builds cleanly with **4,982** jobs. This checkpoint
adds **16** verified proof modules and **192** audited public declarations
relative to 4,966 jobs. All three audits are clean and have no duplicate
targets:

- `Audit.lean`: **4,006** distinct declarations (16 axiom-free).
- `ProbabilityAudit.lean`: **2,981** (15 axiom-free).
- `Chapter3FiniteProcessSpatialBridgeAudit.lean`: **1,973** (14 axiom-free).

The remaining dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`. The proof-source forbidden-declaration scan is empty.

- The five-leaf `CubicConnectedComponent` chain cuts actual half-edge
  tables at the component containing a distinguished vertex, proves the
  inside support is connected and the outside support has no crossing
  edge, and reconstructs the original table bijectively. Its genuine
  finite sum/product factorization and the literal connected compensation
  sum are proved. Grouping by component size and the complete nonlinear
  connected recurrence are not inferred from this decomposition alone.
- `BrownianKilledFiniteDimensionalCoordinates`, `Law`, and `OrderedTimes`
  identify the actual whole-interval surviving Brownian endpoint tuple
  with the genuine iterated killed kernel chain. Every intermediate
  coordinate and the initial point are retained, time vectors may have
  repetitions, and arbitrary coupled nonnegative Borel tests are allowed.
  No finite-dimensional Markov formula is assumed.
- The positive-killed batch proves the actual shifted surviving endpoint
  law has density `phi_T(y-a)-phi_T(y+a)` above zero. For positive starts
  tending to zero, its true boundary density is `2 y phi_T(y)/T`, with
  dominated-convergence limits for bounded Borel compact-window tests.
  Nonpositive starts have zero actual law. The existing actual killed
  semigroup gives the literal Gaussian-density composition identity.
- `BrownianPositiveBridgeConditioning` constructs the actual pinned
  bridge conditioned to stay above `-a`, then translated by `a`. It proves
  the exact normalization `1-exp(-2a^2/T)`, probability mass one, strictly
  positive paths throughout the interval, and both endpoints equal `a`.
  It does not declare a small-start limit or a Vervaat identity.
- `BrownianKilledAreaGeometry`, `Kernel`, and `Semigroup` use the literal
  area above the killing boundary. Exact path-area addition and survival
  splitting give weight multiplication. Whole past/future independence
  proves the actual finite measurable area-weighted kernel semigroup for
  arbitrary nonnegative Borel endpoint tests and all nonnegative duration
  pairs. At zero area parameter it is exactly the genuine unweighted
  killed kernel. No Feynman--Kac, differential equation or stochastic
  composition formula is assumed.

The complete Chapter 3 objective is still active. These are actual new
dependencies, not a substitute for all-order area--Wright identification,
the conditioned-excursion/minimum-shift law identity, actual Palm deletion,
or the literal Brownian identification of the graph limit theorems.

### Literal connected recurrence and joint-time area calculus (4,989 jobs)

The latest complete umbrella passes **4,989** build jobs with zero errors
or warnings. This adds **7** proof modules and **63** audited public
declarations relative to 4,982 jobs, or **23** proof modules and **255**
public declarations relative to 4,966. Three complete audits are clean:

- `Audit.lean`: **4,069** distinct declarations, 17 axiom-free.
- `ProbabilityAudit.lean`: **3,044**, 16 axiom-free.
- `Chapter3FiniteProcessSpatialBridgeAudit.lean`: **2,036**, 15 axiom-free.

There are no duplicate audit targets, no nonstandard proof dependencies,
and no forbidden proof-source declarations. Only the standard logical
dependencies `propext`, `Classical.choice`, and `Quot.sound` occur.

The five-leaf connected recurrence batch transports the actual half-edge
degree fibres and support graphs under explicit relabelling equivalences,
counts root-containing vertex sets and unrestricted edge-label subsets,
and groups the actual root decomposition by its forced `2j` vertices and
`3j` edges. The empty outside remainder is retained. The genuine scalar
pointing convolution gives `A' = C' A`; the proved total-configuration
equation and nonzero `A` then give the connected Riccati equation. Its
coefficient recurrence is stated directly for the original finite
inverse-global-multiplicity sum:

`24(n+1)c(n+1) = 36n(n+1)c(n) + 36 sum_(i+j=n) (i c(i))(j c(j)) + 5 [n=0]`.

This is not a newly specified recursive coefficient sequence.
`wrightConstant_eq_literal_connectedCompensation` identifies the exact
Gamma-normalized original sum with the unchanged paper Wright constant.
The verified boundary coefficients are `c(0)=0`, `c(1)=5/24`, `c(2)=5/16`,
and `c(3)=1105/1152`. The complete connected combinatorial recurrence
obligation is therefore closed.

`BrownianKilledAreaDuhamelGeometry` proves joint time/path quadrature
continuity, actual path-area measurability, joint-time forward-path
continuity, joint time/state area and survival-weight measurability, and
the literal area derivative and exponential depletion formula by the
fundamental theorem of calculus. `BrownianKilledAreaTimeKernel` upgrades
the actual finite weighted endpoint law to a jointly measurable
duration/state kernel with mass at most one. These allow genuine
time-insertion calculations; no stochastic Duhamel or Kac identity is
supplied as a premise or declared proved merely from deterministic FTC.

Still required for the complete Chapter 3 objective: the actual Brownian
all-order area recurrence and Wright identity, the genuine conditioned
excursion/minimum-shift law identification, actual Palm deletion, literal
Aldous factorial densities, and the named Brownian identification of all
finite/regular-compact/countable graph limit terminals. The original
paper assumptions and starred normalization remain unchanged.

### Actual all-order killed-area insertion and positive-bridge density (5,005 jobs)

The complete umbrella passes **5,005** build jobs with zero errors or
warnings. This adds **16** proof modules and **144** audited public
declarations relative to 4,989 jobs. The three complete audits are clean:

- `Audit.lean`: **4,213** distinct declarations, 17 axiom-free.
- `ProbabilityAudit.lean`: **3,188**, 16 axiom-free.
- `Chapter3FiniteProcessSpatialBridgeAudit.lean`: **2,180**, 15 axiom-free.

There are no duplicate audit targets or nonstandard proof dependencies.
The proof-source forbidden-declaration scan is empty; only `propext`,
`Classical.choice` and `Quot.sound` occur in the audits.

- The three `BrownianKilledFiniteDimensional*Density` leaves identify
  the actual surviving Brownian free endpoint tuple at every finite
  strictly ordered time vector with the literal finite product of
  Gaussian-difference densities under product Lebesgue measure. The
  deterministic initial coordinate is omitted from the density, every
  intermediate and final endpoint is retained, and arbitrary coupled
  nonnegative Borel tests are permitted. The true nonpositive initial
  state and nonpositive intermediate coordinate zero branches are proved.
- The six `BrownianPositiveBridgeFiniteDimensional` leaves derive the
  actual positive pinned bridge's complete one-interior-coordinate law
  from the actual bridge/endpoint product and killed two-segment law.
  The exact density integrates to one. Its true small-positive-endpoint
  limit is the entrance-times-exit density divided by the quadratic
  normalization; bounded Borel compact-window tests converge by a proved
  Gaussian bound and dominated convergence. This is not yet a many-point
  or full-path limit, or a minimum-shift/excursion identification.
- The four `BrownianKilledAreaMoment` leaves define each actual moment
  measure by weighting the true Brownian surviving path law with the
  literal area power, then mapping the actual endpoint. The all-order
  insertion equation for these genuine measures is proved using a
  pathwise polynomial fundamental theorem, joint measurability, Tonelli
  and whole past/future independence. The formula uses the actual killed
  transition law and every nonnegative Borel endpoint test, including
  zero duration. Zeroth order is exactly the unweighted killed kernel;
  every positive-order zero-duration measure is zero. The measures are
  allowed to be infinite here; their finiteness is not assumed.
- `BrownianKilledAreaDuhamelInsertion`, `DuhamelPath` and `Duhamel`
  prove the actual stochastic exponential-area insertion equation.
  Both head and tail survival gates are retained in the path identity,
  and Tonelli converts it to an equation between the real area-weighted
  kernels. No Feynman--Kac, stochastic Kac/Duhamel, bridge Markov or
  finite-moment interface is supplied as a premise.

The all-order *killed-path* Kac dependency is closed. The complete
Chapter 3 objective remains active: genuine excursion conditioning and
minimum-shift identification, its all-order Wright area identity, actual
Palm deletion and Aldous factorial densities, and the named Brownian
identification of the graph limit terminals still require proofs.

### Actual finite moment densities and many-point bridge limits (5,026 jobs)

The complete umbrella passes **5,026** build jobs with zero errors or
warnings. Relative to the 5,005-job checkpoint, **21** proof modules and
**187** public declarations are added. The three complete audits pass:

- `Audit.lean`: **4,400** distinct declarations, 17 axiom-free.
- `ProbabilityAudit.lean`: **3,375**, 16 axiom-free.
- `Chapter3FiniteProcessSpatialBridgeAudit.lean`: **2,367**, 15 axiom-free.

There are no duplicate audit targets or nonstandard proof dependencies.
The proof-source forbidden-declaration scan is empty. Audits use only
`propext`, `Classical.choice` and `Quot.sound`.

- `BrownianKilledAreaParameter` proves the actual nonnegative-parameter
  Laplace-kernel setwise continuity and monotonicity, and controls its
  first-order depletion by the actual first surviving area moment.
- `BrownianKilledAreaMomentDensity` and `DensityLaw` construct the
  jointly measurable all-order time/state Gaussian-insertion densities
  and identify them with the original surviving Brownian path-area
  moment measures. The measure identity is proved from the actual Kac
  insertion and Tonelli, with no assumed density or finite-moment premise.
- The four `BrownianKilledAreaMomentFiniteness`/`RealKernel`/
  `RealRecursion`/`Boundary` leaves prove finite mass at every order,
  duration and state from the genuine Gaussian bridge/endpoint area
  decomposition. They prove the signed Bochner Kac formula for bounded
  real Borel tests, literal height insertion integrability, support
  above the boundary, zero law at a nonpositive boundary offset, and
  zero-duration positive-order cases.
- The three `BrownianKilledAreaScalingGeometry`/`MomentScaling`/
  `ExponentialScaling` leaves derive the exact genuine measure scaling
  from the already proved dilation invariance of the actual Brownian
  path law. Moments acquire the duration factor `c^(3*n/2)`; Laplace
  parameters change by `c^(3/2)`. Scaling requires `c > 0` and allows
  every duration, including zero; unit-time normalization requires
  positive duration.
- The five `BrownianPositiveBridgeMultiPoint` leaves identify the
  actual conditioned positive bridge's arbitrary finite ordered internal
  coordinate law with the literal entrance/interior/exit killed-kernel
  product divided by the actual bridge normalization. These genuine
  densities have mass one, permit arbitrary coupled Borel tests and
  vanish when any intermediate coordinate is nonpositive.
- `BrownianKilledDensityConvolution` derives pointwise actual density
  convolution from the true killed semigroup and finite endpoint-chain
  marginals. `MultiPointEntrance`, `MultiPointTests` and
  `MultiPointActualTests` prove literal small-endpoint density limits and
  arbitrary coupled bounded Borel compact-rectangle test limits for the
  actual bridge at every strictly ordered internal time vector. At this
  checkpoint, the limiting entrance product has finite mass at most one;
  full-space mass one and full-path convergence are separate obligations.
- The two `BrownianPositiveBridgeGaussianBounds`/`EnvelopeIntegrability`
  leaves prove global Gaussian-decaying entrance bounds and every
  polynomial envelope moment directly from the literal actual killed
  density. No uniform-integrability or tightness hypothesis is inserted.

All of these are dependencies toward the original Chapter 3 goal. The
genuine excursion/minimum-shift identification, all-order Wright area
identity, actual Palm deletion, Aldous factorial-density identity and
Brownian identification of graph-limit terminals are not yet claimed.

### Full-space internal-coordinate limits and actual Laplace jets (5,039 jobs)

The complete umbrella passes **5,039** build jobs with zero errors or
warnings. Relative to the 5,005-job checkpoint, **33** proof modules and
**270** public declarations have been added, together with one required
Mathlib dependency. The three complete audits pass:

- `Audit.lean`: **4,483** distinct declarations, 17 axiom-free.
- `ProbabilityAudit.lean`: **3,458**, 16 axiom-free.
- `Chapter3FiniteProcessSpatialBridgeAudit.lean`: **2,450**, 15 axiom-free.

There are no duplicate audit targets, source proof placeholders or
nonstandard mathematical axioms. All audit dependencies are confined to
`propext`, `Classical.choice` and `Quot.sound`.

- `BrownianKilledAreaLaplaceTaylorGeometry`, `LaplaceTaylor` and
  `LaplaceJets` prove the actual surviving-area Laplace kernel's
  all-order Taylor remainder bound, controlled by its next genuine area
  moment. For bounded real Borel endpoint tests they prove every-order
  right-hand polynomial jets and the actual right derivative at zero.
  Negative-parameter analyticity is not assumed or claimed.
- `BrownianKilledAreaMomentDensityBoundary` proves the literal all-order
  densities' boundary support and finite total mass using their already
  proved identity with genuine Brownian area moment measures.
- `BrownianEntranceConvolution` and `EntranceExitNormalization` derive
  the exact entrance convolution and normalization from the actual killed
  density convolution and dominated convergence. `MultiPointMass` proves
  that every strictly internal limiting entrance-product law has mass
  one. `MultiPointGlobalTests` proves the actual conditioned bridge's
  full-space convergence for arbitrary bounded coupled Borel tests,
  convergence on all Borel internal-coordinate sets, and literal density
  L1 convergence. This stronger Borel conclusion concerns strictly
  internal coordinates only: varying deterministic endpoints must be
  treated by continuous tests, not by a false setwise Dirac limit.
- The four `BrownianPositiveBridgeTwoPointKernelBounds`/
  `IncrementMoments`/`InteriorMarginal`/`InteriorKolmogorov` leaves prove
  common interior fourth-increment bounds, all interior marginal moments
  and Markov tails, and the genuine restricted Kolmogorov process bound.
  No endpoint modulus or full-path tightness premise is inserted.

The original all-Chapter-3 objective remains active. Endpoint control,
full-path conditioning/minimum-shift identification, the all-order
excursion-area/Wright identity, actual Palm deletion, the Aldous
factorial-density identity and named Brownian identification of the graph
limits remain to be proved.

### All-time area moments and actual conditioned scaling (5,049 jobs)

The complete umbrella passes **5,049** build jobs with zero errors or
warnings. Relative to the 5,039-job checkpoint, **9** proof modules and
**55** public declarations have been added, with one required Mathlib
dependency. All three complete audits pass: **4,538** distinct declarations
in `Audit.lean` (17 axiom-free), **3,513** in `ProbabilityAudit.lean` (16),
and **2,505** in `Chapter3FiniteProcessSpatialBridgeAudit.lean` (15).
There are no duplicate audit targets, source proof placeholders or
nonstandard mathematical axioms.

Actual Gaussian and killed-entrance moment estimates give common
positive-bridge coordinate moments on the entire closed time interval,
including its deterministic endpoints. Literal continuous-path Jensen
and Tonelli give every area moment a uniform finite bound; each
area-power tail vanishes uniformly as the endpoint approaches zero.
Whole conditioned positive-bridge path laws and their genuine area laws
have exact Brownian duration scaling, including arbitrary measurable
area tests and area-power/Laplace formulas. No conditioning-limit,
excursion or all-order Wright identity is inferred from these bounds.

### Genuine projective entrance law and dyadic regularity (5,054 jobs)

The complete umbrella passes **5,054** build jobs with zero errors or
warnings. Relative to the 5,049-job checkpoint, **5** proof modules and
**78** public declarations have been added. All three complete audits
pass: **4,616**, **3,591** and **2,583** distinct declarations respectively,
with unchanged axiom-free counts **17**, **16** and **15**. Duplicate
targets, nonstandard mathematical axioms and proof placeholders are absent.

`BrownianEntranceFiniteDimensionalFamily`, `ProjectiveFamily`,
`EndpointFamily` and `CountableLaw` prove finite-coordinate deletion
consistency and construct the actual countable probability law for
arbitrary sampling labels, including repeated or unordered times.
The endpoint extension has literal zero endpoints. Borel-test convergence
at endpoints applies to the explicitly zero-padded source; no false
setwise convergence of a varying Dirac endpoint is asserted.

`FourthMomentDyadicModulus` proves an explicit all-level bad-event bound
of order `R^-4`, geometric summability, Borel--Cantelli and an actual
continuous dyadic extension matching every sample from measurable
coordinates with their fourth-moment inequalities. Continuity is not
assumed. Applying this general result to the genuine entrance law, and
identifying its full-path excursion law, remain subsequent obligations.

### Endpoint-inclusive increments and genuine compact path sets (5,068 jobs)

The complete umbrella passes **5,068** build jobs with zero errors or
warnings. Relative to the 5,054-job checkpoint, **13** proof modules and
**83** public declarations have been added, with one required Mathlib
dependency. All three complete audits pass: **4,699**, **3,674** and
**2,666** distinct declarations, with axiom-free counts **17**, **16**
and **15**. Duplicate targets, nonstandard axioms and source proof
placeholders are absent.

The eleven genuine killed/positive-bridge moment leaves prove the
harmonic first moment, an inverse-square-root survival bound, centered
weighted Gaussian moments, and actual entrance/exit estimates reaching
both endpoints. Time reversal is derived from genuine finite path laws,
including its endpoint cases. The resulting common fourth-increment
bound holds for every pair of times in the full closed interval, with
a proved finite model-dependent coefficient. The literal evaluation
process has the corresponding common Kolmogorov condition.

`DyadicPathModulus` proves that dyadic approximation recovers each literal
continuous path, and derives a quantitative common modulus and pointwise
norm bounds from common neighbor bounds. `DyadicPathCompactGoodSet`
proves that the actual compact-open path space's closed initial-value/
dyadic-neighbor good sets are genuinely compact, by Arzela--Ascoli.
The actual stopped positive-bridge family tightness application and
continuous entrance realization are still subsequent steps; compact
good-set geometry alone is not called a path convergence theorem.

### Actual unbounded joint-coordinate moment limits (5,073 jobs)

The complete umbrella passes **5,073** build jobs with zero errors or
warnings. Relative to the 5,068-job checkpoint, **3** proof modules and
**49** public declarations have been added, with two required Mathlib
dependencies. All three complete audits pass: **4,748**, **3,723** and
**2,715** distinct declarations, with unchanged axiom-free counts
**17**, **16** and **15**. No duplicate targets, nonstandard mathematical
axioms or source proof placeholders occur.

`BrownianPositiveBridgeFiniteCoordinateMoments` derives actual uniform
high moments and explicit vanishing tails for arbitrary finite coordinate
vectors, monomials and finite-coefficient polynomials. Coordinate times
may include either endpoint for these source bounds.
`EntranceCoordinateMoments` proves finiteness and tail bounds for the
literal internal entrance law, by Fatou from actual density limits.
`JointMomentLimits` proves convergence of arbitrary polynomial-growth
Borel tests and genuine joint moments, using a weighted Cauchy--Schwarz
estimate on the actual density remainder. Its terminals include height
products, signed monomials, arbitrary powers of finite polynomials and
powers of the sum of absolute coordinates. Uniform integrability and
target moment finiteness are conclusions, not inserted interfaces.

The all-Chapter-3 objective remains active. Full path conditioning limits,
their minimum-shift/excursion identity, every-order Wright area identity,
actual Palm deletion, Aldous factorial densities and the named Brownian
identification of graph-limit terminals remain to be completed.

### A genuine continuous entrance path realization (5,078 jobs)

The complete umbrella passes **5,078** build jobs with zero errors or
warnings. Relative to the 5,073-job checkpoint, **5** proof modules and
**63** public declarations have been added. All three complete audits
pass: **4,811**, **3,786** and **2,778** distinct declarations, with
unchanged axiom-free counts **17**, **16** and **15**. Duplicate targets,
nonstandard axioms and source proof placeholders are absent.

`BrownianEntranceDyadicSamples` proves actual almost-sure compatibility
and equality of labels at the same clamped physical time. `MomentTransfer`
proves unbounded moment transfer by truncation and monotone convergence;
`PaddedIncrement` controls the genuine endpoint padding error and proves
that it vanishes. `DyadicMoments` discharges every actual full dyadic
fourth-moment bound from the endpoint-inclusive positive-bridge theorem.

`ContinuousRealization` constructs the continuous process, its genuine
compact-open Borel measurable Path representative and its probability
law. Its full countable sampling law equals the original constructed
entrance law exactly, and every sampled finite marginal is correct.
Zero endpoints and the entire zero stopped portion are actual almost-
everywhere conclusions. Moment bounds, `LocalBound`, compatibility and
continuity are proved, not extra hypotheses of the terminal.
This construction is not yet called the complete conditioning weak
limit, a minimum-shift/Vervaat identity or an Aldous density theorem.

### Genuine positive-bridge path tightness (5,081 jobs)

The complete umbrella passes **5,081** build jobs with zero errors or
warnings. Three new proof modules supply **27** public declarations.
All three full audits pass **4,838**, **3,813** and **2,805** distinct
declarations, with unchanged axiom-free counts **17**, **16** and **15**.
Duplicate targets and nonstandard axioms are absent.

`BrownianPositiveBridgeDyadicModulus` derives the actual adjacent dyadic
fourth moments and the all-level bad-path tail bound. `StoppedSupport`
proves that the actual conditioned path laws are stopped after the
horizon, and have uniformly bounded initial values for small endpoints.
`PathTightness` supplies a single positive endpoint range on which the
entire family of genuine path laws is tight: every positive error has
one common compact set controlling every endpoint in that range.
Neither tightness nor moment bounds are added as hypotheses.

The all-Chapter-3 objective remains active. Actual complete weak path
convergence, the minimum-shift/excursion identity, every-order Wright
area identity, Palm deletion, Aldous factorial densities and the named
Brownian identification of graph-limit terminals remain pending.

### Actual complete positive-bridge path convergence (5,093 jobs)

The complete umbrella passes **5,093** build jobs with zero errors or
warnings. Relative to 5,081, **11** proof modules and **99** public
declarations have been added, together with one additional Mathlib build
dependency. All three full audits pass **4,937**, **3,912** and **2,904**
distinct declarations. Axiom-free counts remain **17**, **16** and **15**;
duplicate targets, nonstandard axioms and source proof placeholders
are absent.

`BrownianEntranceStoppedSampling` proves actual density of the clamped
dyadic coordinates and their measurable embedding on the closed stopped
path set. `SamplingUniqueness` then proves equality of the literal Borel
path measures from their sampling laws, using subtype pullbacks rather
than treating finite-dimensional uniqueness as an assumed interface.

`BrownianPositiveBridgeWeakClusterSupport` passes actual stopped support
and zero limiting endpoints through weak convergence. Moving endpoint
Dirac measures are handled weakly, not by a false setwise or TV claim.
`WeakClusterMarginals` identifies every cluster's actual finite marginals
and full countable sampling law. `WeakCompactness` derives a true compact
weak closure from the proved tightness bounds. `PathConvergence` proves
the complete directed path weak limit as the positive endpoint tends to
zero, including literal bounded continuous real and ENN test integrals.

`BrownianPositiveBridgeAreaTimeMoments`, `AreaOrderedTimes` and
`AreaMomentLimits` prove the actual all-order area moment limits to the
literal sorted entrance-kernel time-cube integrals. The area-power
Tonelli identity, null repeated times and endpoints, target measurability
and every target moment's finiteness are proved, not hypotheses.
`ContinuousPathUniqueMinimumContinuity` and
`BrownianBridgeMinimumShiftContinuity` prove genuine selector continuity
at unique minima, joint cyclic-splice continuity and actual Brownian
almost-sure minimum-shift continuity.

The all-Chapter-3 goal remains active. Complete conditioning path
convergence is now proved; identification of this law with the Brownian
minimum-shift/excursion law is still required. The all-order Wright area
identity, actual Palm deletion, Aldous factorial densities and the named
Brownian identification of graph-limit terminals are not claimed yet.

### Actual entrance area law and bounded first-passage factorization (5,103 jobs)

The complete umbrella passes **5,103** build jobs with zero errors or
warnings. Relative to 5,093, **10** proof modules and **99** public
declarations have been integrated. The three full audits pass **5,036**,
**4,011** and **3,003** distinct declarations; the axiom-free counts remain
**17**, **16** and **15**. Duplicate targets, nonstandard axioms and source
proof placeholders are absent.

`ContinuousPathAreaContinuity` proves actual compact-open continuity of
the path area, jointly with its duration. `BrownianEntranceArbitraryTimeLaw`
and `OrderedTimeLaw` identify the true continuous entrance probability
law at arbitrary times, including repeated, unordered and endpoint
coordinates, and give its actual ordered entrance-kernel densities.
Whole-path nonnegativity is an almost-everywhere conclusion, not a
premise.

`WeakContinuousMomentIdentification` proves moment identification from
actual weak convergence and source square-moment bounds by truncation.
`BrownianPositiveBridgeAreaLawIdentification` discharges those bounds
and identifies every moment of the actual continuous entrance path and
its genuine area law with the finite entrance-kernel time-cube integral.
It also proves actual area-law weak convergence and vanishing moment
tails. `BrownianEntranceDurationScaling` and `AreaScaling` prove exact
whole-path and area-law duration scaling, arbitrary Borel test formulas,
integrability transport and the actual all-order kernel-moment scaling.

`BrownianFirstPassagePastFibers`, `GridStrongMarkov` and `StrongMarkov`
prove full past/future product laws at the actual finite grid passage
times and pass them to the literal capped first passage. Its entire
future path has the original Brownian law and is independent of the
passage time and stopped past. No strong-Markov property is assumed.

The all-Chapter-3 goal remains active. The minimum-shift/entrance identity,
the all-order Wright area identity, actual Palm deletion and the literal
Aldous factorial-density identity remain separate obligations. None is
inferred from the proved entrance-kernel moment formulas or duration
scaling. Brownian identification of the graph-limit terminals is pending.

### Actual uncapped passage, bridge conditioning and moment resolvents (5,114 jobs)

The complete umbrella passes **5,114** build jobs with zero errors or
warnings. Relative to 5,103, **11** proof modules and **112** public
declarations have been integrated. The full audits pass **5,148**,
**4,123** and **3,115** distinct declarations, with unchanged axiom-free
counts **17**, **16** and **15**. All remaining dependencies are the
standard three axioms only; duplicate targets and source proof
placeholders are absent.

`BrownianFirstPassageZeroDrift` proves actual negative-level passage
finiteness from the literal survival tail, as well as positivity and
exact hitting. `UncappedLaw` passes the actual capped laws to the true
passage by almost-everywhere weak image convergence. `StrongMarkovFull`
discharges finiteness: the entire future path has the original Brownian
law and is independent of the actual passage time and stopped past.
Its terminal has no strong-Markov or passage-finiteness premise.

`BrownianBridgeMinimumReconstruction` inverts the actual minimum cyclic
splice. `OccupationBias` proves that the positive bridge's minimum-shift
law is the true minimum-shift law weighted by normalized low-height
occupation, and proves its exact normalization and expected occupation.
`UniformSmallTime`, `TimeConditioning` and `TimeWeakLimit` prove the
actual pinned bridge conditioned on a small positive minimum time is an
inverse uniform-product splice and tends weakly to the true minimum-shift
law. This is distinct from negative-barrier conditioning; no Vervaat
identity is inferred.

`PositiveTimeConvolutionLaplace` proves the genuine time-quadrant change
of variables. `BrownianKilledAreaMomentResolvent` derives the actual
all-order height-insertion recurrence and Borel endpoint-test transforms
from actual moment densities. `BrownianEntranceAreaGammaTransform`
proves the genuine boundary heat normalization and finite Gamma duration
transform of every positive-order entrance-area moment. It does not
supply a formula for the unit moment or identify it with a Wright constant.

The full objective remains active: minimum-shift/entrance identification,
the all-order Wright area identity, actual Palm deletion and the literal
Aldous density theorem still require proof. The Brownian identification
of the graph-limit terminals is not counted as complete.

### Actual passage density, Laplace transform and finite moment mass (5,124 jobs)

The complete umbrella passes **5,124** build jobs with zero errors or
warnings. Relative to 5,114, **10** proof modules and **95** public
declarations have been integrated. The three full audits pass **5,243**,
**4,218** and **3,210** distinct declarations; axiom-free counts remain
**17**, **16** and **15**. Duplicate targets, nonstandard axioms and source
proof placeholders are absent.

`BrownianFirstPassageDistribution`, `DensityGeometry` and `DensityLaw`
identify the complete Borel law of the actual negative-level passage with
its genuine Gaussian hitting density. The reflection CDF, one-dimensional
Jacobian, density integrals and total probability are proved. `Exponential`
and `Laplace` derive the actual capped exponential normalization and true
uncapped passage transform from whole-future independence, Gaussian mgfs
and dominated convergence. No optional-stopping or transform interface
is supplied.

`BrownianRawAreaMomentBounds` proves exact raw-area duration scaling and
polynomial bounds for every actual shifted surviving moment measure.
`BrownianKilledAreaResolventMassBounds` proves finite total state mass
of every positive-duration-Laplace killed-area moment resolvent by actual
Gamma integrability. This does not yet assert pointwise finiteness.

`BrownianFirstPassageEndpointGeometry` reconstructs the actual later
endpoint and identifies its genuine future Gaussian law.
`MinimumApproximation` proves that first hits of levels approaching the
minimum from above converge to the actual earliest minimizer, without a
minimum-uniqueness premise. `ContinuousPathMinimumBandAverage` passes this
actual limit through normalized height-band averages and finite path
measures using a proved common bounded-test estimate.

The full objective remains active. Minimum-shift/entrance identification,
the all-order Wright area identity, Palm deletion, the literal Aldous
factorial densities and Brownian identification of the graph-limit
terminals are not claimed from these dependencies.

### Actual minimum-window disintegration and killed Green kernel (5,141 jobs)

The complete umbrella passes **5,141** build jobs. Relative to 5,124,
**17** proof modules and **98** public declarations have been integrated.
The three full audits pass **5,341**, **4,316** and **3,308** distinct
declarations, with no duplicate targets, nonstandard axioms, errors or
warnings. Their axiom-free counts remain **17**, **16** and **15**.
The forbidden-proof source scan is empty.

The true passage time at successive negative depths has its actual
additive product law and Borel density convolution. Finite-time reversal
is proved to preserve the entire Brownian path law; together with actual
minimum negativity it places the true earliest minimizer in the interior.
First-passage/minimum-depth-window disintegration retains the whole future
path, and level/path Tonelli gives the actual hitting-density formulas.
Bounded continuous band tests converge to the entire future at the actual
earliest minimizer, without a minimum-uniqueness or weak-limit premise.

The true Gaussian heat duration transform is evaluated from the actual
passage Laplace law. Thus the zeroth killed moment duration resolvent has
its exact absorbing-zero Green formula, including its zero-state cases.
This checkpoint does not infer the all-order Wright area identity or the
full Aldous factorial densities from these proved dependencies.

### Actual minimum-window convergence and all-order boundary control (5,150 jobs)

The complete umbrella passes **5,150** build jobs. Relative to 5,141,
**9** proof modules and **69** public declarations have been integrated.
The three full audits pass **5,410**, **4,385** and **3,377** distinct
declarations, with no duplicate targets, nonstandard axioms, errors or
warnings. Their axiom-free counts remain **17**, **16** and **15**.

Every actual killed-area duration resolvent is now finite pointwise and
integrable in each state. Its boundary slope is a genuine dominated
convergence limit, and its exponentially weighted state-total masses are
finite at every order. Actual minimum-depth windows have proved global
survival domination and converge against bounded continuous tests to the
whole future at the actual earliest minimum. No minimum-uniqueness,
entrance-law identification or boundary-exchange assumption is added.

The all-order Wright identity, Palm deletion, literal Aldous densities
and Brownian identification of the graph-limit terminals remain pending.

### Genuine killed free-coordinate entrance and polynomial Green response (5,164 jobs)

The complete umbrella passes **5,164** build jobs. Relative to 5,150,
**13** proof modules and **83** public declarations have been integrated.
The three full audits pass **5,493**, **4,468** and **3,460** distinct
declarations, with no duplicate targets, nonstandard axioms, errors or
warnings. Their axiom-free counts remain **17**, **16** and **15**.

Actual killed paths have a genuine one-boundary finite-coordinate entrance
limit for arbitrary positive strictly ordered sampling times, including
the survival terminal and the literal unshifted coordinates. The proof
uses a globally integrable Gaussian envelope and true remaining-chain
mass at most one, not a finite-dimensional or path-limit hypothesis.
Actual minimum-window convergence has its literal nonnegative
first-passage-density representation for the whole future.

Every exponentially weighted monomial and polynomial has its evaluated
actual killed Green integral. The true all-order resolvent boundary
response is identified with a literal polynomial, whose differential
equation and zero-boundary condition are proved. The entrance kernel's
duration Laplace transform follows from the genuine passage-time law.
The all-order Wright identification and full Brownian/Aldous terminals
are still pending.

### Actual minimum triple density and Wright boundary recurrence (5,179 jobs)

The complete umbrella passes **5,179** build jobs. Relative to 5,164,
**15** proof modules and **82** public declarations have been integrated.
The three full audits pass **5,575**, **4,550** and **3,542** distinct
declarations, with no duplicate targets, nonstandard axioms, errors or
warnings. Their axiom-free counts remain **17**, **16** and **15**.

The actual earliest-minimum time, depth and endpoint displacement have
their joint Brownian density, proved from the genuine minimum-window
limits and killed entrance limit. The positive-level first-passage
density has its exact first moment. Sorting the actual area time cube
and the cumulative-gap change of variables preserve the true measures.
The all-order boundary polynomials have a proved formal-series Riccati
recurrence and transport identity, without an assumed Airy interface.

These dependencies do not yet complete the all-order stochastic Wright
identity, Palm deletion or the Brownian-identified Chapter 3 terminals.

### Literal Wright normalization and original observation coordinates (5,186 jobs)

The complete umbrella passes **5,186** build jobs. Relative to 5,179,
**7** proof modules and **49** public declarations have been integrated.
The three full audits pass **5,624**, **4,599** and **3,591** distinct
declarations, with no duplicate targets, nonstandard axioms, errors or
warnings. Their axiom-free counts remain **17**, **16** and **15**.

The actual boundary-polynomial slopes have the unchanged connected cubic
compensation coefficients and exact Gamma-normalized Wright constants.
The actual minimum-future coordinates retain the literal original
observation times and have their genuine residual-coordinate entrance
limit. Appending the duration to the ordered internal times and passing
to positive cumulative gaps have the exact Lebesgue integral identity.
No stochastic area identity is inferred from these scalar and measure
identities alone; Brownian/Aldous identification remains pending.

### Genuine entrance-product transforms and Borel minimum law (5,190 jobs)

The complete umbrella passes **5,190** build jobs. Relative to 5,186,
**4** proof modules and **55** public declarations have been integrated.
The three full audits pass **5,679**, **4,654** and **3,646** distinct
declarations, with no duplicate targets, nonstandard axioms, errors or
warnings. Their axiom-free counts remain **17**, **16** and **15**.

The actual minimum triple law now equals its numerical density measure
for every nonnegative Borel test. The real cumulative gap schedule gives
exactly the original finite killed schedule, including its constant
terminal extension. Jointly measurable entrance--interior--exit densities
have their precise raw numerators and genuine edgewise Laplace transforms;
positive-gap/state Tonelli works for arbitrary measurable state weights.
All-order area--Wright and full Brownian/Aldous identification remain
separate obligations.

### Actual area-time simplex and genuine bridge endpoint continuity (5,194 jobs)

The complete umbrella passes **5,194** build jobs. Relative to 5,190,
**4** proof modules and **29** public declarations have been integrated.
The three full audits pass **5,708**, **4,683** and **3,675** distinct
declarations, with no duplicate targets, nonstandard axioms, errors or
warnings. Their axiom-free counts remain **17**, **16** and **15**.

The literal entrance area moment equals factorial times its actual
ordered time-simplex integral. The genuine positive-gap change cancels
the density normalization and identifies the all-order duration Laplace
integral with the actual entrance/Green state chain. True stopped-bridge
minimum tests, retaining the whole future, are continuous as the genuine
reconstructed endpoint tends to zero; uniqueness of the actual bridge
minimum is proved rather than assumed. The exact passage--entrance
normalization is proved in both nonnegative and integrable real form.

The all-order stochastic Wright identity, Vervaat identification, Palm
deletion and literal Brownian-identified Chapter 3 terminals remain
pending at this checkpoint.

### Genuine all-order entrance area--Wright identity (5,197 jobs)

The complete umbrella passes **5,197** build jobs. Relative to 5,194,
**3** proof modules and **19** public declarations have been integrated.
The three full audits pass **5,727**, **4,702** and **3,694** distinct
declarations, with no duplicate targets, nonstandard axioms, errors or
warnings. Their axiom-free counts remain **17**, **16** and **15**.
The forbidden-proof source scan is empty.

The actual full Green state chain is identified with the genuine
all-order boundary slope by height-vector Tonelli and the proved Kac
recursion. Together with the actual area time-cube and duration transform,
this proves the entrance area moment divided by its factorial equals
the paper's literal Wright constant at every order, including zero.
The exact positive-duration formula is also proved. There is no assumed
area Laplace formula, Airy interface or redefined Wright constant.

Vervaat/minimum-shift identification, actual Palm deletion and literal
Aldous factorial densities remain pending. The full Chapter 3 goal is
active; these proved moments alone do not complete its Brownian terminals.

### Actual bridge endpoint pinning and passage boundary contraction (5,207 jobs)

The complete umbrella passes **5,207** build jobs. Relative to 5,197,
**10** proof modules and **72** public declarations have been integrated.
The three full audits pass **5,799**, **4,774** and **3,766** distinct
declarations, with no duplicate targets, nonstandard axioms, errors or
warnings. Their axiom-free counts remain **17**, **16** and **15**.
The forbidden-proof source scan is empty.

The actual Brownian minimum/time/depth/original-coordinate density now
retains arbitrary finite original observation times under the stated
deterministic time support. Actual bridge--Gaussian disintegration,
equality of endpoint-weighted Borel integrals and genuine endpoint
continuity give the endpoint-zero pinned bridge minimum density. No
conditional-distribution identity is imposed as a premise.

The level-weighted genuine first-passage source has its exact mass one
half, square-root scaling and concentration at zero. An actual uniform
killed-boundary bound holds at every positive depth, and the weighted
boundary contraction has its literal half-entrance limit. The actual
entrance kernel is jointly continuous at positive duration and has a
uniform envelope retaining Gaussian decay. Genuine positive-bridge area
even moments also have explicit factorial growth on one neighborhood
independent of the moment order, derived from the evaluated Gaussian
exponential-square integral.

The full minimum-shift/entrance path-law identification, actual Palm
deletion and literal Aldous factorial densities remain pending. The
Chapter 3 goal stays active, not completed by these analytic dependencies.

### Finite minimum-coordinate laws and actual area exponential control (5,215 jobs)

The complete umbrella passes **5,215** build jobs. Relative to 5,207,
**8** proof modules and **55** public declarations have been integrated.
The three full audits pass **5,854**, **4,829** and **3,821** distinct
declarations, with no duplicate targets, nonstandard axioms, errors or
warnings. Their axiom-free counts remain **17**, **16** and **15**.
The forbidden-proof source scan is empty.

Actual finite original-minimum coordinate measures agree with their literal
passage/entrance density measures for arbitrary nonnegative Borel tests
under the concrete time cutoff. The finite endpoint candidate has proved
continuity and finite Gaussian domination; actual bridge endpoint tests
retain all the original minimum and observation coordinates.

The actual positive-bridge areas have a uniform exponential-square bound,
proved from all-order factorial growth and the actual exponential series.
This bound transfers to the constructed entrance path law by genuine weak
convergence. Continuous integral transfer under a proved square bound,
normalized right-hand time averaging, and a concrete continuous time cutoff
are also proved, without an assumed limiting-law identity.

The minimum-shift/entrance path-law identification, actual Palm deletion and
literal Aldous factorial densities remain pending. This checkpoint does not
claim that every Chapter 3 probability terminal has been completed.

### Actual small-minimum finite-dimensional entrance limits (5,227 jobs)

The complete umbrella passes **5,227** build jobs. Relative to 5,215,
**12** proof modules and **91** public declarations have been integrated.
The three full audits pass **5,945**, **4,920** and **3,912** distinct
declarations, with no duplicate targets, nonstandard axioms, errors or
warnings. Their axiom-free counts remain **17**, **16** and **15**.
The forbidden-proof source scan is empty.

The actual pinned minimum-coordinate law has its arbitrary Borel density.
The true small-minimum-time event is reconciled with the earliest minimum
selector, and its exact conditioning normalization is proved. Passage
boundary contraction and right-hand time averaging now give the actual
conditioned bridge's complete ordered finite-dimensional entrance limit,
with the literal entrance density and no assumed finite-dimensional law.

Actual positive-bridge path and area exponential tilts converge weakly to
the entrance tilts for every real tilt parameter. The entrance-area moment
generating function is the convergent series of the unchanged enumerative
Wright constants, including negative real arguments. The actual parabolic
score, variance polynomial, and bridge/endpoint factorization are also
proved algebraically on genuine continuous paths.

The complete minimum-shift/entrance path-law identification, actual Palm
deletion and literal Aldous factorial densities are still separate
obligations at this verified umbrella checkpoint.

### Genuine minimum-shift/Wright identification and parabolic path laws (5,235 jobs)

The complete umbrella passes **5,235** build jobs. Relative to 5,227,
**8** proof modules and **62** public declarations have been integrated.
The three full audits pass **6,007**, **4,982** and **3,974** distinct
declarations, with no duplicate targets, nonstandard axioms, errors or
warnings. Their axiom-free counts remain **17**, **16** and **15**.
The forbidden-proof source scan is empty.

The actual cyclic minimum transform of the pinned Brownian bridge has
exactly the entrance continuous-path law in the compact-open Borel space.
The proof combines the actual conditioned bridge's finite-dimensional
limit with its genuine whole-path weak limit and measurable sampling
uniqueness; no finite-dimensional or path-law identification is assumed.
Consequently, actual positive-endpoint bridges converge to this same
minimum-shift law, and the true minimum time has its uniform product law
with the identified excursion.

Every area power moment of this actual excursion is
`E[A_T^r] = (T^(3/2))^r * r! * w_r`, with the unchanged connected cubic
Wright constant. Its exponential moment is the convergent Wright series
for every real parameter. Multiplying the literal full-area Poisson weight
by the area exponential leaves exactly `(T^(3/2))^r * w_r`; the actual
area exponential tilt is a probability measure.

The actual stopped parabolic Brownian law now has its literal exponential
Radon--Nikodym formula, proved from the independent true bridge and endpoint
tilts, not from a Girsanov assumption. The killed endpoint law and literal
full-driver first-passage survival event have their actual constrained
bridge area-weighted Gaussian/Lebesgue densities. The drift energy equals
twice the homogeneous factorial exponent, whose deletion cocycle proves
the exact residual-parameter density factorization.

Genuine reflected excursion time occupation has its countable component
section formula. Actual Brownian growth discharges component finiteness;
Tonelli gives the length-weighted Campbell exchange and inverse length
recovers the unweighted sum, without a finite-first-moment assumption.

Actual random-excursion Palm deletion and the literal Aldous factorial
density are still pending. Identification of the already constructed
finite, regular compact and countable graph limits with that literal
Brownian law therefore remains pending. The Chapter 3 goal stays active.

### Actual random-time paths and excursion deletion geometry (5,269 jobs)

The complete umbrella passes **5,269** build jobs. Relative to 5,235,
**34** proof modules and **236** public declarations have been integrated.
The three full audits pass **6,243**, **5,218** and **4,210** distinct
declarations. Their axiom-free counts are **17**, **16** and **15**;
all remaining dependencies use only the standard three logical axioms.
There are no duplicate targets, errors, warnings or forbidden proof
placeholders. The complete umbrella and all three audit readers are closed.

The actual parabolic hitting time is finite, and its whole raw Brownian
future is independent of its tagged stopped past. The proof passes through
causal dyadic grids and then removes the horizon cutoff. The shifted driver
future has the literal parameter `lambda - elapsedTime`, not a falsely
identified Brownian law. Arbitrary measurable parameter mixtures retain
the past parameter in these true whole-future product identities.

At every negative level the actual uncapped stopped driver law has its
literal exponential density relative to the actual Brownian stopped-past
law. Monotone cutoff convergence and genuine hitting finiteness prove this
without optional-stopping or uniform-integrability assumptions. The same
identity is proved under arbitrary independent parameter measures with
measurable drift and almost-everywhere negative levels.

Actual Brownian and parabolic compact-prefix minima are almost surely
unique: a diffuse independent Gaussian gap excludes ties on separated
intervals, and rational separation plus the genuine stopped density close
the proof. For every fixed positive anchor, the true excursion left
endpoint is its actual prefix minimum time; the right endpoint is the
anchor plus the first passage of the true shifted future driver.
Component finiteness and positivity are discharged by actual Brownian
and parabolic facts, not endpoint-law premises.

Deleting a true complete excursion preserves the remaining full lengths
and areas. Surviving rational representatives are reselected through the
proved component bijection, and all Poisson-marked tuple sums are preserved.
The actual marked-window first moment also has its inverse-length time
occupation formula. These geometric and occupation identities are not
counted as stochastic Palm deletion.

Actual full minimum windows now have their genuine whole past/future
first-passage integrals and limits. The actual depth/time marginal yields
the integrable inverse-square-root remaining-duration bound. Normalized
surviving Brownian measures have exact whole-path duration scaling and
literal relative-coordinate entrance limits.

The genuine probability source formed by rescaling the whole Brownian
future after the unit-prefix minimum is constructed in the actual path
Borel space. Its post-unit whole future is Brownian and independent of
its actual prefix, and its full law is their literal splice product.
Identification of its normalized entrance prefix, the full minimum-split
disintegration, actual Palm deletion and literal Aldous factorial densities
remain pending. The Brownian identification of the graph limits and the
complete Chapter 3 goal therefore remain unfinished.

### Normalized entrance prefix and whole surviving paths (5,275 jobs)

The complete umbrella passes **5,275** jobs. Six new proof modules and
**32** public declarations have been integrated since 5,269. The three
full audits pass **6,275**, **5,250** and **4,242** distinct declarations,
with axiom-free counts **17**, **16** and **15**, no duplicate targets,
errors or warnings, and only the standard three logical axioms otherwise.
The complete umbrella and all three full audit readers are closed; the
project scan finds no forbidden proof placeholders.

The actual unit minimum-future source has its normalized ordered-prefix
finite-dimensional law, including arbitrary nonnegative Borel tests.
The normalization is proved to be the literal entrance mass `sqrt(2/pi)`.
Normalized surviving Brownian measures have their whole-path product and
splice law with a genuinely fresh Brownian future, not an assumed whole
path weak limit. The true parabolic minimum-window formula retains the
actual stopped density and residual future parameter. Exact excursion
deletion density algebra and full-area Poisson cancellation are proved.

The finite candidate minimum-split measure is constructed and its
arbitrary Borel integral formula and finiteness are proved. Equality with
the actual full minimum-split law, stochastic Palm deletion, the literal
Aldous factorial densities and Brownian identification of the graph
limits remain unfinished. The complete Chapter 3 goal stays active.

### Genuine positive-time return and full tagged sampling (5,282 jobs)

The complete umbrella passes **5,282** jobs. Seven further proof modules
and **42** public declarations have been integrated since 5,275. Together
with that checkpoint, this continuation added **13** modules and **74**
public declarations relative to 5,269. The three full audits pass
**6,317**, **5,292** and **4,284** distinct declarations; their axiom-free
counts remain **17**, **16** and **15**. All other dependencies use only
the standard three logical axioms. There are no duplicate targets,
errors, warnings or forbidden proof placeholders. The complete umbrella
and all three full audit readers are closed.

The actual entrance source is strictly positive at every positive unit
prefix time. Its return time is the literal infimum of strictly positive
zero-sublevel times, not first passage at the initial zero. The true
post-unit Brownian future proves finite return, return after the unit
horizon and exact zero height. The positive-time hit set and return
infimum have their exact Brownian duration scaling, including infinity.
The actual unit endpoint has the literal Rayleigh density
`1_{x>0} x exp(-x^2/2)`.

The minimum-split candidate has actual mass one, proved independently of
the full candidate identity. Genuine normalized survivor limits cover
arbitrary repeated, unordered and post-horizon finite samples. The full
tagged past/minimum/future law is proved to be determined by these finite
bounded-continuous tests: its two actual continuous paths embed through
rational evaluations, with stopped time and minimum level retained.

Equality of the actual complete minimum-split law with the candidate,
the full positive-return density and conditioned excursion path law,
stochastic Palm deletion, literal Aldous factorial densities and Brownian
identification of the graph limits remain unfinished. The entire Chapter 3
goal remains active; these dependencies are not counted as completed main
theorems.

### Actual full minimum splitting and whole parabolic tilt (5,290 jobs)

The complete umbrella passes **5,290** jobs. Seven further proof modules
and **29** public declarations have been integrated since 5,282. The three
full audits pass **6,346**, **5,321** and **4,313** distinct declarations;
their axiom-free counts remain **17**, **16** and **15**. All other
dependencies use only the standard three logical axioms. There are no
duplicate targets, errors, warnings or forbidden proof placeholders, and
all complete-umbrella and full-audit readers are closed.

The genuine Brownian minimum-split law now equals the literal candidate
as a measure on two tagged whole continuous paths. The proof uses actual
joint finite-sampling limits and the proved whole-path uniqueness theorem,
not a conditional path-law assumption. Arbitrary Borel tests retain the
stopped past, minimum time and level and the full future, even beyond the
horizon; the entire original Brownian path has its source reconstruction
formula. The candidate's depth/time marginal has its actual passage-density
formula, and its time marginal is the arcsine density.

The actual entrance source's positive-time return has density
`1_{z>1}/(2*z*sqrt(z))`, proved from its true endpoint/first-passage mixture
and a genuine Gaussian square integral. A finite-horizon parabolic density
also has a whole-path lift at every horizon, including zero. This lift
keeps the literal residual drift `lambda-T` on the independent future;
no infinite-horizon Radon--Nikodym density is asserted.

The conditioned complete-excursion path law, stochastic Palm deletion,
literal Aldous factorial densities and Brownian identification of the graph
limits are still unfinished. The entire Chapter 3 goal remains active.

### Actual return-path products and parabolic minimum source (5,298 jobs)

The complete umbrella passes **5,298** jobs. Eight further modules and
**43** public declarations have been integrated since 5,290. The three
full audits pass **6,389**, **5,364** and **4,356** distinct declarations;
the axiom-free counts remain **17**, **16** and **15**. There are no
duplicate audit targets, errors, warnings, forbidden proof placeholders
or nonstandard axiom dependencies. All full-build/audit readers are closed.

The actual full positive-return stopped-past and remaining whole-future
law is a product with a fresh Brownian path. The literal return is globally
Borel, including zero and infinite values. The return at the actual
parabolic minimum equals the complete reflected component length, and
its stopped area is the full component area. Actual depth/time and time
marginals are now identified with their explicit passage and arcsine
densities. The parabolic full minimum-split source retains the physical
residual drift beyond the original horizon.

The actual killed-prefix/first-passage joint density and its exact terminal
entrance normalization are also proved. They do not by themselves identify
the entire completed excursion conditioned on its return time. That path-law
identity, stochastic Palm deletion, literal Aldous factorial densities and
Brownian identification of the graph limits remain unfinished.

### Actual complete-return sources and stopped observation strata (5,310 jobs)

The full umbrella passes **5,310** jobs. Twelve additional modules and
**70** public declarations have been integrated since 5,298. The three
full audits pass **6,459**, **5,434** and **4,426** distinct declarations;
their axiom-free counts remain **17**, **16** and **15**. All readers are
closed; there are no diagnostics, duplicate targets, forbidden placeholders
or nonstandard axiom dependencies.

The actual complete parabolic minimum source now retains the full returned
past, physical complete duration, complete area, and residual whole future.
Its remaining driver is the literal compensated deletion, not an assumed
path identity. Actual arbitrary ordered finite sampling tests determine the
whole tagged-path law. Measurable lifetime strata and genuine zero filling
handle observations at and beyond the literal first return. The complete
conditional excursion identity and stochastic Palm formula are not yet
counted as proved; the Chapter 3 goal remains active.

### Physical complete-return tilt and passage exchange (5,317 jobs)

The full umbrella passes **5,317** jobs. Seven more modules and **25**
public declarations have been integrated since 5,310. The three full
audits pass **6,484**, **5,459** and **4,451** distinct declarations,
with **17**, **16** and **15** axiom-free declarations respectively.
All readers are closed. There are no errors, warnings, duplicate audit
targets, nonstandard axioms or forbidden proof placeholders.

The density at the physical complete return is now proved using the true
post-prefix parabolic negative-level first passage, rather than replacing
the prefix density directly at a later zero-drift return. The complete
minimum source retains the whole stopped component and fresh residual
driver. Removing a fixed complete excursion changes the actual prefix
parameter from lambda to lambda minus its length by a proved stopped
Radon--Nikodym law. Literal time-window and negative-depth integration,
and extraction/reconstruction of arbitrary unit-split observation times,
are also proved. The complete tagged excursion law, stochastic Palm
identity and Brownian-identified Chapter 3 terminals remain pending.

### Actual complete stopped-excursion law and full-area size factor (5,326 jobs)

The full umbrella passes **5,326** jobs. Nine modules and **44** public
declarations have been integrated since 5,317. The three full audits pass
**6,528**, **5,503** and **4,495** distinct declarations; the axiom-free
counts remain **17**, **16** and **15**. All audit readers are closed.
There are no errors, warnings, duplicate targets, nonstandard axioms or
forbidden proof placeholders in this checkpoint.

The actual returned stopped path and physical duration now have their
complete joint entrance-mixture law, proved from literal lifetime strata
and arbitrary finite observations, including observations at and after
the physical first return. Its exact dilation gives every positive source
scale. The true complete-state Campbell source retains the entire deleted
driver, and inverse drift recovers the actual compensated Brownian noise.
The genuine full-area Poisson integral gives exactly the paper's unchanged
Wright size factor at every surplus. These are proved dependencies, not
assumed conditional shape or Palm identities.

The actual marked stochastic Palm deletion formula, literal Aldous
factorial densities, and Brownian identification of the graph limits are
still unfinished. The objective remains every Chapter 3 main theorem.

### Actual joint shape source and arbitrary marked test exchange (5,335 jobs)

The full umbrella passes **5,335** jobs. Nine modules and **27** public
declarations have been integrated since 5,326. The three full audits pass
**6,555**, **5,530** and **4,522** distinct declarations; their axiom-free
counts remain **17**, **16** and **15**. All readers are closed. There are
no diagnostics, duplicate targets, nonstandard axioms or forbidden proof
placeholders in this checkpoint.

The complete-state shape kernel is jointly measurable in the physical
duration, passage depth, returned past, complete excursion and remaining
driver. The actual depth-dependent stopped law admits the proved anchor
time exchange by Tonelli, without replacing it by a fixed passage law.
Full-area Poisson weighting and arbitrary nonnegative remaining-driver
tests have their exact depth integral and literal Wright entrance
amplitude. The ordered excursion source also has a genuine head/tail
decomposition with slot-specific surplus marks and arbitrary coupled
Borel tests.

These are proved source dependencies. The actual marked Palm formula,
all-order Aldous factorial densities, and final Brownian identification
of graph limits remain pending at this checkpoint.

### Actual marked Palm deletion (5,338 jobs)

The full umbrella passes **5,338** jobs. Three new modules and **four**
public declarations have been integrated since 5,335. The full audits
pass **6,559**, **5,534** and **4,526** distinct declarations, with
**17**, **16** and **15** axiom-free declarations. All readers are
closed; diagnostics, duplicate targets, forbidden placeholders and
nonstandard axiom dependencies are absent.

The actual full-area marked Palm deletion formula is now proved for
every surplus and arbitrary nonnegative Borel tests of the literal
component length and compensated deleted Brownian path. Removing a
complete component of length `l` leaves the Brownian driver at parameter
`lambda-l`, with exactly the literal Wright size factor. The proof uses
the genuine complete-return shape source, depth-dependent stopped law,
and full-area Poisson marks, not an assumed Palm interface. Joint
measurability of the deleted head/tail source is also proved. All-order
factorial density and final graph-limit identification remain pending
at this fully audited checkpoint.

### Literal all-order Brownian factorial densities and cell moments (5,348 jobs)

The full umbrella passes **5,348** jobs. Ten modules and **54** public
declarations have been integrated since 5,338. The three full audits pass
**6,613**, **5,588** and **4,580** distinct declarations; axiom-free counts
remain **17**, **16** and **15**. All readers are closed. No diagnostics,
duplicate targets, nonstandard axioms or forbidden placeholders occur.

The genuine marked Palm formula now proves the literal every-order
Brownian--Wright factorial density, including slot-specific surplus and
arbitrary coupled nonnegative Borel tests. Actual finite point measures,
ordered tuples and all mixed cell descending factorials agree. Every
positive closed window has the literal cell density moments, finite
integrability and the summable factorial inversion series. Fixed-size
boundary atoms have zero actual mass. Canonical-chart factorial densities
genuinely determine their weak-Borel law, with neither candidate
integrability nor candidate exponential-moment assumptions. Actual
positive size dilation has its genuine inverse, and the density integral
has its exact starred normalization Jacobian.

Every arbitrary-window local determination and the final Brownian
identification of the model graph limits are not yet claimed complete.

### All literal Chapter 3 terminals completed (5,356 jobs)

The umbrella passes **5,356** jobs. Eight modules and **33** public
declarations have been integrated since the 5,348-job milestone. The
final full audits pass **6,646**, **5,621** and **4,613** distinct
declarations, with **17**, **16** and **15** axiom-free declarations.
All audit and exact leaf readers are closed. No diagnostics, duplicate
targets, nonstandard axioms, forbidden placeholders or missing artifacts
remain.

The actual all-order factorial densities now determine the point law in
every positive closed window. Genuine graph window convergence identifies
the actual Brownian law; finite compact-support tests and vague-Borel
determination lift this to the complete unmarked process. The model-only
terminals discharge every local-limit premise and give twelve actual
finite/compact window/global, empirical-marked and starred conclusions.

One countable integer realization simultaneously retains the population
properties, normalized and raw numerical local formulas, actual starred
global Brownian unmarked laws, and all arbitrary-window Brownian laws
with the original Perron TV mark. Its raw branch keeps the empirical
spectral drift inside the transformed parameter. The zero-drift case is
included by specialization. No global locally compact TV-product mark
space is introduced. All five main results stated in the paper's
Chapter 3 are covered by actual proved terminals.
