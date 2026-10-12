import PerronWright.Enumeration.MarkedPathFactor

/-!
# Literal marked two-core factorization

This stage proves that branch marks and the ordered marks on every actual
degree-two path exhaust the literal marked graph integrand.  It neither
defines decorated normalized data nor regroups the outer graph sum.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

/-- One degree-two component factor with the literal pruning mark on each
of its actual vertices. -/
private def markedGraphCoreComponentFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (marks : Fin k → C(S, ℝ)) (s₀ : S)
    (C₀ : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S) (y : C₀ → S) : ℝ :=
  (∏ c : C₀, marks c.val.val (y c)) *
    graphCoreComponentFactor M t G s₀ C₀ b y

/-- The branch block with literal pruning marks on all actual branch
vertices. -/
def markedGraphCoreBranchFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (marks : Fin k → C(S, ℝ)) (s₀ : S)
    (b : coreBranchIndex G → S) : ℝ :=
  (∏ c : coreBranchIndex G, marks c.val (b c)) *
    graphCoreBranchFactor M t G s₀ b

/-- The actual branch vertices and actual degree-two components partition
the vertex set, so their two mark products recover the full mark product. -/
private theorem vertexMarks_product_coreCoordinates
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    {k : ℕ} (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    (marks : Fin k → C(S, ℝ)) (x : Fin k → S) :
    (∏ v : Fin k, marks v (x v)) =
      (∏ b : coreBranchIndex G,
          marks b.val ((coreCoordinateMeasurableEquiv G x).1 b)) *
        ∏ C₀ : (twoGraph G).ConnectedComponent,
          ∏ c : C₀,
            marks c.val.val
              ((coreCoordinateMeasurableEquiv G x).2 ⟨C₀, c⟩) := by
  classical
  let e := coreCoordinateEquiv G
  calc
    (∏ v : Fin k, marks v (x v)) =
        ∏ q : coreBranchIndex G ⊕
            (Σ C₀ : (twoGraph G).ConnectedComponent, C₀),
          marks (e q) (x (e q)) := by
      symm
      exact Fintype.prod_equiv e
        (fun q => marks (e q) (x (e q)))
        (fun v => marks v (x v))
        (fun _ => rfl)
    _ = (∏ b : coreBranchIndex G,
          marks b.val ((coreCoordinateMeasurableEquiv G x).1 b)) *
        ∏ z : Σ C₀ : (twoGraph G).ConnectedComponent, C₀,
          marks z.2.val.val
            ((coreCoordinateMeasurableEquiv G x).2 z) := by
      rw [Fintype.prod_sum_type]
      congr 1
    _ = _ := by
      rw [Fintype.prod_sigma]

/-- The literal marked integrand factors into one marked branch block and
one marked block for every actual degree-two component. -/
private theorem markedGraphIntegrand_eq_markedCoreFactors
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    (marks : Fin k → C(S, ℝ)) (s₀ : S) (x : Fin k → S) :
    markedGraphIntegrand M t G marks x =
      markedGraphCoreBranchFactor M t G marks s₀
          (coreCoordinateMeasurableEquiv G x).1 *
        ∏ C₀ : (twoGraph G).ConnectedComponent,
          markedGraphCoreComponentFactor M t G marks s₀ C₀
            (coreCoordinateMeasurableEquiv G x).1
            (fun c => (coreCoordinateMeasurableEquiv G x).2 ⟨C₀, c⟩) := by
  classical
  unfold markedGraphIntegrand markedGraphCoreBranchFactor
  rw [graphWeightIntegrand_eq_coreFactors M t G s₀ x]
  rw [vertexMarks_product_coreCoordinates G marks x]
  have hcomponents :
      (∏ C₀ : (twoGraph G).ConnectedComponent,
          markedGraphCoreComponentFactor M t G marks s₀ C₀
            (coreCoordinateMeasurableEquiv G x).1
            (fun c => (coreCoordinateMeasurableEquiv G x).2 ⟨C₀, c⟩)) =
        (∏ C₀ : (twoGraph G).ConnectedComponent,
            ∏ c : C₀,
              marks c.val.val
                ((coreCoordinateMeasurableEquiv G x).2 ⟨C₀, c⟩)) *
          ∏ C₀ : (twoGraph G).ConnectedComponent,
            graphCoreComponentFactor M t G s₀ C₀
              (coreCoordinateMeasurableEquiv G x).1
              (fun c =>
                (coreCoordinateMeasurableEquiv G x).2 ⟨C₀, c⟩) := by
    unfold markedGraphCoreComponentFactor
    rw [Finset.prod_mul_distrib]
  rw [hcomponents]
  ring

/-- Conditional integration of all actual marked degree-two components. -/
private theorem markedGraphWeight_eq_integral_markedCoreComponentFactors
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    (marks : Fin k → C(S, ℝ)) (s₀ : S) :
    markedGraphWeight M t G marks =
      ∫ b : coreBranchIndex G → S,
        markedGraphCoreBranchFactor M t G marks s₀ b *
          ∏ C₀ : (twoGraph G).ConnectedComponent,
            (∫ y : C₀ → S,
              markedGraphCoreComponentFactor M t G marks s₀ C₀ b y
              ∂Measure.pi (fun _ : C₀ => M.mu))
        ∂Measure.pi (fun _ : coreBranchIndex G => M.mu) := by
  let e := coreCoordinateMeasurableEquiv G (S := S)
  let μB := Measure.pi (fun _ : coreBranchIndex G => M.mu)
  let μC := Measure.pi
    (fun _ : Σ C₀ : (twoGraph G).ConnectedComponent, C₀ => M.mu)
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin k => M.mu)) (μB.prod μC) :=
    coreCoordinate_measurePreserving G M.mu
  have hbase : Integrable (markedGraphIntegrand M t G marks)
      (Measure.pi (fun _ : Fin k => M.mu)) :=
    markedGraphIntegrand_integrable M t G marks
  have hcoord : Integrable
      (fun p : (coreBranchIndex G → S) ×
          ((Σ C₀ : (twoGraph G).ConnectedComponent, C₀) → S) =>
        markedGraphIntegrand M t G marks (e.symm p))
      (μB.prod μC) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hbase
  have hfactor (p : (coreBranchIndex G → S) ×
      ((Σ C₀ : (twoGraph G).ConnectedComponent, C₀) → S)) :
      markedGraphIntegrand M t G marks (e.symm p) =
        markedGraphCoreBranchFactor M t G marks s₀ p.1 *
          ∏ C₀ : (twoGraph G).ConnectedComponent,
            markedGraphCoreComponentFactor M t G marks s₀ C₀ p.1
              (fun c => p.2 ⟨C₀, c⟩) := by
    simpa only [e, MeasurableEquiv.apply_symm_apply] using
      markedGraphIntegrand_eq_markedCoreFactors
        M t G marks s₀ (e.symm p)
  have hInt : Integrable
      (fun p : (coreBranchIndex G → S) ×
          ((Σ C₀ : (twoGraph G).ConnectedComponent, C₀) → S) =>
        markedGraphCoreBranchFactor M t G marks s₀ p.1 *
          ∏ C₀ : (twoGraph G).ConnectedComponent,
            markedGraphCoreComponentFactor M t G marks s₀ C₀ p.1
              (fun c => p.2 ⟨C₀, c⟩))
      (μB.prod μC) := by
    refine hcoord.congr ?_
    filter_upwards [] with p
    exact hfactor p
  unfold markedGraphWeight
  calc
    (∫ x : Fin k → S, markedGraphIntegrand M t G marks x
        ∂Measure.pi (fun _ : Fin k => M.mu)) =
      ∫ x : Fin k → S,
        markedGraphCoreBranchFactor M t G marks s₀
            (coreCoordinateMeasurableEquiv G x).1 *
          ∏ C₀ : (twoGraph G).ConnectedComponent,
            markedGraphCoreComponentFactor M t G marks s₀ C₀
              (coreCoordinateMeasurableEquiv G x).1
              (fun c => (coreCoordinateMeasurableEquiv G x).2 ⟨C₀, c⟩)
        ∂Measure.pi (fun _ : Fin k => M.mu) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact markedGraphIntegrand_eq_markedCoreFactors M t G marks s₀ x
    _ = _ := integral_core_component_blocks G M.mu
      (markedGraphCoreBranchFactor M t G marks s₀)
      (fun C₀ => markedGraphCoreComponentFactor M t G marks s₀ C₀)
      hInt

/-- In an actual Hamilton order, a marked component block is exactly the
literal marked path observable.  Here `n = 0` means that the component has
one actual degree-two vertex, hence contributes a marked path of length one;
length zero is reserved for a direct branch-to-branch edge below. -/
private theorem markedGraphCoreComponentFactor_reindexed_eq_markedPathObservable
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k n : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (marks : Fin k → C(S, ℝ))
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) (C₀ : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S)
    (e : SimpleGraph.pathGraph (n + 1) ≃g C₀.toSimpleGraph)
    (qL qR : {q // q ∈ componentBoundaryStubs G C₀})
    (hne : qL ≠ qR) (hL : e 0 = qL.val.1)
    (hR : e (Fin.last n) = qR.val.1)
    (x : Fin (n + 1) → S) :
    markedGraphCoreComponentFactor M t G marks s₀ C₀ b
        (fun c => x (e.symm c)) =
      (∏ i : Fin (n + 1), marks (e i).val.val (x i)) *
        interiorPathObservable M t n
          (b (componentBoundaryStubBranchIndex G C₀ qL))
          (b (componentBoundaryStubBranchIndex G C₀ qR)) x := by
  unfold markedGraphCoreComponentFactor
  rw [graphCoreComponentFactor_reindexed_eq_interiorPathObservable
    M t G hacyc s₀ C₀ b e qL qR hne hL hR x]
  congr 1
  exact Fintype.prod_equiv e.toEquiv.symm
    (fun c : C₀ => marks c.val.val (x (e.symm c)))
    (fun i : Fin (n + 1) => marks (e i).val.val (x i))
    (fun c => by
      have hc : e (e.symm c) = c := e.apply_symm_apply c
      exact congrArg (fun v : Fin k => marks v (x (e.symm c)))
        (congrArg (fun z : C₀ => z.val.val) hc.symm))

/-- Integrating the component gives the marked path factor with the actual
ordered vector of pruning marks. -/
private theorem integral_markedGraphCoreComponentFactor_eq_markedPathFactor
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k n : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (marks : Fin k → C(S, ℝ))
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) (C₀ : (twoGraph G).ConnectedComponent)
    (b : coreBranchIndex G → S)
    (e : SimpleGraph.pathGraph (n + 1) ≃g C₀.toSimpleGraph)
    (qL qR : {q // q ∈ componentBoundaryStubs G C₀})
    (hne : qL ≠ qR) (hL : e 0 = qL.val.1)
    (hR : e (Fin.last n) = qR.val.1) :
    (∫ y : C₀ → S,
        markedGraphCoreComponentFactor M t G marks s₀ C₀ b y
        ∂Measure.pi (fun _ : C₀ => M.mu)) =
      markedPathFactor M t (n + 1)
        (fun i => marks (e i).val.val)
        (b (componentBoundaryStubBranchIndex G C₀ qL))
        (b (componentBoundaryStubBranchIndex G C₀ qR)) := by
  rw [integral_pi_reindex M.mu e.toEquiv
    (markedGraphCoreComponentFactor M t G marks s₀ C₀ b)]
  change
    (∫ x : Fin (n + 1) → S,
      markedGraphCoreComponentFactor M t G marks s₀ C₀ b
        (fun c => x (e.symm c))
      ∂Measure.pi (fun _ : Fin (n + 1) => M.mu)) = _
  apply integral_congr_ae
  filter_upwards [] with x
  exact markedGraphCoreComponentFactor_reindexed_eq_markedPathObservable
    M t G marks hacyc s₀ C₀ b e qL qR hne hL hR x

/-- Simultaneously choose the actual Hamilton order and two actual boundary
stubs of every marked degree-two component. -/
theorem exists_markedGraphWeight_eq_integral_markedPathFactors
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    (marks : Fin k → C(S, ℝ))
    (hacyc : (twoGraph G).IsAcyclic) (s₀ : S) :
    ∃ n : (twoGraph G).ConnectedComponent → ℕ,
      ∃ e : (C₀ : (twoGraph G).ConnectedComponent) →
          SimpleGraph.pathGraph (n C₀ + 1) ≃g C₀.toSimpleGraph,
      ∃ qL qR : ∀ C₀ : (twoGraph G).ConnectedComponent,
          {q // q ∈ componentBoundaryStubs G C₀},
        (∀ C₀ : (twoGraph G).ConnectedComponent,
          Fintype.card C₀ = n C₀ + 1) ∧
        (∀ C₀ : (twoGraph G).ConnectedComponent, qL C₀ ≠ qR C₀) ∧
        (∀ C₀ : (twoGraph G).ConnectedComponent,
          e C₀ 0 = (qL C₀).val.1) ∧
        (∀ C₀ : (twoGraph G).ConnectedComponent,
          e C₀ (Fin.last (n C₀)) = (qR C₀).val.1) ∧
        markedGraphWeight M t G marks =
          ∫ b : coreBranchIndex G → S,
            markedGraphCoreBranchFactor M t G marks s₀ b *
              ∏ C₀ : (twoGraph G).ConnectedComponent,
                markedPathFactor M t (n C₀ + 1)
                  (fun i => marks ((e C₀) i).val.val)
                  (b (componentBoundaryStubBranchIndex G C₀ (qL C₀)))
                  (b (componentBoundaryStubBranchIndex G C₀ (qR C₀)))
            ∂Measure.pi (fun _ : coreBranchIndex G => M.mu) := by
  have hchoice := fun C₀ : (twoGraph G).ConnectedComponent =>
    exists_componentPathOrder_with_boundaryStubs G hacyc C₀
  choose n hn e qL qR hne hL hR using hchoice
  refine ⟨n, e, qL, qR, hn, hne, hL, hR, ?_⟩
  rw [markedGraphWeight_eq_integral_markedCoreComponentFactors
    M t G marks s₀]
  apply integral_congr_ae
  filter_upwards [] with b
  congr 1
  apply Finset.prod_congr rfl
  intro C₀ _
  exact integral_markedGraphCoreComponentFactor_eq_markedPathFactor
    M t G marks hacyc s₀ C₀ b (e C₀) (qL C₀) (qR C₀)
      (hne C₀) (hL C₀) (hR C₀)

/-- Relabelling branch coordinates transports their pruning marks together
with the already proved vertex and direct-edge factors.  These direct edges
are precisely the length-zero case: they have no internal mark and contribute
`pathKernelEdgeFactor M t 0`. -/
theorem markedGraphCoreBranchFactor_relabel_eq_kernelFactors
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} (G : SimpleGraph (Fin k))
    (marks : Fin k → C(S, ℝ))
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) {nv : ℕ}
    (eB : (branchingVertices G : Set (Fin k)) ≃ Fin nv)
    (x : Fin nv → S) :
    markedGraphCoreBranchFactor M t G marks s₀
        (fun b => x (eB (coreBranchEquivBranching G hmin b))) =
      (∏ i : Fin nv,
          marks ((coreBranchEquivBranching G hmin).symm (eB.symm i)).val
              (x i) *
            Real.exp (-t * M.degreeFunction (x i))) *
        ∏ d : {e // e ∈ directBranchEdges G},
          pathKernelEdgeFactor M t 0 x
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inr d : KernelEdgeLabel G))) := by
  classical
  unfold markedGraphCoreBranchFactor
  rw [graphCoreBranchFactor_relabel_eq_kernelFactors
    M t G hmin hacyc s₀ eB x]
  have hmarks :
      (∏ c : coreBranchIndex G,
          marks c.val (x (eB (coreBranchEquivBranching G hmin c)))) =
        ∏ i : Fin nv,
          marks ((coreBranchEquivBranching G hmin).symm (eB.symm i)).val
            (x i) := by
    let e := (coreBranchEquivBranching G hmin).trans eB
    exact Fintype.prod_equiv e
      (fun c : coreBranchIndex G =>
        marks c.val (x (eB (coreBranchEquivBranching G hmin c))))
      (fun i : Fin nv =>
        marks ((coreBranchEquivBranching G hmin).symm (eB.symm i)).val
          (x i))
      (fun c => by simp only [e, Equiv.trans_apply,
        Equiv.symm_apply_apply])
  rw [hmarks, Finset.prod_mul_distrib]
  ring

/-- The unordered endpoint pair of a genuine path component is the pair of
branch indices selected by any two distinct actual boundary stubs. -/
theorem kernelBranchEndpoints_eq_boundaryStubBranchPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (twoGraph G).IsAcyclic)
    (C₀ : (twoGraph G).ConnectedComponent)
    (qL qR : {q // q ∈ componentBoundaryStubs G C₀})
    (hne : qL ≠ qR) :
    kernelBranchEndpoints G hmin hacyc
        (Sum.inl C₀ : KernelEdgeLabel G) =
      s(coreBranchEquivBranching G hmin
          (componentBoundaryStubBranchIndex G C₀ qL),
        coreBranchEquivBranching G hmin
          (componentBoundaryStubBranchIndex G C₀ qR)) := by
  let bL : (branchingVertices G : Set V) :=
    coreBranchEquivBranching G hmin
      (componentBoundaryStubBranchIndex G C₀ qL)
  let bR : (branchingVertices G : Set V) :=
    coreBranchEquivBranching G hmin
      (componentBoundaryStubBranchIndex G C₀ qR)
  apply Sym2.map.injective Subtype.val_injective
  calc
    Sym2.map Subtype.val
        (kernelBranchEndpoints G hmin hacyc
          (Sum.inl C₀ : KernelEdgeLabel G)) =
      degreeTwoPathEndpoints G hacyc C₀ := by
        exact kernelBranchEndpoints_map_val G hmin hacyc
          (Sum.inl C₀ : KernelEdgeLabel G)
    _ = s(qL.val.2, qR.val.2) :=
      degreeTwoPathEndpoints_eq_boundaryStubPair G hacyc C₀ qL qR hne
    _ = Sym2.map Subtype.val s(bL, bR) := by
      simp only [Sym2.map_mk]
      congr 1

end PerronWright.GraphCore
