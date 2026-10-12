import PerronWright.Enumeration.MarkedCoreFactorization

/-!
# Decorated normalized identity and realized finite fibres

The continuous decorations are never asserted to form a finite ambient type.
For each actual labelled graph we construct one datum, prove its decorated
integral equals the literal graph weight, and then group only over the finite
image of the actual graph set.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

/-- Literal data retained after normalizing a marked terminal two-core.
The ordered endpoint lift aligns a chosen Hamilton order with its path marks.
Its unordered image is the bounded kernel table; storing that table separately
would duplicate information.  No finiteness is asserted for this continuous
decoration space. -/
structure DecoratedKernelDatum
    (S : Type*) [MetricSpace S] (k ell : ℕ) where
  nv : Fin (2 * ell + 1)
  ne : Fin (3 * ell + 1)
  length : Fin ne.val → Fin (k + 1)
  orientedEndpoints : Fin ne.val → Fin nv.val × Fin nv.val
  branchMark : Fin nv.val → C(S, ℝ)
  pathMark : (j : Fin ne.val) → Fin (length j).val → C(S, ℝ)

/-- The exact normalized integral of a realized decorated datum. -/
def decoratedKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k ell : ℕ}
    (D : DecoratedKernelDatum S k ell) : ℝ :=
  ∫ x : Fin D.nv.val → S,
    ((∏ i : Fin D.nv.val,
        D.branchMark i (x i) *
          Real.exp (-t * M.degreeFunction (x i))) *
      ∏ j : Fin D.ne.val,
        markedPathFactor M t (D.length j).val (D.pathMark j)
          (x (D.orientedEndpoints j).1)
          (x (D.orientedEndpoints j).2))
    ∂Measure.pi (fun _ : Fin D.nv.val => M.mu)

/-- Forget the continuous marks and the auxiliary orientation used to order
each path-mark vector, retaining exactly the bounded unordered kernel shape
and its path lengths. -/
def DecoratedKernelDatum.toKernelLengthDatum
    {S : Type*} [MetricSpace S] {k ell : ℕ}
    (D : DecoratedKernelDatum S k ell) :
    BoundedKernelLengthDatum k ell :=
  ⟨D.nv, D.ne,
    fun j => s((D.orientedEndpoints j).1, (D.orientedEndpoints j).2),
    D.length⟩

/-- With all marks equal to one, the decorated integral is exactly the
previous normalized kernel/length integral. -/
theorem decoratedKernelIntegral_eq_boundedKernelLengthIntegral_of_marks_one
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k ell : ℕ}
    (D : DecoratedKernelDatum S k ell)
    (hbranch : ∀ i, D.branchMark i = 1)
    (hpath : ∀ j i, D.pathMark j i = 1) :
    decoratedKernelIntegral M t D =
      boundedKernelLengthIntegral M t D.toKernelLengthDatum := by
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [hbranch i]
    simp only [ContinuousMap.one_apply, one_mul]
  · apply Finset.prod_congr rfl
    intro j _
    have hmark : D.pathMark j = fun _ => 1 := by
      funext i
      exact hpath j i
    rw [hmark, markedPathFactor_one]
    rfl

set_option linter.style.haveILetI false in
/-- A single genuinely marked two-core admits a normalized decorated-kernel
integral built solely from its actual finite graph, components, and marks. -/
theorem exists_markedGraphWeight_eq_decoratedKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {m K ell : ℕ}
    (G : SimpleGraph (Fin m))
    (marks : Fin m → C(S, ℝ))
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    (hell : 0 < ell) (hs : G.edgeFinset.card = m + ell)
    (hmK : m ≤ K) (s₀ : S) :
    ∃ D : DecoratedKernelDatum S K ell,
      markedGraphWeight M t G marks = decoratedKernelIntegral M t D := by
  classical
  let hscard : G.edgeFinset.card = Fintype.card (Fin m) + ell := by
    simpa only [Fintype.card_fin] using hs
  let hacyc : (twoGraph G).IsAcyclic :=
    degreeTwo_induced_isAcyclic G hconn hmin hell hscard
  letI : Fintype (twoGraph G).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype {e : Sym2 (Fin m) // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  obtain ⟨nv, ne, eB, eE, _, _⟩ :=
    exists_exact_bounded_kernel_relabeling G hconn hmin hell hscard
  letI : Fintype (KernelEdgeLabel G) := by
    dsimp only [KernelEdgeLabel]
    infer_instance
  obtain ⟨n, e, qL, qR, hn, hne, hL, hR, hweight⟩ :=
    exists_markedGraphWeight_eq_integral_markedPathFactors
      M t G marks hacyc s₀
  let edgeLength : KernelEdgeLabel G → ℕ
    | Sum.inl C₀ => n C₀ + 1
    | Sum.inr _ => 0
  have hedgeLength (a : KernelEdgeLabel G) : edgeLength a ≤ K := by
    cases a with
    | inl C₀ =>
        have hcard : Fintype.card C₀ ≤ m :=
          by
            simpa only [Fintype.card_fin] using
              (Fintype.card_le_of_injective
                (fun x : C₀ => x.val.val)
                (fun x y hxy => Subtype.ext (Subtype.ext hxy)))
        have hle : n C₀ + 1 ≤ m := by
          rw [← hn C₀]
          exact hcard
        exact hle.trans hmK
    | inr d =>
        simp only [edgeLength]
        exact Nat.zero_le _
  let length : Fin ne.val → Fin (K + 1) := fun j =>
    ⟨edgeLength (eE.symm j),
      Nat.lt_succ_of_le (hedgeLength (eE.symm j))⟩
  let branchMark : Fin nv.val → C(S, ℝ) := fun i =>
    marks ((coreBranchEquivBranching G hmin).symm (eB.symm i)).val
  let componentLeft (C₀ : (twoGraph G).ConnectedComponent) : Fin nv.val :=
    eB (coreBranchEquivBranching G hmin
      (componentBoundaryStubBranchIndex G C₀ (qL C₀)))
  let componentRight (C₀ : (twoGraph G).ConnectedComponent) : Fin nv.val :=
    eB (coreBranchEquivBranching G hmin
      (componentBoundaryStubBranchIndex G C₀ (qR C₀)))
  let directOrientation
      (d : {a : Sym2 (Fin m) // a ∈ directBranchEdges G}) :
      Fin nv.val × Fin nv.val :=
    Classical.choose (Sym2.mk_surjective
      (Sym2.map eB (kernelBranchEndpoints G hmin hacyc
        (Sum.inr d : KernelEdgeLabel G))))
  let edgeOrientation : KernelEdgeLabel G → Fin nv.val × Fin nv.val
    | Sum.inl C₀ => (componentLeft C₀, componentRight C₀)
    | Sum.inr d => directOrientation d
  have hedgeOrientation (a : KernelEdgeLabel G) :
      Sym2.map eB (kernelBranchEndpoints G hmin hacyc a) =
        s((edgeOrientation a).1, (edgeOrientation a).2) := by
    cases a with
    | inl C₀ =>
        rw [kernelBranchEndpoints_eq_boundaryStubBranchPair
          G hmin hacyc C₀ (qL C₀) (qR C₀) (hne C₀)]
        rfl
    | inr d =>
        exact (Classical.choose_spec (Sym2.mk_surjective
          (Sym2.map eB (kernelBranchEndpoints G hmin hacyc
            (Sum.inr d : KernelEdgeLabel G))))).symm
  let orientedEndpoints : Fin ne.val → Fin nv.val × Fin nv.val :=
    fun j => edgeOrientation (eE.symm j)
  let edgeMark : (a : KernelEdgeLabel G) → Fin (edgeLength a) → C(S, ℝ)
    | Sum.inl C₀ => fun i => marks ((e C₀) i).val.val
    | Sum.inr _ => fun i => Fin.elim0 i
  let pathMark : (j : Fin ne.val) → Fin (length j).val → C(S, ℝ) :=
    fun j => edgeMark (eE.symm j)
  let D : DecoratedKernelDatum S K ell :=
    { nv := nv
      ne := ne
      length := length
      orientedEndpoints := orientedEndpoints
      branchMark := branchMark
      pathMark := pathMark }
  refine ⟨D, ?_⟩
  rw [hweight]
  rw [integral_coreBranch_relabel M G hmin eB]
  unfold decoratedKernelIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  let b : coreBranchIndex G → S :=
    fun c => x (eB (coreBranchEquivBranching G hmin c))
  change
    markedGraphCoreBranchFactor M t G marks s₀ b *
        ∏ C₀ : (twoGraph G).ConnectedComponent,
          markedPathFactor M t (n C₀ + 1)
            (fun i => marks ((e C₀) i).val.val)
            (b (componentBoundaryStubBranchIndex G C₀ (qL C₀)))
            (b (componentBoundaryStubBranchIndex G C₀ (qR C₀))) = _
  rw [markedGraphCoreBranchFactor_relabel_eq_kernelFactors
    M t G marks hmin hacyc s₀ eB x]
  let actualFactor : KernelEdgeLabel G → ℝ := fun a =>
    markedPathFactor M t (edgeLength a) (edgeMark a)
      (x (edgeOrientation a).1) (x (edgeOrientation a).2)
  have hcomponent :
      (∏ C₀ : (twoGraph G).ConnectedComponent,
          markedPathFactor M t (n C₀ + 1)
            (fun i => marks ((e C₀) i).val.val)
            (b (componentBoundaryStubBranchIndex G C₀ (qL C₀)))
            (b (componentBoundaryStubBranchIndex G C₀ (qR C₀)))) =
        ∏ C₀ : (twoGraph G).ConnectedComponent,
          actualFactor (Sum.inl C₀) := by
    apply Finset.prod_congr rfl
    intro C₀ _
    rfl
  have hdirect :
      (∏ d : {a : Sym2 (Fin m) // a ∈ directBranchEdges G},
          pathKernelEdgeFactor M t 0 x
            (Sym2.map eB (kernelBranchEndpoints G hmin hacyc
              (Sum.inr d : KernelEdgeLabel G)))) =
        ∏ d : {a : Sym2 (Fin m) // a ∈ directBranchEdges G},
          actualFactor (Sum.inr d) := by
    apply Finset.prod_congr rfl
    intro d _
    rw [hedgeOrientation (Sum.inr d : KernelEdgeLabel G)]
    rfl
  have hsplit :
      (∏ a : KernelEdgeLabel G, actualFactor a) =
        (∏ C₀ : (twoGraph G).ConnectedComponent,
          actualFactor (Sum.inl C₀)) *
        ∏ d : {a : Sym2 (Fin m) // a ∈ directBranchEdges G},
          actualFactor (Sum.inr d) := by
    change
      (∏ a : (twoGraph G).ConnectedComponent ⊕
          {d // d ∈ directBranchEdges G}, actualFactor a) = _
    exact Fintype.prod_sum_type actualFactor
  have hrelabel :
      (∏ a : KernelEdgeLabel G, actualFactor a) =
        ∏ j : Fin ne.val,
          markedPathFactor M t (D.length j).val (D.pathMark j)
            (x (D.orientedEndpoints j).1)
            (x (D.orientedEndpoints j).2) := by
    exact Fintype.prod_equiv eE
      actualFactor
      (fun j : Fin ne.val =>
        markedPathFactor M t (D.length j).val (D.pathMark j)
          (x (D.orientedEndpoints j).1)
          (x (D.orientedEndpoints j).2))
      (fun a => by
        simp only [D, length, pathMark, orientedEndpoints,
          Equiv.symm_apply_apply]
        rw [eE.symm_apply_apply])
  rw [← hrelabel, hsplit, ← hcomponent, ← hdirect]
  ring

/-- Original connected labelled graphs in the fixed positive-surplus sum. -/
abbrev FixedSurplusGraph (k ell : ℕ) :=
  {G : SimpleGraph (Fin k) // G ∈ fixedSurplusGraphs k ell}

/-- Each original graph has a decorated normalized datum whose integral is
its literal graph weight; its decorations are its actual pruning marks. -/
theorem exists_graphWeight_eq_actualDecoratedKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (k ell : ℕ) (hell : 0 < ell)
    (s₀ : S) (A : FixedSurplusGraph k ell) :
    ∃ D : DecoratedKernelDatum S k ell,
      M.graphWeight t A.1 = decoratedKernelIntegral M t D := by
  classical
  let G := A.1
  let p := LeafPruning.pruneAll k G
  have hA : G.Connected ∧
      G.edgeFinset.card + 1 = Fintype.card (Fin k) + (ell + 1) := by
    simpa only [G, fixedSurplusGraphs, Finset.mem_filter,
      Finset.mem_univ, true_and] using A.2
  have hadm := coreIndex_admissible G hA.1 hA.2
  have hconn : p.terminalGraph.Connected := by
    change (coreIndex G).2.Connected
    exact hadm.1
  have hmin : ∀ v, 2 ≤ p.terminalGraph.degree v := by
    change ∀ v, 2 ≤ (coreIndex G).2.degree v
    exact hadm.2.1
  have hs : p.terminalGraph.edgeFinset.card = p.terminalCount + ell := by
    change (coreIndex G).2.edgeFinset.card = (coreIndex G).1.val + ell
    exact hadm.2.2.1
  obtain ⟨D, hD⟩ := exists_markedGraphWeight_eq_decoratedKernelIntegral
    M t p.terminalGraph (p.terminalMarks M t (fun _ => 1))
      hconn hmin hell hs p.terminalCount_le s₀
  refine ⟨D, ?_⟩
  exact (graphWeight_pruneAll M t G).trans hD

/-- A deterministic choice of the proved actual datum. -/
def actualDecoratedKernelDatum
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (k ell : ℕ) (hell : 0 < ell)
    (s₀ : S) (A : FixedSurplusGraph k ell) :
    DecoratedKernelDatum S k ell :=
  Classical.choose
    (exists_graphWeight_eq_actualDecoratedKernelIntegral
      M t k ell hell s₀ A)

theorem graphWeight_eq_actualDecoratedKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (k ell : ℕ) (hell : 0 < ell)
    (s₀ : S) (A : FixedSurplusGraph k ell) :
    M.graphWeight t A.1 =
      decoratedKernelIntegral M t
        (actualDecoratedKernelDatum M t k ell hell s₀ A) :=
  Classical.choose_spec
    (exists_graphWeight_eq_actualDecoratedKernelIntegral
      M t k ell hell s₀ A)

/-- Only the decorations actually produced by the finite graph set. -/
def realizedDecoratedKernelData
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (k ell : ℕ) (hell : 0 < ell)
    (s₀ : S) : Finset (DecoratedKernelDatum S k ell) := by
  classical
  exact Finset.univ.image
    (actualDecoratedKernelDatum M t k ell hell s₀)

/-- Every graph weight is first replaced by its proved decorated integral;
the resulting finite sum is then partitioned by equal realized data. -/
theorem connectedWeight_eq_realizedDecoratedKernel_fibers
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (k ell : ℕ) (hell : 0 < ell)
    (s₀ : S) :
    M.connectedWeight t k (ell + 1) =
      ∑ D ∈ realizedDecoratedKernelData M t k ell hell s₀,
        ∑ _A ∈ (Finset.univ : Finset (FixedSurplusGraph k ell)).filter
            (fun A => actualDecoratedKernelDatum M t k ell hell s₀ A = D),
          decoratedKernelIntegral M t D := by
  classical
  rw [connectedWeight_eq_sum_fixedSurplusGraphs M t k ell]
  let Φ := actualDecoratedKernelDatum M t k ell hell s₀
  let R := realizedDecoratedKernelData M t k ell hell s₀
  have hsub :
      (∑ G ∈ fixedSurplusGraphs k ell, M.graphWeight t G) =
        ∑ A : FixedSurplusGraph k ell, M.graphWeight t A.1 := by
    exact Finset.sum_subtype (fixedSurplusGraphs k ell)
      (fun _ => Iff.rfl) (fun G => M.graphWeight t G)
  rw [hsub]
  have hreplace :
      (∑ A : FixedSurplusGraph k ell, M.graphWeight t A.1) =
        ∑ A : FixedSurplusGraph k ell,
          decoratedKernelIntegral M t (Φ A) := by
    apply Fintype.sum_congr
    intro A
    exact graphWeight_eq_actualDecoratedKernelIntegral
      M t k ell hell s₀ A
  rw [hreplace]
  have hsupport :
      (Finset.univ : Finset (FixedSurplusGraph k ell)).filter
          (fun A => Φ A ∈ R) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro A _
    exact Finset.mem_image.mpr ⟨A, Finset.mem_univ A, rfl⟩
  have hpartition := Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ : Finset (FixedSurplusGraph k ell)) R Φ
    (fun A => decoratedKernelIntegral M t (Φ A))
  rw [hsupport] at hpartition
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro A hA
  have hΦ : Φ A = D := (Finset.mem_filter.mp hA).2
  rw [hΦ]

end PerronWright.GraphCore
