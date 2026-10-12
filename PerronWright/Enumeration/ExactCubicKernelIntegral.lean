import PerronWright.Enumeration.NormalizedKernelIntegral
import PerronWright.Enumeration.CubicKernelValence

/-!
# Exact cubic normalized-kernel integral

This module specializes the bounded normalized-kernel integral to an
actual cubic core.  Both coordinate cardinalities are then exact, and the
endpoint table is the project's literal cubic `FiniteMultiGraph`.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

set_option linter.style.haveILetI false in
/-- The canonical cubic endpoint table comes with exact relabellings of the
actual branch vertices and actual suppressed-edge labels. -/
theorem exists_exact_cubic_kernel_relabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell)
    (hcubic : ∀ v ∈ branchingVertices G, G.degree v = 3) :
    ∃ (eB : (branchingVertices G : Set V) ≃ Fin (2 * ell))
      (eE : KernelEdgeLabel G ≃ Fin (3 * ell)),
      ∀ e : KernelEdgeLabel G,
        (normalizedCubicFiniteMultiGraph
          G hconn hmin hell hs hcubic).endpoints (eE e) =
          Sym2.map eB
            (kernelBranchEndpoints G hmin
              (degreeTwo_induced_isAcyclic G hconn hmin hell hs) e) := by
  let hacyc := degreeTwo_induced_isAcyclic G hconn hmin hell hs
  have hE : Nat.card (KernelEdgeLabel G) = 3 * ell :=
    (kernelEdgeLabel_card_eq_three_surplus_iff_cubic
      G hconn hmin hell hs).mpr hcubic
  letI : Fintype (twoGraph G).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype {e : Sym2 V // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype (KernelEdgeLabel G) := by
    dsimp only [KernelEdgeLabel]
    infer_instance
  let eB : (branchingVertices G : Set V) ≃ Fin (2 * ell) :=
    Finset.equivFinOfCardEq
      ((branchingVertices_card_eq_two_surplus_iff_cubic
        G hmin hs).mpr hcubic)
  let eE : KernelEdgeLabel G ≃ Fin (3 * ell) := by
    apply Fintype.equivFinOfCardEq
    simpa only [Nat.card_eq_fintype_card] using hE
  refine ⟨eB, eE, ?_⟩
  intro e
  change normalizedCubicKernelShape G hconn hmin hell hs hcubic (eE e) = _
  simp only [normalizedCubicKernelShape, eB, eE,
    Equiv.symm_apply_apply]
  apply congrArg (fun f => Sym2.map f
    (kernelBranchEndpoints G hmin hacyc e))
  funext x
  rfl

set_option linter.style.haveILetI false in
/-- An actual cubic positive-surplus core has an exact integral over its
`2 ell` normalized branch coordinates and `3 ell` normalized edge labels.
The endpoint table is literally cubic, with loops counted twice. -/
theorem exists_graphWeight_eq_exactCubicKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k))
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = k + ell)
    (hcubic : ∀ v ∈ branchingVertices G, G.degree v = 3)
    (s₀ : S) :
    let H := normalizedCubicFiniteMultiGraph G hconn hmin hell
      (by simpa using hs) hcubic
    ∃ length : Fin (3 * ell) → ℕ,
      M.graphWeight t G =
        ∫ x : Fin (2 * ell) → S,
          (∏ i : Fin (2 * ell),
              Real.exp (-t * M.degreeFunction (x i))) *
            ∏ j : Fin (3 * ell),
              pathKernelEdgeFactor M t (length j) x (H.endpoints j)
          ∂Measure.pi (fun _ : Fin (2 * ell) => M.mu) ∧
      ∀ i : Fin (2 * ell), H.degree i = 3 := by
  classical
  dsimp only
  let hscard : G.edgeFinset.card = Fintype.card (Fin k) + ell := by
    simpa using hs
  let hacyc : (twoGraph G).IsAcyclic :=
    degreeTwo_induced_isAcyclic G hconn hmin hell hscard
  letI : Fintype (twoGraph G).ConnectedComponent := Fintype.ofFinite _
  letI : ∀ C : (twoGraph G).ConnectedComponent, Fintype C :=
    fun C => Fintype.ofFinite C
  letI : Fintype {e : Sym2 (Fin k) // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype (KernelEdgeLabel G) := by
    dsimp only [KernelEdgeLabel]
    infer_instance
  obtain ⟨eB, eE, hend⟩ :=
    exists_exact_cubic_kernel_relabeling
      G hconn hmin hell hscard hcubic
  obtain ⟨n, _hn, qL, qR, hne, hweight⟩ :=
    exists_graphWeight_eq_integral_corePathKernels M t G hacyc s₀
  let edgeLength : KernelEdgeLabel G → ℕ
    | Sum.inl C => n C + 1
    | Sum.inr _ => 0
  let length : Fin (3 * ell) → ℕ :=
    fun j => edgeLength (eE.symm j)
  refine ⟨length, ?_, ?_⟩
  · rw [hweight]
    rw [integral_coreBranch_relabel M G hmin eB]
    apply integral_congr_ae
    filter_upwards [] with x
    let b : coreBranchIndex G → S :=
      fun c => x (eB (coreBranchEquivBranching G hmin c))
    change
      graphCoreBranchFactor M t G s₀ b *
          ∏ C : (twoGraph G).ConnectedComponent,
            pathKernel M t (n C + 1)
              (b (componentBoundaryStubBranchIndex G C (qL C)),
                b (componentBoundaryStubBranchIndex G C (qR C))) = _
    rw [graphCoreBranchFactor_relabel_eq_kernelFactors
      M t G hmin hacyc s₀ eB x]
    have hcomp :
        (∏ C : (twoGraph G).ConnectedComponent,
            pathKernel M t (n C + 1)
              (b (componentBoundaryStubBranchIndex G C (qL C)),
                b (componentBoundaryStubBranchIndex G C (qR C)))) =
          ∏ C : (twoGraph G).ConnectedComponent,
            pathKernelEdgeFactor M t (n C + 1) x
              (Sym2.map eB
                (kernelBranchEndpoints G hmin hacyc
                  (Sum.inl C : KernelEdgeLabel G))) := by
      apply Finset.prod_congr rfl
      intro C _
      simpa [b] using
        (pathKernelEdgeFactor_kernelBranchEndpoints_inl
          M t G hmin hacyc C (qL C) (qR C) (hne C) eB b).symm
    rw [hcomp]
    let actualFactor : KernelEdgeLabel G → ℝ := fun e =>
      pathKernelEdgeFactor M t (edgeLength e) x
        (Sym2.map eB (kernelBranchEndpoints G hmin hacyc e))
    have hsplit :
        (∏ e : KernelEdgeLabel G, actualFactor e) =
          (∏ C : (twoGraph G).ConnectedComponent,
            actualFactor (Sum.inl C)) *
          ∏ d : {e // e ∈ directBranchEdges G},
            actualFactor (Sum.inr d) := by
      change
        (∏ e : (twoGraph G).ConnectedComponent ⊕
            {d // d ∈ directBranchEdges G}, actualFactor e) = _
      exact Fintype.prod_sum_type actualFactor
    have hrelabel :
        (∏ e : KernelEdgeLabel G, actualFactor e) =
          ∏ j : Fin (3 * ell),
            pathKernelEdgeFactor M t (length j) x
              ((normalizedCubicFiniteMultiGraph
                G hconn hmin hell hscard hcubic).endpoints j) := by
      exact Fintype.prod_equiv eE
        actualFactor
        (fun j : Fin (3 * ell) =>
          pathKernelEdgeFactor M t (length j) x
            ((normalizedCubicFiniteMultiGraph
              G hconn hmin hell hscard hcubic).endpoints j))
        (fun e => by
          have hlen : length (eE e) = edgeLength e := by
            simp [length]
          rw [hlen, hend e])
    rw [← hrelabel, hsplit]
    dsimp only [actualFactor, edgeLength]
    ring
  · intro i
    exact normalizedCubicFiniteMultiGraph_degree
      G hconn hmin hell hscard hcubic i

end PerronWright.GraphCore
