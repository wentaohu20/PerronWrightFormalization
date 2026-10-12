import PerronWright.Enumeration.CubicRecoveredCoordinateAlignment

/-!
# Global recovered-coordinate fibre

This module transports the positive degree-two components of two subdivision
data through an equality of their reconstructed labelled graphs.  Combined
with the canonical branch/edge alignment, this gives the competing path
coordinate required by the recovered-coordinate converse.  Parallel kernel
edges remain separated because component transport is derived from the
intrinsic `KernelEdgeLabel` alignment.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Equality of ambient labelled graphs transports connected components of
their induced degree-two graphs. -/
noncomputable def degreeTwoComponentEquivOfGraphEq
    {k : ℕ} {G E : SimpleGraph (Fin k)} (h : G = E) :
    (twoGraph G).ConnectedComponent ≃
      (twoGraph E).ConnectedComponent := by
  subst E
  exact Equiv.refl _

@[simp]
theorem kernelEdgeLabelEquivOfGraphEq_inl
    {k : ℕ} {G E : SimpleGraph (Fin k)} (h : G = E)
    (C : (twoGraph G).ConnectedComponent) :
    kernelEdgeLabelEquivOfGraphEq h (.inl C) =
      .inl (degreeTwoComponentEquivOfGraphEq h C) := by
  subst E
  rfl

/-- If a specified component is the equality-transport of another one, their
induced component graphs are canonically isomorphic. -/
noncomputable def degreeTwoComponentGraphIsoOfGraphEq
    {k : ℕ} {G E : SimpleGraph (Fin k)} (h : G = E)
    (C : (twoGraph G).ConnectedComponent)
    (C' : (twoGraph E).ConnectedComponent)
    (hC : degreeTwoComponentEquivOfGraphEq h C = C') :
    C.toSimpleGraph ≃g C'.toSimpleGraph := by
  subst E
  change C = C' at hC
  subst C'
  exact SimpleGraph.Iso.refl

@[simp]
theorem degreeTwoComponentGraphIsoOfGraphEq_apply_val
    {k : ℕ} {G E : SimpleGraph (Fin k)} (h : G = E)
    (C : (twoGraph G).ConnectedComponent)
    (C' : (twoGraph E).ConnectedComponent)
    (hC : degreeTwoComponentEquivOfGraphEq h C = C')
    (x : C) :
    ((degreeTwoComponentGraphIsoOfGraphEq h C C' hC x).val.val) =
      x.val.val := by
  subst E
  change C = C' at hC
  subst C'
  rfl

@[simp]
theorem degreeTwoComponentGraphIsoOfGraphEq_symm_apply_val
    {k : ℕ} {G E : SimpleGraph (Fin k)} (h : G = E)
    (C : (twoGraph G).ConnectedComponent)
    (C' : (twoGraph E).ConnectedComponent)
    (hC : degreeTwoComponentEquivOfGraphEq h C = C')
    (x : C') :
    (((degreeTwoComponentGraphIsoOfGraphEq h C C' hC).symm x).val.val) =
      x.val.val := by
  subst E
  change C = C' at hC
  subst C'
  rfl

/-- Equality of path lengths gives the evident graph isomorphism between the
two standard finite paths. -/
def pathGraphIsoCongr {m n : ℕ} (h : m = n) :
    SimpleGraph.pathGraph m ≃g SimpleGraph.pathGraph n where
  toEquiv := finCongr h
  map_rel_iff' := by
    intro i j
    simp only [SimpleGraph.pathGraph_adj, finCongr_apply_coe]

/-- The orientation-aware internal-coordinate equivalence, promoted to an
isomorphism of standard path graphs. -/
noncomputable def CubicKernelSubdivisionDatum.recoveredPathIndexGraphIso
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) :
    SimpleGraph.pathGraph (D.profile.length e).val ≃g
      SimpleGraph.pathGraph
        (E.profile.length
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)).val :=
  if _hloop : (K.graph.endpoints e).IsDiag then
    pathGraphIsoCongr
      (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e)
  else if _hfirst :
      D.recoveredBranchCoordinatePerm K E hG
          (cubicKernelOrderedEndpoints K.graph e).1 =
        (cubicKernelOrderedEndpoints K.graph
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)).1 then
    pathGraphIsoCongr
      (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e)
  else
    (pathGraphRevIso (D.profile.length e).val).trans
      (pathGraphIsoCongr
        (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e))

@[simp]
theorem CubicKernelSubdivisionDatum.recoveredPathIndexGraphIso_toEquiv
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) :
    (D.recoveredPathIndexGraphIso K E hG e).toEquiv =
      D.recoveredPathIndexEquiv K E hG e := by
  unfold CubicKernelSubdivisionDatum.recoveredPathIndexGraphIso
    CubicKernelSubdivisionDatum.recoveredPathIndexEquiv
    pathGraphIsoCongr pathGraphRevIso
  split_ifs <;> rfl

/-- A positive edge in the first recovered coordinate system, transported to
the canonically aligned positive edge of the second datum. -/
noncomputable abbrev CubicKernelSubdivisionDatum.recoveredPositiveEdge
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val}) :
    {f : Fin (3 * ell) // 0 < (E.profile.length f).val} := by
  refine ⟨D.recoveredKernelEdgeCoordinatePerm K E hG e.1, ?_⟩
  rw [← D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e.1]
  exact e.2

@[simp]
theorem CubicKernelSubdivisionDatum.recoveredPositiveEdge_val
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val}) :
    (D.recoveredPositiveEdge K E hG e).1 =
      D.recoveredKernelEdgeCoordinatePerm K E hG e.1 :=
  rfl

/-- Intrinsic suppressed-edge transport sends the positive component of `D`
to the aligned positive component of `E`. -/
theorem CubicKernelSubdivisionDatum.recoveredPositiveEdgeComponent_intrinsic
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val}) :
    kernelEdgeLabelEquivOfGraphEq hG
        (.inl (D.positiveEdgeComponent K e)) =
      .inl (E.positiveEdgeComponent K
        (D.recoveredPositiveEdge K E hG e)) := by
  have hD :
      (D.recoveredKernelEdgeEquiv K).symm e.1 =
        (.inl (D.positiveEdgeComponent K e) :
          KernelEdgeLabel D.reconstructedGraph) := by
    apply (D.recoveredKernelEdgeEquiv K).injective
    rw [Equiv.apply_symm_apply]
    exact (D.recoveredKernelEdgeEquiv_positive K e).symm
  have hE :
      (E.recoveredKernelEdgeEquiv K).symm
          (D.recoveredKernelEdgeCoordinatePerm K E hG e.1) =
        (.inl (E.positiveEdgeComponent K
          (D.recoveredPositiveEdge K E hG e)) :
          KernelEdgeLabel E.reconstructedGraph) := by
    apply (E.recoveredKernelEdgeEquiv K).injective
    rw [Equiv.apply_symm_apply]
    exact (E.recoveredKernelEdgeEquiv_positive K
      (D.recoveredPositiveEdge K E hG e)).symm
  rw [← hD, ← hE]
  exact D.recoveredKernelEdgeCoordinatePerm_intrinsic K E hG e.1

/-- Equality transport identifies the two aligned positive degree-two
components. -/
theorem CubicKernelSubdivisionDatum.recoveredPositiveEdgeComponent_eq
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val}) :
    degreeTwoComponentEquivOfGraphEq hG
        (D.positiveEdgeComponent K e) =
      E.positiveEdgeComponent K
        (D.recoveredPositiveEdge K E hG e) := by
  apply Sum.inl.inj
  rw [← kernelEdgeLabelEquivOfGraphEq_inl hG]
  exact D.recoveredPositiveEdgeComponent_intrinsic K E hG e

/-- The aligned positive components, regarded as induced simple graphs. -/
noncomputable def CubicKernelSubdivisionDatum.recoveredPositiveEdgeComponentIso
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val}) :
    (D.positiveEdgeComponent K e).toSimpleGraph ≃g
      (E.positiveEdgeComponent K
        (D.recoveredPositiveEdge K E hG e)).toSimpleGraph :=
  degreeTwoComponentGraphIsoOfGraphEq hG
    (D.positiveEdgeComponent K e)
    (E.positiveEdgeComponent K (D.recoveredPositiveEdge K E hG e))
    (D.recoveredPositiveEdgeComponent_eq K E hG e)

@[simp]
theorem CubicKernelSubdivisionDatum.recoveredPositiveEdgeComponentIso_symm_apply_val
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val})
    (x : E.positiveEdgeComponent K
      (D.recoveredPositiveEdge K E hG e)) :
    ((D.recoveredPositiveEdgeComponentIso K E hG e).symm x).val.val =
      x.val.val := by
  unfold CubicKernelSubdivisionDatum.recoveredPositiveEdgeComponentIso
  exact degreeTwoComponentGraphIsoOfGraphEq_symm_apply_val _ _ _ _ _

/-- The second datum's canonical path coordinate, oriented and transported
back into the first datum's intrinsic positive component. -/
noncomputable def CubicKernelSubdivisionDatum.recoveredAlignedPositiveEdgePathIso
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val}) :
    SimpleGraph.pathGraph (D.profile.length e.1).val ≃g
      (D.positiveEdgeComponent K e).toSimpleGraph :=
  (D.recoveredPathIndexGraphIso K E hG e.1).trans
    ((E.positiveEdgePathIso K (D.recoveredPositiveEdge K E hG e)).trans
      (D.recoveredPositiveEdgeComponentIso K E hG e).symm)

/-- Evaluation of the transported path coordinate is exactly evaluation of
the coordinate-aligned label equivalence. -/
theorem CubicKernelSubdivisionDatum.recoveredAlignedPositiveEdgePathIso_apply_val
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val})
  (i : Fin (D.profile.length e.1).val) :
    (D.recoveredAlignedPositiveEdgePathIso K E hG e i).val.val =
      D.recoveredCoordinateAlignedLabels K E hG (.inr ⟨e.1, i⟩) := by
  rw [CubicKernelSubdivisionDatum.recoveredAlignedPositiveEdgePathIso,
    RelIso.trans_apply, RelIso.trans_apply,
    D.recoveredPositiveEdgeComponentIso_symm_apply_val K E hG,
    E.positiveEdgePathIso_apply_val,
    D.recoveredCoordinateAlignedLabels_path K E hG]
  rw [← D.recoveredPathIndexGraphIso_toEquiv K E hG e.1]
  rfl

/-- In a non-loop recovered component, the component vertex adjacent to the
first ordered branch endpoint is the first canonical path coordinate. -/
theorem CubicKernelSubdivisionDatum.positiveEdgeComponent_eq_first_of_adj
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val})
    (hnonloop : ¬(K.graph.endpoints e.1).IsDiag)
    (x : D.positiveEdgeComponent K e)
    (hx : D.reconstructedGraph.Adj x.val.val
      (D.branchLabel (cubicKernelOrderedEndpoints K.graph e.1).1)) :
    x = D.positiveEdgePathIso K e ⟨0, e.2⟩ := by
  let qL := D.positiveEdgeFirstBoundaryStub K e
  let qR := D.positiveEdgeLastBoundaryStub K e
  let q : Σ _x : D.positiveEdgeComponent K e, Fin k :=
    ⟨x, D.branchLabel (cubicKernelOrderedEndpoints K.graph e.1).1⟩
  have hq : q ∈ componentBoundaryStubs D.reconstructedGraph
      (D.positiveEdgeComponent K e) := by
    simp only [componentBoundaryStubs, Finset.mem_sigma, Finset.mem_univ,
      true_and, Finset.mem_filter,
      D.reconstructedGraph.mem_neighborFinset]
    refine ⟨hx, ?_⟩
    rw [D.branchVertex_degree_eq_three K]
    norm_num
  have hval : qL.val ≠ qR.val := by
    intro h
    exact D.positiveEdgeBoundaryStubs_ne K e (Subtype.ext h)
  have hpair : componentBoundaryStubs D.reconstructedGraph
      (D.positiveEdgeComponent K e) = {qL.val, qR.val} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact qL.property
      · exact qR.property
    · rw [Finset.card_pair hval,
        componentBoundaryStubs_card_eq_two D.reconstructedGraph
          (D.reconstructedTwoGraph_isAcyclic K)
          (D.positiveEdgeComponent K e)]
  have hqpair : q = qL.val ∨ q = qR.val := by
    have hmem := hq
    rw [hpair] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hqpair with hfirst | hlast
  · have hxfirst : x = qL.val.1 := congrArg Sigma.fst hfirst
    rw [D.positiveEdgePathIso_zero_eq_firstStub K e]
    exact hxfirst
  · exfalso
    have hbranch :
        D.branchLabel (cubicKernelOrderedEndpoints K.graph e.1).1 =
          D.branchLabel (cubicKernelOrderedEndpoints K.graph e.1).2 :=
      congrArg Sigma.snd hlast
    have hordered :
        (cubicKernelOrderedEndpoints K.graph e.1).1 =
          (cubicKernelOrderedEndpoints K.graph e.1).2 := by
      change D.labels (.inl _) = D.labels (.inl _) at hbranch
      exact Sum.inl.inj (D.labels.injective hbranch)
    exact hnonloop
      ((cubicKernelOrderedEndpoints_eq_iff_isDiag K.graph e.1).1 hordered)

/-- On a non-loop, the transported coordinate starts at the first canonical
vertex of the recovered component.  The direct/reversed endpoint dichotomy
is exactly what fixes this orientation. -/
theorem CubicKernelSubdivisionDatum.recoveredAlignedPositiveEdgePathIso_first
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : {e : Fin (3 * ell) // 0 < (D.profile.length e).val})
    (hnonloop : ¬(K.graph.endpoints e.1).IsDiag) :
    D.recoveredAlignedPositiveEdgePathIso K E hG e ⟨0, e.2⟩ =
      D.positiveEdgePathIso K e ⟨0, e.2⟩ := by
  apply D.positiveEdgeComponent_eq_first_of_adj K e hnonloop
  let f := D.recoveredPositiveEdge K E hG e
  let oD := cubicKernelOrderedEndpoints K.graph e.1
  let oE := cubicKernelOrderedEndpoints K.graph f.1
  have hAdjTransport (a b : Fin k) :
      D.reconstructedGraph.Adj a b ↔ E.reconstructedGraph.Adj a b := by
    rw [hG]
  by_cases hfirst :
      D.recoveredBranchCoordinatePerm K E hG oD.1 = oE.1
  · have hindex :
        D.recoveredPathIndexEquiv K E hG e.1 ⟨0, e.2⟩ =
          (⟨0, f.2⟩ : Fin (E.profile.length f.1).val) := by
      rw [D.recoveredPathIndexEquiv_of_nonloop_direct K E hG e.1
        hnonloop hfirst]
      apply Fin.ext
      rfl
    have hadj := E.firstPathLabel_adj_firstBranch K f
    apply (hAdjTransport _ _).2
    rw [D.recoveredAlignedPositiveEdgePathIso_apply_val K E hG e]
    rw [D.recoveredCoordinateAlignedLabels_path K E hG, hindex]
    rw [← D.branchLabel_recoveredBranchCoordinatePerm K E hG oD.1,
      hfirst]
    exact hadj
  · have hreversed :=
      D.orderedEndpoints_reversed_of_first_ne K E hG e.1 hfirst
    have hindex :
        D.recoveredPathIndexEquiv K E hG e.1 ⟨0, e.2⟩ =
          E.positiveEdgeLastIndex K f := by
      rw [D.recoveredPathIndexEquiv_of_nonloop_reversed K E hG e.1
        hnonloop hfirst]
      apply Fin.ext
      simp only [Equiv.trans_apply, finCongr_apply_coe,
        E.positiveEdgeLastIndex_val]
      dsimp only [f, CubicKernelSubdivisionDatum.recoveredPositiveEdge]
      rw [← D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e.1]
      rfl
    have hadj := E.positiveEdgePathIso_last_adj_secondBranch K f
    apply (hAdjTransport _ _).2
    rw [D.recoveredAlignedPositiveEdgePathIso_apply_val K E hG e]
    rw [D.recoveredCoordinateAlignedLabels_path K E hG, hindex]
    rw [← D.branchLabel_recoveredBranchCoordinatePerm K E hG oD.1,
      hreversed.1]
    simpa only [E.positiveEdgePathIso_apply_val] using hadj

/-- After canonical recovery of branch, edge, and path coordinates, the
complete fibre over one reconstructed labelled graph is one unique Boolean
loop-orientation orbit. -/
theorem CubicKernelSubdivisionDatum.existsUnique_reverseLoops_eq_alignedDatum
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    ∃! A : Finset (CubicKernelLoopEdge K.graph),
      D.reverseLoops A = D.recoveredCoordinateAlignedDatum K E hG := by
  exact existsUnique_reverseLoops_eq_of_recovered_coordinates
    K D (D.recoveredCoordinateAlignedLabels K E hG)
    (D.recoveredCoordinateAlignedLabels_branch K E hG)
    (D.recoveredAlignedPositiveEdgePathIso K E hG)
    (D.recoveredAlignedPositiveEdgePathIso_apply_val K E hG)
    (D.recoveredAlignedPositiveEdgePathIso_first K E hG)

/-- As a consequence rather than an extra edge-table argument, the aligned
datum reconstructs the second graph (and hence the first graph) exactly. -/
theorem CubicKernelSubdivisionDatum.recoveredCoordinateAlignedDatum_reconstructedGraph
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    (D.recoveredCoordinateAlignedDatum K E hG).reconstructedGraph =
      E.reconstructedGraph := by
  obtain ⟨A, hA, _hunique⟩ :=
    D.existsUnique_reverseLoops_eq_alignedDatum K E hG
  rw [← hA, D.reverseLoops_reconstructedGraph A, hG]

end PerronWright.GraphCore
