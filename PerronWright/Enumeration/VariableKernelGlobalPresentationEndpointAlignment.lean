import PerronWright.Enumeration.VariableKernelGlobalPresentationShapeAlignment

/-!
# Endpoint-table alignment for global variable-kernel presentations

The recovered branch and suppressed-edge equivalences of two presentations
over one labelled graph transport the complete endpoint table.  The argument
passes through intrinsic `KernelEdgeLabel`s, so parallel kernel edges remain
distinct.  We then relabel the source kernel by the recovered source-side
permutations, cast the two finite coordinate types to the target shape
counts, and prove equality with the target edge-labelled multigraph and
bounded kernel.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Relabel both coordinate types of a finite multigraph by equivalences
which are allowed to change the displayed finite cardinalities. -/
def variableFiniteMultiGraphCoordinateRelabel
    {nv ne nv' ne' : ℕ}
    (gammaV : Fin nv ≃ Fin nv') (gammaE : Fin ne ≃ Fin ne')
    (H : PerronWright.FiniteMultiGraph nv ne) :
    PerronWright.FiniteMultiGraph nv' ne' where
  endpoints e := Sym2.map gammaV (H.endpoints (gammaE.symm e))

@[simp] theorem variableFiniteMultiGraphCoordinateRelabel_endpoints
    {nv ne nv' ne' : ℕ}
    (gammaV : Fin nv ≃ Fin nv') (gammaE : Fin ne ≃ Fin ne')
    (H : PerronWright.FiniteMultiGraph nv ne) (e : Fin ne') :
    (variableFiniteMultiGraphCoordinateRelabel gammaV gammaE H).endpoints e =
      Sym2.map gammaV (H.endpoints (gammaE.symm e)) :=
  rfl

/-- Fixed-cardinality relabelling followed by a cross-cardinality cast is
the single relabelling by the composite coordinate equivalences. -/
theorem variableFiniteMultiGraphCoordinateRelabel_after_fixed
    {nv ne nv' ne' : ℕ}
    (gamma : Equiv.Perm (Fin nv) × Equiv.Perm (Fin ne))
    (deltaV : Fin nv ≃ Fin nv') (deltaE : Fin ne ≃ Fin ne')
    (H : PerronWright.FiniteMultiGraph nv ne) :
    variableFiniteMultiGraphCoordinateRelabel deltaV deltaE
        (boundedFiniteMultiGraphCoordinateRelabel gamma H) =
      variableFiniteMultiGraphCoordinateRelabel
        (gamma.1.trans deltaV) (gamma.2.trans deltaE) H := by
  cases H
  simp [variableFiniteMultiGraphCoordinateRelabel,
    boundedFiniteMultiGraphCoordinateRelabel,
    Function.comp_def, Equiv.trans_apply, Sym2.map_map]

/-- A finite multigraph is determined by its full edge-labelled endpoint
table. -/
private theorem finiteMultiGraph_eq_of_endpoints_eq
    {v e : ℕ}
    {H H' : PerronWright.FiniteMultiGraph v e}
    (h : H.endpoints = H'.endpoints) : H = H' := by
  cases H with
  | mk endpoints =>
      cases H' with
      | mk endpoints' =>
          dsimp only at h
          subst endpoints'
          rfl

/-- Equality of the two displayed shape counts and equality after the
corresponding cross-cardinality casts recover literal equality of bounded
kernel shapes. -/
private theorem boundedKernelShape_eq_of_castBackCoordinateRelabelGraph
    {ell : ℕ} (A B : BoundedKernelShape ell)
    (gamma : Equiv.Perm (Fin A.1.val) × Equiv.Perm (Fin A.2.1.val))
    (hV : A.1.val = B.1.val) (hE : A.2.1.val = B.2.1.val)
    (hgraph :
      variableFiniteMultiGraphCoordinateRelabel (finCongr hV) (finCongr hE)
          (boundedFiniteMultiGraphCoordinateRelabel gamma
            (boundedKernelFiniteMultiGraph A)) =
        boundedKernelFiniteMultiGraph B) :
    (⟨A.1, A.2.1,
      (boundedFiniteMultiGraphCoordinateRelabel gamma
        (boundedKernelFiniteMultiGraph A)).endpoints⟩ :
      BoundedKernelShape ell) = B := by
  rcases A with ⟨av, ae, aends⟩
  rcases B with ⟨bv, be, bends⟩
  have hV' : av = bv := Fin.ext hV
  have hE' : ae = be := Fin.ext hE
  cases hV'
  cases hE'
  change
    (⟨av, ae,
      (boundedFiniteMultiGraphCoordinateRelabel gamma ⟨aends⟩).endpoints⟩ :
        BoundedKernelShape ell) = ⟨av, ae, bends⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      have hendpoints := congrArg
        (fun H : PerronWright.FiniteMultiGraph av.val ae.val ↦ H.endpoints)
        hgraph
      simpa [variableFiniteMultiGraphCoordinateRelabel,
        boundedFiniteMultiGraphCoordinateRelabel,
        boundedKernelFiniteMultiGraph] using hendpoints

/-- Branch endpoints commute with equality transport of the labelled graph.
The minimum-degree and degree-two-acyclicity witnesses disappear by proof
irrelevance. -/
theorem variableKernelBranchEndpoints_equivOfGraphEq
    {k : ℕ} {G H : SimpleGraph (Fin k)} (h : G = H)
    (hminG : ∀ v, 2 ≤ G.degree v)
    (hminH : ∀ v, 2 ≤ H.degree v)
    (hacycG : (twoGraph G).IsAcyclic)
    (hacycH : (twoGraph H).IsAcyclic)
    (e : KernelEdgeLabel G) :
    Sym2.map (variableBranchingVertexEquivOfGraphEq h)
        (kernelBranchEndpoints G hminG hacycG e) =
      kernelBranchEndpoints H hminH hacycH
        (variableKernelEdgeLabelEquivOfGraphEq h e) := by
  subst H
  have hminH_eq : hminH = hminG := Subsingleton.elim _ _
  have hacycH_eq : hacycH = hacycG := Subsingleton.elim _ _
  subst hminH
  subst hacycH
  change Sym2.map (fun x ↦ x)
      (kernelBranchEndpoints G hminG hacycG e) =
    kernelBranchEndpoints G hminG hacycG e
  exact congrFun Sym2.map_id _

namespace BoundedKernelPresentation

/-- The recovered cross-presentation coordinates transport the full labelled
endpoint table.  Since the edge coordinate passes through
`KernelEdgeLabel`, the statement retains parallel-edge labels. -/
theorem kernelEndpoints_globalRecoveredCoordinateEquiv
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (e : Fin P.1.toLabelledBoundedKernel.shape.2.1.val) :
    Q.1.toLabelledBoundedKernel.shape.2.2
        (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG e) =
      Sym2.map (P.globalRecoveredBranchCoordinateEquiv Q hG)
        (P.1.toLabelledBoundedKernel.shape.2.2 e) := by
  let KP := P.1.toLabelledBoundedKernel
  let KQ := Q.1.toLabelledBoundedKernel
  let hminP := P.2.reconstructedGraph_minDegree_two
  let hminQ := Q.2.reconstructedGraph_minDegree_two
  let hacycP := P.2.reconstructedTwoGraph_isAcyclic
    KP P.1.connected hell
  let hacycQ := Q.2.reconstructedTwoGraph_isAcyclic
    KQ Q.1.connected hell
  let xP : KernelEdgeLabel P.2.reconstructedGraph :=
    (P.2.recoveredKernelEdgeEquiv KP).symm e
  have hx : variableKernelEdgeLabelEquivOfGraphEq hG xP =
      (Q.2.recoveredKernelEdgeEquiv KQ).symm
        (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG e) :=
    P.globalRecoveredKernelEdgeCoordinateEquiv_intrinsic Q hG e
  have htransport := variableKernelBranchEndpoints_equivOfGraphEq hG
    hminP hminQ hacycP hacycQ xP
  have hP := congrFun
    (P.2.recoveredKernelBranchEndpointTable KP P.1.connected hell) e
  have hQ := congrFun
    (Q.2.recoveredKernelBranchEndpointTable KQ Q.1.connected hell)
      (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG e)
  calc
    KQ.shape.2.2 (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG e) =
        Sym2.map (Q.2.branchLabelEquivBranching KQ).symm
          (kernelBranchEndpoints Q.2.reconstructedGraph hminQ hacycQ
            ((Q.2.recoveredKernelEdgeEquiv KQ).symm
              (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG e))) :=
      hQ.symm
    _ = Sym2.map (Q.2.branchLabelEquivBranching KQ).symm
          (kernelBranchEndpoints Q.2.reconstructedGraph hminQ hacycQ
            (variableKernelEdgeLabelEquivOfGraphEq hG xP)) := by
      rw [hx]
    _ = Sym2.map (Q.2.branchLabelEquivBranching KQ).symm
          (Sym2.map (variableBranchingVertexEquivOfGraphEq hG)
            (kernelBranchEndpoints P.2.reconstructedGraph
              hminP hacycP xP)) := by
      rw [htransport]
    _ = Sym2.map (P.globalRecoveredBranchCoordinateEquiv Q hG)
          (Sym2.map (P.2.branchLabelEquivBranching KP).symm
            (kernelBranchEndpoints P.2.reconstructedGraph
              hminP hacycP xP)) := by
      simp only [Sym2.map_map]
      apply Sym2.map_congr
      intro v _hv
      simp only [globalRecoveredBranchCoordinateEquiv,
        Function.comp_apply, Equiv.trans_apply]
      rw [(P.2.branchLabelEquivBranching KP).apply_symm_apply v]
    _ = Sym2.map (P.globalRecoveredBranchCoordinateEquiv Q hG)
          (KP.shape.2.2 e) := by
      simpa only [boundedKernelFiniteMultiGraph] using
        congrArg (Sym2.map
          (P.globalRecoveredBranchCoordinateEquiv Q hG)) hP

/-- At the level of complete edge-labelled multigraphs, the heterogeneous
recovered coordinate equivalences carry the source kernel to the target
kernel. -/
theorem finiteMultiGraph_globalRecoveredCoordinateEquiv
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    variableFiniteMultiGraphCoordinateRelabel
        (P.globalRecoveredBranchCoordinateEquiv Q hG)
        (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG)
        (boundedKernelFiniteMultiGraph
          P.1.toLabelledBoundedKernel.shape) =
      boundedKernelFiniteMultiGraph Q.1.toLabelledBoundedKernel.shape := by
  apply finiteMultiGraph_eq_of_endpoints_eq
  funext f
  let e := (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG).symm f
  calc
    (variableFiniteMultiGraphCoordinateRelabel
        (P.globalRecoveredBranchCoordinateEquiv Q hG)
        (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG)
        (boundedKernelFiniteMultiGraph
          P.1.toLabelledBoundedKernel.shape)).endpoints f =
        Sym2.map (P.globalRecoveredBranchCoordinateEquiv Q hG)
          (P.1.toLabelledBoundedKernel.shape.2.2 e) := by
      rfl
    _ = Q.1.toLabelledBoundedKernel.shape.2.2
          (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG e) :=
      (P.kernelEndpoints_globalRecoveredCoordinateEquiv
        hell Q hG e).symm
    _ = (boundedKernelFiniteMultiGraph
          Q.1.toLabelledBoundedKernel.shape).endpoints f := by
      rw [(P.globalRecoveredKernelEdgeCoordinateEquiv Q hG).apply_symm_apply]
      rfl

/-- First relabel the source kernel inside its own cardinality stratum, then
cast both finite coordinate types to the target counts. -/
def castBackCoordinateRelabelGraph
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    PerronWright.FiniteMultiGraph
      Q.1.toLabelledBoundedKernel.shape.1.val
      Q.1.toLabelledBoundedKernel.shape.2.1.val :=
  variableFiniteMultiGraphCoordinateRelabel
    (P.branchCoordinateCountCast Q hG)
    (P.kernelEdgeCoordinateCountCast Q hG)
    (boundedFiniteMultiGraphCoordinateRelabel
      (P.globalRecoveredCoordinatePerm Q hG)
      (boundedKernelFiniteMultiGraph
        P.1.toLabelledBoundedKernel.shape))

/-- The cast-back relabelled source graph is exactly the target edge-labelled
multigraph.  This is stronger than equality of support graphs. -/
theorem castBackCoordinateRelabelGraph_eq_target
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    P.castBackCoordinateRelabelGraph Q hG =
      boundedKernelFiniteMultiGraph Q.1.toLabelledBoundedKernel.shape := by
  let gamma := P.globalRecoveredCoordinatePerm Q hG
  let deltaV := P.branchCoordinateCountCast Q hG
  let deltaE := P.kernelEdgeCoordinateCountCast Q hG
  calc
    P.castBackCoordinateRelabelGraph Q hG =
        variableFiniteMultiGraphCoordinateRelabel
          (gamma.1.trans deltaV) (gamma.2.trans deltaE)
          (boundedKernelFiniteMultiGraph
            P.1.toLabelledBoundedKernel.shape) :=
      variableFiniteMultiGraphCoordinateRelabel_after_fixed
        gamma deltaV deltaE _
    _ = variableFiniteMultiGraphCoordinateRelabel
          (P.globalRecoveredBranchCoordinateEquiv Q hG)
          (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG)
          (boundedKernelFiniteMultiGraph
            P.1.toLabelledBoundedKernel.shape) := by
      have hV : gamma.1.trans deltaV =
          P.globalRecoveredBranchCoordinateEquiv Q hG := by
        apply Equiv.ext
        intro v
        exact P.branchCoordinateCountCast_globalRecoveredBranchCoordinatePerm
          Q hG v
      have hE : gamma.2.trans deltaE =
          P.globalRecoveredKernelEdgeCoordinateEquiv Q hG := by
        apply Equiv.ext
        intro e
        exact
          P.kernelEdgeCoordinateCountCast_globalRecoveredKernelEdgeCoordinatePerm
            Q hG e
      rw [hV, hE]
    _ = boundedKernelFiniteMultiGraph
          Q.1.toLabelledBoundedKernel.shape :=
      P.finiteMultiGraph_globalRecoveredCoordinateEquiv hell Q hG

/-- The cast-back relabelled source, packaged as a connected bounded kernel
in the target cardinality stratum.  Its proof fields are inherited from the
target after the exact endpoint-table equality. -/
noncomputable def castBackCoordinateRelabelKernel
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    LabelledConnectedBoundedKernel ell where
  toLabelledBoundedKernel :=
    { shape :=
        ⟨Q.1.toLabelledBoundedKernel.shape.1,
          Q.1.toLabelledBoundedKernel.shape.2.1,
          (P.castBackCoordinateRelabelGraph Q hG).endpoints⟩
      minDegree := by
        intro v
        rw [P.castBackCoordinateRelabelGraph_eq_target hell Q hG]
        exact Q.1.toLabelledBoundedKernel.minDegree v
      excess := Q.1.toLabelledBoundedKernel.excess }
  connected := by
    rw [P.castBackCoordinateRelabelGraph_eq_target hell Q hG]
    exact Q.1.connected

/-- Exact bounded-kernel alignment after source permutation relabelling and
the two count casts. -/
theorem castBackCoordinateRelabelKernel_eq_target
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    P.castBackCoordinateRelabelKernel hell Q hG = Q.1 := by
  apply LabelledConnectedBoundedKernel.ext
  change
    (⟨Q.1.toLabelledBoundedKernel.shape.1,
      Q.1.toLabelledBoundedKernel.shape.2.1,
      (P.castBackCoordinateRelabelGraph Q hG).endpoints⟩ :
        BoundedKernelShape ell) = Q.1.toLabelledBoundedKernel.shape
  rw [P.castBackCoordinateRelabelGraph_eq_target hell Q hG]
  rfl

/-- After eliminating the two propositionally equal shape counts, the
source-side recovered coordinate permutation carries the original connected
bounded kernel itself to the target kernel. -/
theorem kernel_coordinateRelabel_globalRecoveredCoordinatePerm
    {k ell : ℕ} (hell : 0 < ell)
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    P.1.coordinateRelabel (P.globalRecoveredCoordinatePerm Q hG) = Q.1 := by
  apply LabelledConnectedBoundedKernel.ext
  let hV := P.vertexCount_eq_of_reconstructedGraph_eq Q hG
  let hE := P.edgeCount_eq_of_reconstructedGraph_eq Q hG
  refine boundedKernelShape_eq_of_castBackCoordinateRelabelGraph
    P.1.toLabelledBoundedKernel.shape
    Q.1.toLabelledBoundedKernel.shape
    (P.globalRecoveredCoordinatePerm Q hG) hV hE ?_
  simpa [castBackCoordinateRelabelGraph,
    branchCoordinateCountCast, kernelEdgeCoordinateCountCast,
    hV, hE] using
    P.castBackCoordinateRelabelGraph_eq_target hell Q hG

end BoundedKernelPresentation

end PerronWright.GraphCore
