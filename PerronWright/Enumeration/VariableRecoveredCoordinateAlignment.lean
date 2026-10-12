import PerronWright.Enumeration.VariableRecoveredKernelEdgeNaturality

/-!
# Fixed-kernel recovered-coordinate alignment for bounded kernels

Two subdivision data over one bounded kernel and with the same reconstructed
labelled graph canonically determine branch- and suppressed-edge-coordinate
permutations.  Intrinsic suppressed-edge length then supplies the dependent
path-index casts.  Non-loop paths are oriented by the aligned first endpoint;
loop paths are deliberately left unreversed, so the residual ambiguity is
exactly the Boolean loop-orientation action.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Intrinsic suppressed-edge length is invariant under equality transport
of the ambient labelled graph. -/
theorem variableKernelEdgeInternalLength_equivOfGraphEq
    {k : ℕ} {G H : SimpleGraph (Fin k)} (h : G = H)
    (e : KernelEdgeLabel G) :
    kernelEdgeInternalLength H (variableKernelEdgeLabelEquivOfGraphEq h e) =
      kernelEdgeInternalLength G e := by
  subst H
  rfl

/-- The canonical branch-coordinate permutation between two subdivision
data over one fixed bounded kernel. -/
noncomputable def BoundedKernelSubdivisionDatum.recoveredBranchCoordinatePerm
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    Equiv.Perm (Fin K.shape.1.val) :=
  (D.branchLabelEquivBranching K).trans
    ((variableBranchingVertexEquivOfGraphEq hG).trans
      (E.branchLabelEquivBranching K).symm)

/-- Recovered branch coordinates carry exactly the same original vertex
labels. -/
theorem BoundedKernelSubdivisionDatum.branchLabel_recoveredBranchCoordinatePerm
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (v : Fin K.shape.1.val) :
    E.branchLabel (D.recoveredBranchCoordinatePerm K E hG v) =
      D.branchLabel v := by
  rw [← E.branchLabelEquivBranching_apply K,
    ← D.branchLabelEquivBranching_apply K]
  simp only [BoundedKernelSubdivisionDatum.recoveredBranchCoordinatePerm,
    Equiv.trans_apply, Equiv.apply_symm_apply,
    variableBranchingVertexEquivOfGraphEq_apply_val]

/-- The recovered suppressed-edge coordinate permutation preserves every
subdivision length. -/
theorem BoundedKernelSubdivisionDatum.profile_length_recoveredKernelEdgeCoordinatePerm
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.shape.2.1.val) :
    (D.profile.length e).val =
      (E.profile.length
        (D.recoveredKernelEdgeCoordinatePerm K E hG e)).val := by
  calc
    (D.profile.length e).val = D.recoveredKernelEdgeLength K e :=
      (D.recoveredKernelEdgeLength_eq K e).symm
    _ = kernelEdgeInternalLength D.reconstructedGraph
        ((D.recoveredKernelEdgeEquiv K).symm e) := rfl
    _ = kernelEdgeInternalLength E.reconstructedGraph
        (variableKernelEdgeLabelEquivOfGraphEq hG
          ((D.recoveredKernelEdgeEquiv K).symm e)) :=
      (variableKernelEdgeInternalLength_equivOfGraphEq hG _).symm
    _ = kernelEdgeInternalLength E.reconstructedGraph
        ((E.recoveredKernelEdgeEquiv K).symm
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)) := by
      rw [D.recoveredKernelEdgeCoordinatePerm_intrinsic K E hG e]
    _ = E.recoveredKernelEdgeLength K
        (D.recoveredKernelEdgeCoordinatePerm K E hG e) := rfl
    _ = (E.profile.length
        (D.recoveredKernelEdgeCoordinatePerm K E hG e)).val :=
      E.recoveredKernelEdgeLength_eq K _

/-- Recovered coordinates carry the complete edge-labelled endpoint table.
The positivity hypothesis is needed only to obtain acyclicity of the
degree-two graphs from the connected positive-surplus kernel. -/
theorem BoundedKernelSubdivisionDatum.kernelEndpoints_recoveredCoordinatePerm
    {k ell : ℕ} (hell : 0 < ell)
    (K : LabelledConnectedBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K.toLabelledBoundedKernel)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.toLabelledBoundedKernel.shape.2.1.val) :
    (boundedKernelFiniteMultiGraph K.toLabelledBoundedKernel.shape).endpoints
        (D.recoveredKernelEdgeCoordinatePerm
          K.toLabelledBoundedKernel E hG e) =
      Sym2.map
        (D.recoveredBranchCoordinatePerm
          K.toLabelledBoundedKernel E hG)
        ((boundedKernelFiniteMultiGraph
          K.toLabelledBoundedKernel.shape).endpoints e) := by
  let K0 := K.toLabelledBoundedKernel
  let hminD := D.reconstructedGraph_minDegree_two
  let hminE := E.reconstructedGraph_minDegree_two
  let hacycD := D.reconstructedTwoGraph_isAcyclic K0 K.connected hell
  let hacycE := E.reconstructedTwoGraph_isAcyclic K0 K.connected hell
  let xD : KernelEdgeLabel D.reconstructedGraph :=
    (D.recoveredKernelEdgeEquiv K0).symm e
  have hx : variableKernelEdgeLabelEquivOfGraphEq hG xD =
      (E.recoveredKernelEdgeEquiv K0).symm
        (D.recoveredKernelEdgeCoordinatePerm K0 E hG e) :=
    D.recoveredKernelEdgeCoordinatePerm_intrinsic K0 E hG e
  have htransport := variableKernelBranchEndpoints_equivOfGraphEq hG
    hminD hminE hacycD hacycE xD
  have hD := congrFun
    (D.recoveredKernelBranchEndpointTable K0 K.connected hell) e
  have hE := congrFun
    (E.recoveredKernelBranchEndpointTable K0 K.connected hell)
      (D.recoveredKernelEdgeCoordinatePerm K0 E hG e)
  calc
    (boundedKernelFiniteMultiGraph K0.shape).endpoints
        (D.recoveredKernelEdgeCoordinatePerm K0 E hG e) =
        Sym2.map (E.branchLabelEquivBranching K0).symm
          (kernelBranchEndpoints E.reconstructedGraph hminE hacycE
            ((E.recoveredKernelEdgeEquiv K0).symm
              (D.recoveredKernelEdgeCoordinatePerm K0 E hG e))) := hE.symm
    _ = Sym2.map (E.branchLabelEquivBranching K0).symm
          (kernelBranchEndpoints E.reconstructedGraph hminE hacycE
            (variableKernelEdgeLabelEquivOfGraphEq hG xD)) := by
      rw [hx]
    _ = Sym2.map (E.branchLabelEquivBranching K0).symm
          (Sym2.map (variableBranchingVertexEquivOfGraphEq hG)
            (kernelBranchEndpoints D.reconstructedGraph hminD hacycD xD)) := by
      rw [htransport]
    _ = Sym2.map (D.recoveredBranchCoordinatePerm K0 E hG)
          (Sym2.map (D.branchLabelEquivBranching K0).symm
            (kernelBranchEndpoints D.reconstructedGraph hminD hacycD xD)) := by
      simp only [Sym2.map_map]
      apply Sym2.map_congr
      intro v _hv
      simp only [BoundedKernelSubdivisionDatum.recoveredBranchCoordinatePerm,
        Function.comp_apply, Equiv.trans_apply]
      rw [(D.branchLabelEquivBranching K0).apply_symm_apply v]
    _ = Sym2.map (D.recoveredBranchCoordinatePerm K0 E hG)
          ((boundedKernelFiniteMultiGraph K0.shape).endpoints e) := by
      rw [hD]

/-- After recovered branch and edge coordinates have been aligned, the two
ordered endpoint pairs agree either directly or in the opposite order. -/
theorem BoundedKernelSubdivisionDatum.orderedEndpoints_recoveredCoordinatePerm
    {k ell : ℕ} (hell : 0 < ell)
    (K : LabelledConnectedBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K.toLabelledBoundedKernel)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.toLabelledBoundedKernel.shape.2.1.val) :
    let K0 := K.toLabelledBoundedKernel
    let sigmaV := D.recoveredBranchCoordinatePerm K0 E hG
    let sigmaE := D.recoveredKernelEdgeCoordinatePerm K0 E hG
    let oD := boundedKernelOrderedEndpoints K0.shape e
    let oE := boundedKernelOrderedEndpoints K0.shape (sigmaE e)
    (sigmaV oD.1 = oE.1 ∧ sigmaV oD.2 = oE.2) ∨
      (sigmaV oD.1 = oE.2 ∧ sigmaV oD.2 = oE.1) := by
  dsimp only
  apply Sym2.eq_iff.mp
  calc
    s((D.recoveredBranchCoordinatePerm K.toLabelledBoundedKernel E hG)
          (boundedKernelOrderedEndpoints
            K.toLabelledBoundedKernel.shape e).1,
        (D.recoveredBranchCoordinatePerm K.toLabelledBoundedKernel E hG)
          (boundedKernelOrderedEndpoints
            K.toLabelledBoundedKernel.shape e).2) =
        Sym2.map
          (D.recoveredBranchCoordinatePerm K.toLabelledBoundedKernel E hG)
          ((boundedKernelFiniteMultiGraph
            K.toLabelledBoundedKernel.shape).endpoints e) := by
      simpa only [boundedKernelFiniteMultiGraph, Sym2.map_mk] using
        congrArg
          (Sym2.map
            (D.recoveredBranchCoordinatePerm
              K.toLabelledBoundedKernel E hG))
          (boundedKernelOrderedEndpoints_mk
            K.toLabelledBoundedKernel e)
    _ = (boundedKernelFiniteMultiGraph
          K.toLabelledBoundedKernel.shape).endpoints
          (D.recoveredKernelEdgeCoordinatePerm
            K.toLabelledBoundedKernel E hG e) :=
      (D.kernelEndpoints_recoveredCoordinatePerm hell K E hG e).symm
    _ = s((boundedKernelOrderedEndpoints K.toLabelledBoundedKernel.shape
            (D.recoveredKernelEdgeCoordinatePerm
              K.toLabelledBoundedKernel E hG e)).1,
          (boundedKernelOrderedEndpoints K.toLabelledBoundedKernel.shape
            (D.recoveredKernelEdgeCoordinatePerm
              K.toLabelledBoundedKernel E hG e)).2) :=
      (boundedKernelOrderedEndpoints_mk K.toLabelledBoundedKernel _).symm

/-- Failure of direct first-endpoint alignment forces the reversed endpoint
alignment. -/
theorem BoundedKernelSubdivisionDatum.orderedEndpoints_reversed_of_first_ne
    {k ell : ℕ} (hell : 0 < ell)
    (K : LabelledConnectedBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K.toLabelledBoundedKernel)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.toLabelledBoundedKernel.shape.2.1.val)
    (hfirst :
      D.recoveredBranchCoordinatePerm K.toLabelledBoundedKernel E hG
          (boundedKernelOrderedEndpoints
            K.toLabelledBoundedKernel.shape e).1 ≠
        (boundedKernelOrderedEndpoints K.toLabelledBoundedKernel.shape
          (D.recoveredKernelEdgeCoordinatePerm
            K.toLabelledBoundedKernel E hG e)).1) :
    D.recoveredBranchCoordinatePerm K.toLabelledBoundedKernel E hG
        (boundedKernelOrderedEndpoints K.toLabelledBoundedKernel.shape e).1 =
      (boundedKernelOrderedEndpoints K.toLabelledBoundedKernel.shape
        (D.recoveredKernelEdgeCoordinatePerm
          K.toLabelledBoundedKernel E hG e)).2 ∧
    D.recoveredBranchCoordinatePerm K.toLabelledBoundedKernel E hG
        (boundedKernelOrderedEndpoints K.toLabelledBoundedKernel.shape e).2 =
      (boundedKernelOrderedEndpoints K.toLabelledBoundedKernel.shape
        (D.recoveredKernelEdgeCoordinatePerm
          K.toLabelledBoundedKernel E hG e)).1 := by
  rcases D.orderedEndpoints_recoveredCoordinatePerm hell K E hG e with
    hdirect | hreversed
  · exact False.elim (hfirst hdirect.1)
  · exact hreversed

/-- The recovered edge permutation preserves the loop predicate. -/
theorem BoundedKernelSubdivisionDatum.kernelEndpoint_isDiag_recoveredCoordinatePerm
    {k ell : ℕ} (hell : 0 < ell)
    (K : LabelledConnectedBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K.toLabelledBoundedKernel)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.toLabelledBoundedKernel.shape.2.1.val) :
    ((boundedKernelFiniteMultiGraph K.toLabelledBoundedKernel.shape).endpoints
        (D.recoveredKernelEdgeCoordinatePerm
          K.toLabelledBoundedKernel E hG e)).IsDiag ↔
      ((boundedKernelFiniteMultiGraph
        K.toLabelledBoundedKernel.shape).endpoints e).IsDiag := by
  rw [D.kernelEndpoints_recoveredCoordinatePerm hell K E hG e]
  exact Sym2.isDiag_map
    (D.recoveredBranchCoordinatePerm
      K.toLabelledBoundedKernel E hG).injective

/-- The internal path-coordinate equivalence on one recovered edge.  Loops
are left unreversed; non-loops are oriented by their aligned first
endpoints. -/
noncomputable def BoundedKernelSubdivisionDatum.recoveredPathIndexEquiv
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.shape.2.1.val) :
    Fin (D.profile.length e).val ≃
      Fin (E.profile.length
        (D.recoveredKernelEdgeCoordinatePerm K E hG e)).val :=
  if _hloop :
      ((boundedKernelFiniteMultiGraph K.shape).endpoints e).IsDiag then
    finCongr (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e)
  else if _hfirst :
      D.recoveredBranchCoordinatePerm K E hG
          (boundedKernelOrderedEndpoints K.shape e).1 =
        (boundedKernelOrderedEndpoints K.shape
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)).1 then
    finCongr (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e)
  else
    (Fin.revPerm : Equiv.Perm (Fin (D.profile.length e).val)).trans
      (finCongr
        (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e))

@[simp] theorem BoundedKernelSubdivisionDatum.recoveredPathIndexEquiv_of_loop
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.shape.2.1.val)
    (hloop : ((boundedKernelFiniteMultiGraph K.shape).endpoints e).IsDiag) :
    D.recoveredPathIndexEquiv K E hG e =
      finCongr
        (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e) := by
  simp [BoundedKernelSubdivisionDatum.recoveredPathIndexEquiv, hloop]

@[simp] theorem BoundedKernelSubdivisionDatum.recoveredPathIndexEquiv_of_nonloop_direct
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.shape.2.1.val)
    (hnonloop :
      ¬((boundedKernelFiniteMultiGraph K.shape).endpoints e).IsDiag)
    (hfirst :
      D.recoveredBranchCoordinatePerm K E hG
          (boundedKernelOrderedEndpoints K.shape e).1 =
        (boundedKernelOrderedEndpoints K.shape
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)).1) :
    D.recoveredPathIndexEquiv K E hG e =
      finCongr
        (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e) := by
  simp [BoundedKernelSubdivisionDatum.recoveredPathIndexEquiv,
    hnonloop, hfirst]

@[simp] theorem BoundedKernelSubdivisionDatum.recoveredPathIndexEquiv_of_nonloop_reversed
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.shape.2.1.val)
    (hnonloop :
      ¬((boundedKernelFiniteMultiGraph K.shape).endpoints e).IsDiag)
    (hfirst :
      D.recoveredBranchCoordinatePerm K E hG
          (boundedKernelOrderedEndpoints K.shape e).1 ≠
        (boundedKernelOrderedEndpoints K.shape
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)).1) :
    D.recoveredPathIndexEquiv K E hG e =
      (Fin.revPerm : Equiv.Perm (Fin (D.profile.length e).val)).trans
        (finCongr
          (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e)) := by
  simp [BoundedKernelSubdivisionDatum.recoveredPathIndexEquiv,
    hnonloop, hfirst]

/-- The complete subdivision-slot equivalence induced by recovered branch,
edge, and oriented path coordinates. -/
noncomputable def BoundedKernelSubdivisionDatum.recoveredSubdivisionSlotEquiv
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    BoundedKernelSubdivisionSlot D.profile ≃
      BoundedKernelSubdivisionSlot E.profile :=
  Equiv.sumCongr (D.recoveredBranchCoordinatePerm K E hG)
    (Equiv.sigmaCongr
      (D.recoveredKernelEdgeCoordinatePerm K E hG)
      (D.recoveredPathIndexEquiv K E hG))

@[simp] theorem BoundedKernelSubdivisionDatum.recoveredSubdivisionSlotEquiv_inl
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (v : Fin K.shape.1.val) :
    D.recoveredSubdivisionSlotEquiv K E hG (.inl v) =
      .inl (D.recoveredBranchCoordinatePerm K E hG v) :=
  rfl

@[simp] theorem BoundedKernelSubdivisionDatum.recoveredSubdivisionSlotEquiv_inr
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.shape.2.1.val)
    (i : Fin (D.profile.length e).val) :
    D.recoveredSubdivisionSlotEquiv K E hG (.inr ⟨e, i⟩) =
      .inr ⟨D.recoveredKernelEdgeCoordinatePerm K E hG e,
        D.recoveredPathIndexEquiv K E hG e i⟩ :=
  rfl

/-- The second datum's labels pulled back to the first datum's recovered
coordinates. -/
noncomputable def BoundedKernelSubdivisionDatum.recoveredCoordinateAlignedLabels
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    BoundedKernelSubdivisionSlot D.profile ≃ Fin k :=
  (D.recoveredSubdivisionSlotEquiv K E hG).trans E.labels

/-- The second subdivision datum expressed in the first datum's recovered
coordinate system. -/
noncomputable def BoundedKernelSubdivisionDatum.recoveredCoordinateAlignedDatum
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    BoundedKernelSubdivisionDatum k K :=
  ⟨D.profile, D.recoveredCoordinateAlignedLabels K E hG⟩

theorem BoundedKernelSubdivisionDatum.recoveredCoordinateAlignedLabels_branch
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (v : Fin K.shape.1.val) :
    D.recoveredCoordinateAlignedLabels K E hG (.inl v) =
      D.labels (.inl v) := by
  change E.branchLabel (D.recoveredBranchCoordinatePerm K E hG v) =
    D.branchLabel v
  exact D.branchLabel_recoveredBranchCoordinatePerm K E hG v

theorem BoundedKernelSubdivisionDatum.recoveredCoordinateAlignedLabels_path
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin K.shape.2.1.val)
    (i : Fin (D.profile.length e).val) :
    D.recoveredCoordinateAlignedLabels K E hG (.inr ⟨e, i⟩) =
      E.pathLabel (D.recoveredKernelEdgeCoordinatePerm K E hG e)
        (D.recoveredPathIndexEquiv K E hG e i) :=
  rfl

@[simp] theorem BoundedKernelSubdivisionDatum.recoveredCoordinateAlignedDatum_profile
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    (D.recoveredCoordinateAlignedDatum K E hG).profile = D.profile :=
  rfl

theorem BoundedKernelSubdivisionDatum.recoveredCoordinateAlignedDatum_branchLabel
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D E : BoundedKernelSubdivisionDatum k K)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (v : Fin K.shape.1.val) :
    (D.recoveredCoordinateAlignedDatum K E hG).branchLabel v =
      D.branchLabel v :=
  D.recoveredCoordinateAlignedLabels_branch K E hG v

end PerronWright.GraphCore
