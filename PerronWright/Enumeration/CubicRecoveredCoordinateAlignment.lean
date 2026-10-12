import PerronWright.Enumeration.CubicRecoveredCoordinateConverse

/-!
# Canonical alignment of recovered cubic-subdivision coordinates

Two subdivision data which reconstruct the same labelled simple graph need
not use the same normalized kernel coordinates.  In particular, a simple
support graph does not distinguish parallel edges of its suppressed
multigraph.  The intrinsic suppressed-edge type `KernelEdgeLabel`, however,
does distinguish their degree-two components (and its direct edges).

This module uses the common reconstructed graph to define canonical
permutations of the normalized branch and kernel-edge coordinates.  It proves
that branch labels, intrinsic edge labels, lengths, and endpoint tables agree
after these permutations, and packages the resulting equivalence of all
subdivision slots.  On a non-loop edge the internal path coordinate is
transported in the unique direction compatible with the aligned ordered
endpoints; on a loop it is left in the identity direction.  Thus the residual
loop reversals are deliberately left to the Boolean loop-orientation action.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Equality of labelled simple graphs transports their branching-vertex
subtypes without changing the underlying vertex label. -/
noncomputable def branchingVertexEquivOfGraphEq
    {k : ℕ} {G E : SimpleGraph (Fin k)} (h : G = E) :
    (branchingVertices G : Set (Fin k)) ≃
      (branchingVertices E : Set (Fin k)) := by
  subst E
  exact Equiv.refl _

@[simp]
theorem branchingVertexEquivOfGraphEq_apply_val
    {k : ℕ} {G E : SimpleGraph (Fin k)} (h : G = E)
    (v : (branchingVertices G : Set (Fin k))) :
    (branchingVertexEquivOfGraphEq h v).val = v.val := by
  subst E
  rfl

/-- Equality of labelled simple graphs transports the full suppressed-edge
label type.  Since this transports connected components themselves, parallel
suppressed edges remain distinct. -/
noncomputable def kernelEdgeLabelEquivOfGraphEq
    {k : ℕ} {G E : SimpleGraph (Fin k)} (h : G = E) :
    KernelEdgeLabel G ≃ KernelEdgeLabel E := by
  subst E
  exact Equiv.refl _

/-- Intrinsic suppressed-edge length is invariant under equality transport
of the ambient labelled graph. -/
theorem kernelEdgeInternalLength_equivOfGraphEq
    {k : ℕ} {G E : SimpleGraph (Fin k)} (h : G = E)
    (e : KernelEdgeLabel G) :
    kernelEdgeInternalLength E (kernelEdgeLabelEquivOfGraphEq h e) =
      kernelEdgeInternalLength G e := by
  subst E
  rfl

/-- Suppressed branch endpoints commute with equality transport of the
ambient graph.  The minimum-degree and acyclicity proofs are immaterial by
proof irrelevance. -/
theorem kernelBranchEndpoints_equivOfGraphEq
    {k : ℕ} {G E : SimpleGraph (Fin k)} (h : G = E)
    (hminG : ∀ v, 2 ≤ G.degree v)
    (hminE : ∀ v, 2 ≤ E.degree v)
    (hacycG : (twoGraph G).IsAcyclic)
    (hacycE : (twoGraph E).IsAcyclic)
    (e : KernelEdgeLabel G) :
    Sym2.map (branchingVertexEquivOfGraphEq h)
        (kernelBranchEndpoints G hminG hacycG e) =
      kernelBranchEndpoints E hminE hacycE
        (kernelEdgeLabelEquivOfGraphEq h e) := by
  subst E
  have hminE_eq : hminE = hminG := Subsingleton.elim _ _
  have hacycE_eq : hacycE = hacycG := Subsingleton.elim _ _
  subst hminE
  subst hacycE
  change Sym2.map (fun x ↦ x)
      (kernelBranchEndpoints G hminG hacycG e) =
    kernelBranchEndpoints G hminG hacycG e
  exact congrFun Sym2.map_id _

/-- The canonical branch-coordinate permutation from `D`-coordinates to
`E`-coordinates, obtained by identifying both with the branching vertices of
their common reconstructed graph. -/
noncomputable def CubicKernelSubdivisionDatum.recoveredBranchCoordinatePerm
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    Equiv.Perm (Fin (2 * ell)) :=
  (D.branchLabelEquivBranching K).trans
    ((branchingVertexEquivOfGraphEq hG).trans
      (E.branchLabelEquivBranching K).symm)

/-- The canonical edge-coordinate permutation from `D`-coordinates to
`E`-coordinates.  It passes through the intrinsic suppressed-edge label type,
so it correctly distinguishes parallel kernel edges. -/
noncomputable def CubicKernelSubdivisionDatum.recoveredKernelEdgeCoordinatePerm
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    Equiv.Perm (Fin (3 * ell)) :=
  ((D.recoveredKernelEdgeEquiv K).symm.trans
      (kernelEdgeLabelEquivOfGraphEq hG)).trans
    (E.recoveredKernelEdgeEquiv K)

/-- Branch coordinates selected by the canonical permutation carry exactly
the same original vertex labels. -/
theorem CubicKernelSubdivisionDatum.branchLabel_recoveredBranchCoordinatePerm
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (v : Fin (2 * ell)) :
    E.branchLabel (D.recoveredBranchCoordinatePerm K E hG v) =
      D.branchLabel v := by
  rw [← E.branchLabelEquivBranching_apply K,
    ← D.branchLabelEquivBranching_apply K]
  simp only [CubicKernelSubdivisionDatum.recoveredBranchCoordinatePerm,
    Equiv.trans_apply, Equiv.apply_symm_apply,
    branchingVertexEquivOfGraphEq_apply_val]

/-- The intrinsic edge represented by a normalized `D`-edge is transported
to the intrinsic edge represented by its canonically aligned `E`-edge. -/
theorem CubicKernelSubdivisionDatum.recoveredKernelEdgeCoordinatePerm_intrinsic
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) :
    kernelEdgeLabelEquivOfGraphEq hG
        ((D.recoveredKernelEdgeEquiv K).symm e) =
      (E.recoveredKernelEdgeEquiv K).symm
        (D.recoveredKernelEdgeCoordinatePerm K E hG e) := by
  apply (E.recoveredKernelEdgeEquiv K).injective
  simp only [CubicKernelSubdivisionDatum.recoveredKernelEdgeCoordinatePerm,
    Equiv.trans_apply, Equiv.apply_symm_apply]

/-- The canonical edge-coordinate permutation preserves every subdivision
length. -/
theorem CubicKernelSubdivisionDatum.profile_length_recoveredKernelEdgeCoordinatePerm
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) :
    (D.profile.length e).val =
      (E.profile.length
        (D.recoveredKernelEdgeCoordinatePerm K E hG e)).val := by
  calc
    (D.profile.length e).val = D.recoveredKernelEdgeLength K e :=
      (D.recoveredKernelEdgeLength_eq K e).symm
    _ = kernelEdgeInternalLength D.reconstructedGraph
        ((D.recoveredKernelEdgeEquiv K).symm e) := rfl
    _ = kernelEdgeInternalLength E.reconstructedGraph
        (kernelEdgeLabelEquivOfGraphEq hG
          ((D.recoveredKernelEdgeEquiv K).symm e)) :=
      (kernelEdgeInternalLength_equivOfGraphEq hG _).symm
    _ = kernelEdgeInternalLength E.reconstructedGraph
        ((E.recoveredKernelEdgeEquiv K).symm
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)) := by
      rw [D.recoveredKernelEdgeCoordinatePerm_intrinsic K E hG e]
    _ = E.recoveredKernelEdgeLength K
        (D.recoveredKernelEdgeCoordinatePerm K E hG e) := rfl
    _ = (E.profile.length
        (D.recoveredKernelEdgeCoordinatePerm K E hG e)).val :=
      E.recoveredKernelEdgeLength_eq K _

/-- The canonical branch and edge permutations form an automorphism of the
labelled cubic endpoint table.  This is the endpoint-level statement which
retains all parallel-edge labels rather than collapsing to simple support. -/
theorem CubicKernelSubdivisionDatum.kernelEndpoints_recoveredCoordinatePerm
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) :
    K.graph.endpoints
        (D.recoveredKernelEdgeCoordinatePerm K E hG e) =
      Sym2.map (D.recoveredBranchCoordinatePerm K E hG)
        (K.graph.endpoints e) := by
  let hminD := D.reconstructedGraph_minDegree_two K.cubic K.connected
  let hminE := E.reconstructedGraph_minDegree_two K.cubic K.connected
  let hacycD := D.reconstructedTwoGraph_isAcyclic K
  let hacycE := E.reconstructedTwoGraph_isAcyclic K
  let xD : KernelEdgeLabel D.reconstructedGraph :=
    (D.recoveredKernelEdgeEquiv K).symm e
  have hx : kernelEdgeLabelEquivOfGraphEq hG xD =
      (E.recoveredKernelEdgeEquiv K).symm
        (D.recoveredKernelEdgeCoordinatePerm K E hG e) :=
    D.recoveredKernelEdgeCoordinatePerm_intrinsic K E hG e
  have htransport := kernelBranchEndpoints_equivOfGraphEq hG
    hminD hminE hacycD hacycE xD
  have hD := congrFun (D.recoveredKernelBranchEndpointTable K) e
  have hE := congrFun (E.recoveredKernelBranchEndpointTable K)
    (D.recoveredKernelEdgeCoordinatePerm K E hG e)
  calc
    K.graph.endpoints
        (D.recoveredKernelEdgeCoordinatePerm K E hG e) =
        Sym2.map (E.branchLabelEquivBranching K).symm
          (kernelBranchEndpoints E.reconstructedGraph hminE hacycE
            ((E.recoveredKernelEdgeEquiv K).symm
              (D.recoveredKernelEdgeCoordinatePerm K E hG e))) := hE.symm
    _ = Sym2.map (E.branchLabelEquivBranching K).symm
          (kernelBranchEndpoints E.reconstructedGraph hminE hacycE
            (kernelEdgeLabelEquivOfGraphEq hG xD)) := by rw [hx]
    _ = Sym2.map (E.branchLabelEquivBranching K).symm
          (Sym2.map (branchingVertexEquivOfGraphEq hG)
            (kernelBranchEndpoints D.reconstructedGraph hminD hacycD xD)) := by
      rw [htransport]
    _ = Sym2.map (D.recoveredBranchCoordinatePerm K E hG)
          (Sym2.map (D.branchLabelEquivBranching K).symm
            (kernelBranchEndpoints D.reconstructedGraph hminD hacycD xD)) := by
      simp only [Sym2.map_map]
      apply Sym2.map_congr
      intro v _hv
      simp only [CubicKernelSubdivisionDatum.recoveredBranchCoordinatePerm,
        Function.comp_apply, Equiv.trans_apply]
      rw [(D.branchLabelEquivBranching K).apply_symm_apply v]
    _ = Sym2.map (D.recoveredBranchCoordinatePerm K E hG)
          (K.graph.endpoints e) := by rw [hD]

/-- After the recovered branch and edge coordinates have been aligned, the
two ordered endpoint pairs agree either directly or in the opposite order.
This is obtained from equality of the corresponding unordered endpoint pairs;
in particular, it does not collapse parallel edges. -/
theorem CubicKernelSubdivisionDatum.orderedEndpoints_recoveredCoordinatePerm
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) :
    let σV := D.recoveredBranchCoordinatePerm K E hG
    let σE := D.recoveredKernelEdgeCoordinatePerm K E hG
    let oD := cubicKernelOrderedEndpoints K.graph e
    let oE := cubicKernelOrderedEndpoints K.graph (σE e)
    (σV oD.1 = oE.1 ∧ σV oD.2 = oE.2) ∨
      (σV oD.1 = oE.2 ∧ σV oD.2 = oE.1) := by
  dsimp only
  apply Sym2.eq_iff.mp
  calc
    s((D.recoveredBranchCoordinatePerm K E hG)
          (cubicKernelOrderedEndpoints K.graph e).1,
        (D.recoveredBranchCoordinatePerm K E hG)
          (cubicKernelOrderedEndpoints K.graph e).2) =
        Sym2.map (D.recoveredBranchCoordinatePerm K E hG)
          (K.graph.endpoints e) := by
      rw [← cubicKernelOrderedEndpoints_mk K.graph e, Sym2.map_mk]
    _ = K.graph.endpoints
          (D.recoveredKernelEdgeCoordinatePerm K E hG e) :=
      (D.kernelEndpoints_recoveredCoordinatePerm K E hG e).symm
    _ = s((cubicKernelOrderedEndpoints K.graph
            (D.recoveredKernelEdgeCoordinatePerm K E hG e)).1,
          (cubicKernelOrderedEndpoints K.graph
            (D.recoveredKernelEdgeCoordinatePerm K E hG e)).2) :=
      (cubicKernelOrderedEndpoints_mk K.graph _).symm

/-- On a non-loop edge the unordered endpoint identity gives the precise
direct-or-reversed ordered-endpoint dichotomy used to orient its internal
path coordinate. -/
theorem CubicKernelSubdivisionDatum.nonloop_orderedEndpoints_dichotomy
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell))
    (_hnonloop : ¬(K.graph.endpoints e).IsDiag) :
    let σV := D.recoveredBranchCoordinatePerm K E hG
    let σE := D.recoveredKernelEdgeCoordinatePerm K E hG
    let oD := cubicKernelOrderedEndpoints K.graph e
    let oE := cubicKernelOrderedEndpoints K.graph (σE e)
    (σV oD.1 = oE.1 ∧ σV oD.2 = oE.2) ∨
      (σV oD.1 = oE.2 ∧ σV oD.2 = oE.1) :=
  D.orderedEndpoints_recoveredCoordinatePerm K E hG e

/-- For a non-loop, the direct and reversed alternatives in the preceding
dichotomy cannot both hold.  This is where non-diagonality is used: both
orders at once would identify the two source endpoints through the injective
branch-coordinate permutation. -/
theorem CubicKernelSubdivisionDatum.nonloop_orderedEndpoints_exclusive
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell))
    (hnonloop : ¬(K.graph.endpoints e).IsDiag) :
    let σV := D.recoveredBranchCoordinatePerm K E hG
    let σE := D.recoveredKernelEdgeCoordinatePerm K E hG
    let oD := cubicKernelOrderedEndpoints K.graph e
    let oE := cubicKernelOrderedEndpoints K.graph (σE e)
    ¬ ((σV oD.1 = oE.1 ∧ σV oD.2 = oE.2) ∧
      (σV oD.1 = oE.2 ∧ σV oD.2 = oE.1)) := by
  dsimp only
  intro hboth
  have hsame :
      D.recoveredBranchCoordinatePerm K E hG
          (cubicKernelOrderedEndpoints K.graph e).1 =
        D.recoveredBranchCoordinatePerm K E hG
          (cubicKernelOrderedEndpoints K.graph e).2 :=
    hboth.1.1.trans hboth.2.2.symm
  have hordered :
      (cubicKernelOrderedEndpoints K.graph e).1 =
        (cubicKernelOrderedEndpoints K.graph e).2 :=
    (D.recoveredBranchCoordinatePerm K E hG).injective hsame
  exact hnonloop
    ((cubicKernelOrderedEndpoints_eq_iff_isDiag K.graph e).1 hordered)

/-- The canonical recovered edge permutation preserves the loop predicate. -/
theorem CubicKernelSubdivisionDatum.kernelEndpoint_isDiag_recoveredCoordinatePerm
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) :
    (K.graph.endpoints
        (D.recoveredKernelEdgeCoordinatePerm K E hG e)).IsDiag ↔
      (K.graph.endpoints e).IsDiag := by
  rw [D.kernelEndpoints_recoveredCoordinatePerm K E hG e]
  exact Sym2.isDiag_map
    (D.recoveredBranchCoordinatePerm K E hG).injective

/-- If the first aligned endpoint is not the first endpoint in the target
coordinate, the endpoint alignment is necessarily the reversed one. -/
theorem CubicKernelSubdivisionDatum.orderedEndpoints_reversed_of_first_ne
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell))
    (hfirst :
      D.recoveredBranchCoordinatePerm K E hG
          (cubicKernelOrderedEndpoints K.graph e).1 ≠
        (cubicKernelOrderedEndpoints K.graph
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)).1) :
    D.recoveredBranchCoordinatePerm K E hG
        (cubicKernelOrderedEndpoints K.graph e).1 =
      (cubicKernelOrderedEndpoints K.graph
        (D.recoveredKernelEdgeCoordinatePerm K E hG e)).2 ∧
    D.recoveredBranchCoordinatePerm K E hG
        (cubicKernelOrderedEndpoints K.graph e).2 =
      (cubicKernelOrderedEndpoints K.graph
        (D.recoveredKernelEdgeCoordinatePerm K E hG e)).1 := by
  rcases D.orderedEndpoints_recoveredCoordinatePerm K E hG e with
    hdirect | hreversed
  · exact False.elim (hfirst hdirect.1)
  · exact hreversed

/-- The internal coordinate equivalence on one aligned kernel edge.  Loops
are transported without reversal.  A non-loop is transported directly when
the aligned first endpoints agree, and by `Fin.revPerm` otherwise. -/
noncomputable def CubicKernelSubdivisionDatum.recoveredPathIndexEquiv
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) :
    Fin (D.profile.length e).val ≃
      Fin (E.profile.length
        (D.recoveredKernelEdgeCoordinatePerm K E hG e)).val :=
  if _hloop : (K.graph.endpoints e).IsDiag then
    finCongr (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e)
  else if _hfirst :
      D.recoveredBranchCoordinatePerm K E hG
          (cubicKernelOrderedEndpoints K.graph e).1 =
        (cubicKernelOrderedEndpoints K.graph
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)).1 then
    finCongr (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e)
  else
    (Fin.revPerm : Equiv.Perm (Fin (D.profile.length e).val)).trans
      (finCongr
        (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e))

@[simp]
theorem CubicKernelSubdivisionDatum.recoveredPathIndexEquiv_of_loop
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) (hloop : (K.graph.endpoints e).IsDiag) :
    D.recoveredPathIndexEquiv K E hG e =
      finCongr
        (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e) := by
  simp [CubicKernelSubdivisionDatum.recoveredPathIndexEquiv, hloop]

@[simp]
theorem CubicKernelSubdivisionDatum.recoveredPathIndexEquiv_of_nonloop_direct
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) (hnonloop : ¬(K.graph.endpoints e).IsDiag)
    (hfirst :
      D.recoveredBranchCoordinatePerm K E hG
          (cubicKernelOrderedEndpoints K.graph e).1 =
        (cubicKernelOrderedEndpoints K.graph
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)).1) :
    D.recoveredPathIndexEquiv K E hG e =
      finCongr
        (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e) := by
  simp [CubicKernelSubdivisionDatum.recoveredPathIndexEquiv,
    hnonloop, hfirst]

@[simp]
theorem CubicKernelSubdivisionDatum.recoveredPathIndexEquiv_of_nonloop_reversed
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) (hnonloop : ¬(K.graph.endpoints e).IsDiag)
    (hfirst :
      D.recoveredBranchCoordinatePerm K E hG
          (cubicKernelOrderedEndpoints K.graph e).1 ≠
        (cubicKernelOrderedEndpoints K.graph
          (D.recoveredKernelEdgeCoordinatePerm K E hG e)).1) :
    D.recoveredPathIndexEquiv K E hG e =
      (Fin.revPerm : Equiv.Perm (Fin (D.profile.length e).val)).trans
        (finCongr
          (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hG e)) := by
  simp [CubicKernelSubdivisionDatum.recoveredPathIndexEquiv,
    hnonloop, hfirst]

/-- The complete subdivision-slot equivalence induced by the canonical
branch and kernel-edge coordinate alignment, with non-loop path coordinates
oriented by their aligned endpoints and loop coordinates left unreversed. -/
noncomputable def CubicKernelSubdivisionDatum.recoveredSubdivisionSlotEquiv
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    CubicKernelSubdivisionSlot D.profile ≃
      CubicKernelSubdivisionSlot E.profile :=
  Equiv.sumCongr (D.recoveredBranchCoordinatePerm K E hG)
    (Equiv.sigmaCongr
      (D.recoveredKernelEdgeCoordinatePerm K E hG)
      (D.recoveredPathIndexEquiv K E hG))

@[simp]
theorem CubicKernelSubdivisionDatum.recoveredSubdivisionSlotEquiv_inl
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (v : Fin (2 * ell)) :
    D.recoveredSubdivisionSlotEquiv K E hG (.inl v) =
      .inl (D.recoveredBranchCoordinatePerm K E hG v) := by
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.recoveredSubdivisionSlotEquiv_inr
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) (i : Fin (D.profile.length e).val) :
    D.recoveredSubdivisionSlotEquiv K E hG (.inr ⟨e, i⟩) =
      .inr ⟨D.recoveredKernelEdgeCoordinatePerm K E hG e,
        D.recoveredPathIndexEquiv K E hG e i⟩ := by
  rfl

/-- The second datum's original labels, pulled back to the first datum's
canonically recovered coordinates. -/
noncomputable def CubicKernelSubdivisionDatum.recoveredCoordinateAlignedLabels
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    CubicKernelSubdivisionSlot D.profile ≃ Fin k :=
  (D.recoveredSubdivisionSlotEquiv K E hG).trans E.labels

/-- The second subdivision datum expressed in the canonically recovered
branch and kernel-edge coordinates of the first datum.  Its profile is the
first profile; the slot equivalence above performs the required length casts. -/
noncomputable def CubicKernelSubdivisionDatum.recoveredCoordinateAlignedDatum
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    CubicKernelSubdivisionDatum k ell K.graph :=
  ⟨D.profile, D.recoveredCoordinateAlignedLabels K E hG⟩

/-- After pulling back the second datum to the recovered coordinates of the
first, all branch labels agree literally. -/
theorem CubicKernelSubdivisionDatum.recoveredCoordinateAlignedLabels_branch
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (v : Fin (2 * ell)) :
    D.recoveredCoordinateAlignedLabels K E hG (.inl v) =
      D.labels (.inl v) := by
  change E.branchLabel (D.recoveredBranchCoordinatePerm K E hG v) =
    D.branchLabel v
  exact D.branchLabel_recoveredBranchCoordinatePerm K E hG v

/-- The aligned internal label at a source path coordinate is the second
datum's label at the canonically aligned edge and oriented path coordinate. -/
theorem CubicKernelSubdivisionDatum.recoveredCoordinateAlignedLabels_path
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (e : Fin (3 * ell)) (i : Fin (D.profile.length e).val) :
    D.recoveredCoordinateAlignedLabels K E hG (.inr ⟨e, i⟩) =
      E.pathLabel (D.recoveredKernelEdgeCoordinatePerm K E hG e)
        (D.recoveredPathIndexEquiv K E hG e i) := by
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.recoveredCoordinateAlignedDatum_profile
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph) :
    (D.recoveredCoordinateAlignedDatum K E hG).profile = D.profile :=
  rfl

/-- The aligned datum has the first datum's branch coordinates literally,
which is the `hbranch` input of the recovered-coordinate converse. -/
theorem CubicKernelSubdivisionDatum.recoveredCoordinateAlignedDatum_branchLabel
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E : CubicKernelSubdivisionDatum k ell K.graph)
    (hG : D.reconstructedGraph = E.reconstructedGraph)
    (v : Fin (2 * ell)) :
    (D.recoveredCoordinateAlignedDatum K E hG).branchLabel v =
      D.branchLabel v :=
  D.recoveredCoordinateAlignedLabels_branch K E hG v

end PerronWright.GraphCore
