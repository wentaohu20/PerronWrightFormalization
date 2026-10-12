import PerronWright.Enumeration.CubicGlobalPresentationActionLaws
import PerronWright.Enumeration.CubicRecoveredCoordinateGlobalFibre

/-!
# The global reconstruction fibre of cubic presentations

This file begins the decoder for the global coordinate-and-loop action.  Two
presentations which reconstruct the same labelled graph may live over
different edge-labelled cubic kernels.  Their branch and edge coordinates
are nevertheless canonically identified through the intrinsic branching
vertices and suppressed-edge labels of the common reconstructed graph.

The endpoint-table theorem below proves that these two recovered
permutations carry the first kernel exactly to the second.  This is the
cross-kernel step missing from the earlier fixed-kernel fibre theorem.

The final code-to-fibre equivalence is not asserted here.  After the kernel
identification one must still transport the first subdivision datum across
that sigma equality and prove that it differs from the second datum by one
unique loop-reversal set.  The existing unique-loop theorem is formulated
over a definitionally fixed kernel; the precise remaining cast/alignment
lemma is recorded at the end of the file rather than assumed.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

namespace CubicKernelPresentation

/-- Canonical branch-coordinate transport between two possibly different
cubic kernels presenting the same labelled reconstructed graph. -/
noncomputable def globalRecoveredBranchCoordinatePerm
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    Equiv.Perm (Fin (2 * ell)) :=
  (P.2.branchLabelEquivBranching P.1).trans
    ((branchingVertexEquivOfGraphEq hG).trans
      (Q.2.branchLabelEquivBranching Q.1).symm)

/-- Canonical edge-coordinate transport between two possibly different
cubic kernels presenting the same labelled reconstructed graph. -/
noncomputable def globalRecoveredKernelEdgeCoordinatePerm
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    Equiv.Perm (Fin (3 * ell)) :=
  ((P.2.recoveredKernelEdgeEquiv P.1).symm.trans
      (kernelEdgeLabelEquivOfGraphEq hG)).trans
    (Q.2.recoveredKernelEdgeEquiv Q.1)

/-- The recovered branch and edge permutations, packaged as one coordinate
transport. -/
noncomputable def globalRecoveredCoordinatePerm
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    CubicKernelCoordinatePerm ell :=
  (P.globalRecoveredBranchCoordinatePerm Q hG,
    P.globalRecoveredKernelEdgeCoordinatePerm Q hG)

/-- Canonically corresponding branch coordinates carry the same original
vertex label. -/
theorem branchLabel_globalRecoveredBranchCoordinatePerm
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (v : Fin (2 * ell)) :
    Q.2.branchLabel (P.globalRecoveredBranchCoordinatePerm Q hG v) =
      P.2.branchLabel v := by
  rw [← Q.2.branchLabelEquivBranching_apply Q.1,
    ← P.2.branchLabelEquivBranching_apply P.1]
  simp only [globalRecoveredBranchCoordinatePerm, Equiv.trans_apply,
    Equiv.apply_symm_apply, branchingVertexEquivOfGraphEq_apply_val]

/-- Canonically corresponding normalized edge coordinates represent the
same intrinsic suppressed edge of the reconstructed graph. -/
theorem globalRecoveredKernelEdgeCoordinatePerm_intrinsic
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (e : Fin (3 * ell)) :
    kernelEdgeLabelEquivOfGraphEq hG
        ((P.2.recoveredKernelEdgeEquiv P.1).symm e) =
      (Q.2.recoveredKernelEdgeEquiv Q.1).symm
        (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e) := by
  apply (Q.2.recoveredKernelEdgeEquiv Q.1).injective
  simp only [globalRecoveredKernelEdgeCoordinatePerm, Equiv.trans_apply,
    Equiv.apply_symm_apply]

/-- The cross-kernel recovered edge coordinate preserves the full internal
path length. -/
theorem profile_length_globalRecoveredKernelEdgeCoordinatePerm
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (e : Fin (3 * ell)) :
    (P.2.profile.length e).val =
      (Q.2.profile.length
        (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e)).val := by
  calc
    (P.2.profile.length e).val = P.2.recoveredKernelEdgeLength P.1 e :=
      (P.2.recoveredKernelEdgeLength_eq P.1 e).symm
    _ = kernelEdgeInternalLength P.2.reconstructedGraph
        ((P.2.recoveredKernelEdgeEquiv P.1).symm e) := rfl
    _ = kernelEdgeInternalLength Q.2.reconstructedGraph
        (kernelEdgeLabelEquivOfGraphEq hG
          ((P.2.recoveredKernelEdgeEquiv P.1).symm e)) :=
      (kernelEdgeInternalLength_equivOfGraphEq hG _).symm
    _ = kernelEdgeInternalLength Q.2.reconstructedGraph
        ((Q.2.recoveredKernelEdgeEquiv Q.1).symm
          (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e)) := by
      rw [P.globalRecoveredKernelEdgeCoordinatePerm_intrinsic Q hG e]
    _ = Q.2.recoveredKernelEdgeLength Q.1
        (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e) := rfl
    _ = (Q.2.profile.length
        (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e)).val :=
      Q.2.recoveredKernelEdgeLength_eq Q.1 _

/-- The recovered cross-kernel coordinates transport the complete labelled
endpoint table, including loops and parallel edge labels. -/
theorem kernelEndpoints_globalRecoveredCoordinatePerm
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (e : Fin (3 * ell)) :
    Q.1.graph.endpoints
        (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e) =
      Sym2.map (P.globalRecoveredBranchCoordinatePerm Q hG)
        (P.1.graph.endpoints e) := by
  let hminP := P.2.reconstructedGraph_minDegree_two
    P.1.cubic P.1.connected
  let hminQ := Q.2.reconstructedGraph_minDegree_two
    Q.1.cubic Q.1.connected
  let hacycP := P.2.reconstructedTwoGraph_isAcyclic P.1
  let hacycQ := Q.2.reconstructedTwoGraph_isAcyclic Q.1
  let xP : KernelEdgeLabel P.2.reconstructedGraph :=
    (P.2.recoveredKernelEdgeEquiv P.1).symm e
  have hx : kernelEdgeLabelEquivOfGraphEq hG xP =
      (Q.2.recoveredKernelEdgeEquiv Q.1).symm
        (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e) :=
    P.globalRecoveredKernelEdgeCoordinatePerm_intrinsic Q hG e
  have htransport := kernelBranchEndpoints_equivOfGraphEq hG
    hminP hminQ hacycP hacycQ xP
  have hP := congrFun (P.2.recoveredKernelBranchEndpointTable P.1) e
  have hQ := congrFun (Q.2.recoveredKernelBranchEndpointTable Q.1)
    (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e)
  calc
    Q.1.graph.endpoints
        (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e) =
        Sym2.map (Q.2.branchLabelEquivBranching Q.1).symm
          (kernelBranchEndpoints Q.2.reconstructedGraph hminQ hacycQ
            ((Q.2.recoveredKernelEdgeEquiv Q.1).symm
              (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e))) :=
      hQ.symm
    _ = Sym2.map (Q.2.branchLabelEquivBranching Q.1).symm
          (kernelBranchEndpoints Q.2.reconstructedGraph hminQ hacycQ
            (kernelEdgeLabelEquivOfGraphEq hG xP)) := by rw [hx]
    _ = Sym2.map (Q.2.branchLabelEquivBranching Q.1).symm
          (Sym2.map (branchingVertexEquivOfGraphEq hG)
            (kernelBranchEndpoints P.2.reconstructedGraph hminP hacycP xP)) := by
      rw [htransport]
    _ = Sym2.map (P.globalRecoveredBranchCoordinatePerm Q hG)
          (Sym2.map (P.2.branchLabelEquivBranching P.1).symm
            (kernelBranchEndpoints P.2.reconstructedGraph hminP hacycP xP)) := by
      simp only [Sym2.map_map]
      apply Sym2.map_congr
      intro v _hv
      simp only [globalRecoveredBranchCoordinatePerm,
        Function.comp_apply, Equiv.trans_apply]
      rw [(P.2.branchLabelEquivBranching P.1).apply_symm_apply v]
    _ = Sym2.map (P.globalRecoveredBranchCoordinatePerm Q hG)
          (P.1.graph.endpoints e) := by rw [hP]

/-- The recovered coordinate pair carries the first endpoint table exactly
to the second endpoint table. -/
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

theorem graph_eq_coordinateRelabel_globalRecoveredCoordinatePerm
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    Q.1.graph = finiteMultiGraphCoordinateRelabel
      (P.globalRecoveredCoordinatePerm Q hG) P.1.graph := by
  apply finiteMultiGraph_eq_of_endpoints_eq
  funext f
  let e := (P.globalRecoveredKernelEdgeCoordinatePerm Q hG).symm f
  calc
    Q.1.graph.endpoints f =
        Q.1.graph.endpoints
          (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e) := by
      rw [(P.globalRecoveredKernelEdgeCoordinatePerm Q hG).apply_symm_apply]
    _ = Sym2.map (P.globalRecoveredBranchCoordinatePerm Q hG)
          (P.1.graph.endpoints e) :=
      P.kernelEndpoints_globalRecoveredCoordinatePerm Q hG e
    _ = (finiteMultiGraphCoordinateRelabel
          (P.globalRecoveredCoordinatePerm Q hG) P.1.graph).endpoints f := by
      simp only [finiteMultiGraphCoordinateRelabel_endpoints,
        globalRecoveredCoordinatePerm, e]

/-- Consequently the recovered coordinate pair carries the first connected
cubic kernel itself to the second one; proof fields are discarded by
structure extensionality. -/
private theorem labelledConnectedCubicKernel_eq_of_graph_eq
    {ell : ℕ}
    {K K' : LabelledConnectedCubicKernel ell}
    (h : K.graph = K'.graph) : K = K' := by
  cases K with
  | mk graph cubic connected =>
      cases K' with
      | mk graph' cubic' connected' =>
          dsimp only at h
          subst graph'
          rfl

theorem kernel_coordinateRelabel_globalRecoveredCoordinatePerm
    {k ell : ℕ}
    (P Q : CubicKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    P.1.coordinateRelabel (P.globalRecoveredCoordinatePerm Q hG) = Q.1 := by
  apply labelledConnectedCubicKernel_eq_of_graph_eq
  exact (P.graph_eq_coordinateRelabel_globalRecoveredCoordinatePerm Q hG).symm

/-- The actual symmetry-code map into the reconstruction fibre based at
`P`. -/
noncomputable def symmetryFibreMap
    {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G) :
    P.1.SymmetryCode → ReconstructionFibre (ell := ell) G :=
  fun c ↦ applySymmetryInFibre P c

@[simp]
theorem symmetryFibreMap_val
    {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
    (P : ReconstructionFibre (ell := ell) G)
    (c : P.1.SymmetryCode) :
    (symmetryFibreMap P c).1 = P.1.applySymmetry c :=
  rfl

/-- For two elements of one global reconstruction fibre, the canonical
recovered coordinate pair carries the base kernel to the target kernel. -/
theorem reconstructionFibre_kernel_alignment
    {k ell : ℕ}
    {G : SimpleGraph (Fin k)}
    (P Q : ReconstructionFibre (ell := ell) G) :
    P.1.1.coordinateRelabel
        (P.1.globalRecoveredCoordinatePerm Q.1
          (P.2.trans Q.2.symm)) =
      Q.1.1 :=
  P.1.kernel_coordinateRelabel_globalRecoveredCoordinatePerm Q.1
    (P.2.trans Q.2.symm)

/-!
## Exact remaining decoder lemma

The preceding endpoint theorem removes the cross-kernel obstruction.  For
`P Q : ReconstructionFibre G`, put

`γ := P.1.globalRecoveredCoordinatePerm Q.1 (P.2.trans Q.2.symm)`.

We have proved that `(P.1.coordinateRelabel γ).1 = Q.1`.  To finish the
global fibre equivalence, one must now prove, after transporting the datum
across this kernel equality, the single statement

`∃! A, (P.1.coordinateRelabel γ).2.reverseLoops A = Q.1.2`.

Here `A` lives in the loop-edge type of `Q.1.1.graph`; writing the equality
requires the explicit `Sigma.ext`/`HEq` transport induced by
`kernel_coordinateRelabel_globalRecoveredCoordinatePerm`.  The mathematical
content should follow from
`existsUnique_reverseLoops_eq_alignedDatum`: the transported coordinate
datum is precisely the recovered-coordinate alignment of `P` with `Q`.
What is not yet in the library is that cross-kernel alignment/cast identity.

Once that lemma is proved, it directly supplies a unique preimage of `Q`
under `symmetryFibreMap P`; its uniqueness simultaneously proves both
surjectivity and injectivity.  Until then, neither property is declared.
-/

end CubicKernelPresentation

end PerronWright.GraphCore
