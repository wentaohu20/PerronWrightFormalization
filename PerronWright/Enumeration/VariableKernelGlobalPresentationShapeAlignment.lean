import PerronWright.Enumeration.VariableKernelPresentationSymmetry

/-!
# Shape-count alignment for global variable-kernel presentations

Two variable-valence presentations of one labelled reconstructed graph may
start with differently typed finite vertex and edge coordinate sets.  The
intrinsic branching-vertex and suppressed-edge recovery equivalences first
identify those coordinate sets.  This module packages those heterogeneous
equivalences, proves equality of the two numerical shape counts, and records
the resulting `Fin` casts needed by the later endpoint-table and datum-cast
layers.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Equality of labelled simple graphs transports their branching-vertex
subtypes without changing the underlying vertex label. -/
noncomputable def variableBranchingVertexEquivOfGraphEq
    {k : ℕ} {G H : SimpleGraph (Fin k)} (h : G = H) :
    (branchingVertices G : Set (Fin k)) ≃
      (branchingVertices H : Set (Fin k)) := by
  subst H
  exact Equiv.refl _

@[simp] theorem variableBranchingVertexEquivOfGraphEq_apply_val
    {k : ℕ} {G H : SimpleGraph (Fin k)} (h : G = H)
    (v : (branchingVertices G : Set (Fin k))) :
    (variableBranchingVertexEquivOfGraphEq h v).1 = v.1 := by
  subst H
  rfl

/-- Equality of labelled simple graphs transports intrinsic suppressed-edge
labels. -/
noncomputable def variableKernelEdgeLabelEquivOfGraphEq
    {k : ℕ} {G H : SimpleGraph (Fin k)} (h : G = H) :
    KernelEdgeLabel G ≃ KernelEdgeLabel H := by
  subst H
  exact Equiv.refl _

@[simp] theorem variableKernelEdgeLabelEquivOfGraphEq_rfl
    {k : ℕ} {G : SimpleGraph (Fin k)} :
    variableKernelEdgeLabelEquivOfGraphEq (G := G) (H := G) rfl =
      Equiv.refl _ :=
  rfl

/-- Transporting an intrinsic suppressed-edge label across a graph equality
and immediately back is the identity. -/
theorem variableKernelEdgeLabelEquivOfGraphEq_symm_apply_apply
    {k : ℕ} {G H : SimpleGraph (Fin k)} (h : G = H)
    (e : KernelEdgeLabel G) :
    variableKernelEdgeLabelEquivOfGraphEq h.symm
        (variableKernelEdgeLabelEquivOfGraphEq h e) = e := by
  subst H
  rfl

/-- Successive equality transports of intrinsic suppressed-edge labels agree
with transport along the composite equality. -/
theorem variableKernelEdgeLabelEquivOfGraphEq_trans
    {k : ℕ} {G H J : SimpleGraph (Fin k)}
    (hGH : G = H) (hHJ : H = J) (e : KernelEdgeLabel G) :
    variableKernelEdgeLabelEquivOfGraphEq hHJ
        (variableKernelEdgeLabelEquivOfGraphEq hGH e) =
      variableKernelEdgeLabelEquivOfGraphEq (hGH.trans hHJ) e := by
  subst H
  subst J
  rfl

/-- Transport a variable-kernel subdivision datum across literal equality of
its bounded kernel index. -/
def boundedKernelSubdivisionDatumCast
    {k ell : ℕ} {K L : LabelledBoundedKernel ell}
    (h : K = L) (D : BoundedKernelSubdivisionDatum k K) :
    BoundedKernelSubdivisionDatum k L := by
  subst L
  exact D

@[simp] theorem boundedKernelSubdivisionDatumCast_rfl
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    boundedKernelSubdivisionDatumCast rfl D = D :=
  rfl

@[simp] theorem boundedKernelSubdivisionDatumCast_reconstructedGraph
    {k ell : ℕ} {K L : LabelledBoundedKernel ell}
    (h : K = L) (D : BoundedKernelSubdivisionDatum k K) :
    (boundedKernelSubdivisionDatumCast h D).reconstructedGraph =
      D.reconstructedGraph := by
  subst L
  rfl

/-- Transport a loop-coordinate set across literal equality of its bounded
kernel index. -/
def boundedKernelLoopSetCast
    {ell : ℕ} {K L : LabelledBoundedKernel ell}
    (h : K = L) (A : Finset (BoundedKernelLoopEdge K)) :
    Finset (BoundedKernelLoopEdge L) := by
  subst L
  exact A

@[simp] theorem boundedKernelLoopSetCast_rfl
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (A : Finset (BoundedKernelLoopEdge K)) :
    boundedKernelLoopSetCast rfl A = A :=
  rfl

/-- Casting a loop set across a kernel equality and back along its inverse
returns the original set. -/
theorem boundedKernelLoopSetCast_symm_apply
    {ell : ℕ} {K L : LabelledBoundedKernel ell}
    (h : K = L) (A : Finset (BoundedKernelLoopEdge L)) :
    boundedKernelLoopSetCast h
        (boundedKernelLoopSetCast h.symm A) = A := by
  subst L
  rfl

namespace BoundedKernelPresentation

/-- Canonical branch-coordinate equivalence between two variable-kernel
presentations of the same reconstructed labelled graph. -/
noncomputable def globalRecoveredBranchCoordinateEquiv
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    Fin P.1.toLabelledBoundedKernel.shape.1.val ≃
      Fin Q.1.toLabelledBoundedKernel.shape.1.val :=
  (P.2.branchLabelEquivBranching P.1.toLabelledBoundedKernel).trans
    ((variableBranchingVertexEquivOfGraphEq hG).trans
      (Q.2.branchLabelEquivBranching
        Q.1.toLabelledBoundedKernel).symm)

/-- Canonical suppressed-edge-coordinate equivalence between two
variable-kernel presentations of the same reconstructed labelled graph. -/
noncomputable def globalRecoveredKernelEdgeCoordinateEquiv
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    Fin P.1.toLabelledBoundedKernel.shape.2.1.val ≃
      Fin Q.1.toLabelledBoundedKernel.shape.2.1.val :=
  ((P.2.recoveredKernelEdgeEquiv
      P.1.toLabelledBoundedKernel).symm.trans
        (variableKernelEdgeLabelEquivOfGraphEq hG)).trans
    (Q.2.recoveredKernelEdgeEquiv Q.1.toLabelledBoundedKernel)

/-- Corresponding recovered branch coordinates carry the same original
vertex label. -/
theorem branchLabel_globalRecoveredBranchCoordinateEquiv
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (v : Fin P.1.toLabelledBoundedKernel.shape.1.val) :
    Q.2.branchLabel (P.globalRecoveredBranchCoordinateEquiv Q hG v) =
      P.2.branchLabel v := by
  rw [← Q.2.branchLabelEquivBranching_apply
      Q.1.toLabelledBoundedKernel,
    ← P.2.branchLabelEquivBranching_apply
      P.1.toLabelledBoundedKernel]
  simp only [globalRecoveredBranchCoordinateEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply,
    variableBranchingVertexEquivOfGraphEq_apply_val]

/-- Corresponding recovered edge coordinates denote the same intrinsic
suppressed edge after graph-equality transport. -/
theorem globalRecoveredKernelEdgeCoordinateEquiv_intrinsic
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (e : Fin P.1.toLabelledBoundedKernel.shape.2.1.val) :
    variableKernelEdgeLabelEquivOfGraphEq hG
        ((P.2.recoveredKernelEdgeEquiv
          P.1.toLabelledBoundedKernel).symm e) =
      (Q.2.recoveredKernelEdgeEquiv
        Q.1.toLabelledBoundedKernel).symm
          (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG e) := by
  apply (Q.2.recoveredKernelEdgeEquiv
    Q.1.toLabelledBoundedKernel).injective
  simp only [globalRecoveredKernelEdgeCoordinateEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]

/-- The two kernel presentations have the same number of branch
coordinates. -/
theorem vertexCount_eq_of_reconstructedGraph_eq
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    P.1.toLabelledBoundedKernel.shape.1.val =
      Q.1.toLabelledBoundedKernel.shape.1.val := by
  simpa only [Fintype.card_fin] using
    Fintype.card_congr (P.globalRecoveredBranchCoordinateEquiv Q hG)

/-- The two kernel presentations have the same number of suppressed-edge
coordinates. -/
theorem edgeCount_eq_of_reconstructedGraph_eq
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    P.1.toLabelledBoundedKernel.shape.2.1.val =
      Q.1.toLabelledBoundedKernel.shape.2.1.val := by
  simpa only [Fintype.card_fin] using
    Fintype.card_congr
      (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG)

/-- Equality of reconstructed graphs also identifies the bounded vertex-count
coordinates themselves, not only their values. -/
theorem vertexShapeIndex_eq_of_reconstructedGraph_eq
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    P.1.toLabelledBoundedKernel.shape.1 =
      Q.1.toLabelledBoundedKernel.shape.1 := by
  apply Fin.ext
  exact P.vertexCount_eq_of_reconstructedGraph_eq Q hG

/-- Equality of reconstructed graphs also identifies the bounded edge-count
coordinates themselves, not only their values. -/
theorem edgeShapeIndex_eq_of_reconstructedGraph_eq
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    P.1.toLabelledBoundedKernel.shape.2.1 =
      Q.1.toLabelledBoundedKernel.shape.2.1 := by
  apply Fin.ext
  exact P.edgeCount_eq_of_reconstructedGraph_eq Q hG

/-- The literal `Fin` cast from the source branch-coordinate type to the
target branch-coordinate type. -/
noncomputable def branchCoordinateCountCast
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    Fin P.1.toLabelledBoundedKernel.shape.1.val ≃
      Fin Q.1.toLabelledBoundedKernel.shape.1.val :=
  finCongr (P.vertexCount_eq_of_reconstructedGraph_eq Q hG)

/-- The literal `Fin` cast from the source suppressed-edge-coordinate type to
the target suppressed-edge-coordinate type. -/
noncomputable def kernelEdgeCoordinateCountCast
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    Fin P.1.toLabelledBoundedKernel.shape.2.1.val ≃
      Fin Q.1.toLabelledBoundedKernel.shape.2.1.val :=
  finCongr (P.edgeCount_eq_of_reconstructedGraph_eq Q hG)

/-- After casting the target branch-coordinate type back to the source
count, the recovered cross-presentation equivalence is a genuine source
coordinate permutation. -/
noncomputable def globalRecoveredBranchCoordinatePerm
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    Equiv.Perm (Fin P.1.toLabelledBoundedKernel.shape.1.val) :=
  (P.globalRecoveredBranchCoordinateEquiv Q hG).trans
    (P.branchCoordinateCountCast Q hG).symm

/-- After casting the target edge-coordinate type back to the source count,
the recovered cross-presentation equivalence is a genuine source coordinate
permutation. -/
noncomputable def globalRecoveredKernelEdgeCoordinatePerm
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    Equiv.Perm (Fin P.1.toLabelledBoundedKernel.shape.2.1.val) :=
  (P.globalRecoveredKernelEdgeCoordinateEquiv Q hG).trans
    (P.kernelEdgeCoordinateCountCast Q hG).symm

/-- The two recovered source-coordinate permutations packaged in the exact
coordinate-code type used by `applySymmetry`. -/
noncomputable def globalRecoveredCoordinatePerm
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph) :
    BoundedKernelCoordinatePerm P.1.toLabelledBoundedKernel :=
  (P.globalRecoveredBranchCoordinatePerm Q hG,
    P.globalRecoveredKernelEdgeCoordinatePerm Q hG)

@[simp] theorem branchCoordinateCountCast_globalRecoveredBranchCoordinatePerm
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (v : Fin P.1.toLabelledBoundedKernel.shape.1.val) :
    P.branchCoordinateCountCast Q hG
        (P.globalRecoveredBranchCoordinatePerm Q hG v) =
      P.globalRecoveredBranchCoordinateEquiv Q hG v := by
  simp [globalRecoveredBranchCoordinatePerm]

@[simp] theorem kernelEdgeCoordinateCountCast_globalRecoveredKernelEdgeCoordinatePerm
    {k ell : ℕ}
    (P Q : BoundedKernelPresentation k ell)
    (hG : P.2.reconstructedGraph = Q.2.reconstructedGraph)
    (e : Fin P.1.toLabelledBoundedKernel.shape.2.1.val) :
    P.kernelEdgeCoordinateCountCast Q hG
        (P.globalRecoveredKernelEdgeCoordinatePerm Q hG e) =
      P.globalRecoveredKernelEdgeCoordinateEquiv Q hG e := by
  simp [globalRecoveredKernelEdgeCoordinatePerm]

end BoundedKernelPresentation

end PerronWright.GraphCore
