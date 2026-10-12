import PerronWright.Enumeration.VariableKernelPresentationSymmetry
import PerronWright.Enumeration.FixedSurplusCubicNoncubicSplit

/-!
# Classification of reconstructed noncubic bounded-kernel presentations

This module records the terminal graph-theoretic output of the variable-
kernel reconstruction.  A connected bounded kernel in the strict noncubic
range reconstructs an admissible attachment core, and the intrinsic
suppressed-edge equivalence transfers the strict kernel-edge bound to that
core.  No presentation-fibre cardinality is used here.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- A connected noncubic bounded kernel together with one labelled
admissible subdivision datum. -/
abbrev ConnectedNoncubicBoundedKernelPresentation (k ell : ℕ) :=
  Σ K : LabelledConnectedNoncubicKernel ell,
    BoundedKernelSubdivisionDatum k K.1.toLabelledBoundedKernel

namespace ConnectedNoncubicBoundedKernelPresentation

/-- The reconstructed graph of a connected noncubic bounded-kernel
presentation is an admissible noncubic attachment core. -/
theorem reconstructedGraph_isNoncubicAdmissibleAttachmentCore
    {k ell : ℕ} (hell : 0 < ell)
    (P : ConnectedNoncubicBoundedKernelPresentation k ell) :
    IsNoncubicAdmissibleAttachmentCore k ell
      P.2.reconstructedGraph := by
  let K : LabelledConnectedBoundedKernel ell := P.1.1
  let D : BoundedKernelSubdivisionDatum k K.toLabelledBoundedKernel := P.2
  have hout := D.reconstructedGraph_admissible K.connected
  have htwo : IsTwoCore D.reconstructedGraph Set.univ := by
    intro v _hv
    have hcard : 1 < (D.reconstructedGraph.neighborFinset v).card := by
      rw [D.reconstructedGraph.card_neighborFinset_eq_degree]
      exact lt_of_lt_of_le (by omega) (hout.2.1 v)
    obtain ⟨w, z, hw, hz, hwz⟩ := Finset.one_lt_card_iff.mp hcard
    exact ⟨w, Set.mem_univ w, z, Set.mem_univ z, hwz,
      (D.reconstructedGraph.mem_neighborFinset v w).mp hw,
      (D.reconstructedGraph.mem_neighborFinset v z).mp hz⟩
  have hadmissible :
      IsAdmissibleAttachmentCore k ell D.reconstructedGraph :=
    ⟨hout.1, htwo, hout.2.2⟩
  refine ⟨hadmissible,
    (not_cubic_iff_kernelEdgeLabel_card_lt_three_surplus
      hell hadmissible).2 ?_⟩
  calc
    Nat.card (KernelEdgeLabel D.reconstructedGraph) =
        Nat.card (Fin K.toLabelledBoundedKernel.shape.2.1.val) :=
      Nat.card_congr
        (D.recoveredKernelEdgeEquiv K.toLabelledBoundedKernel)
    _ = K.toLabelledBoundedKernel.shape.2.1.val :=
      Nat.card_fin _
    _ < 3 * ell := P.1.2

end ConnectedNoncubicBoundedKernelPresentation

end PerronWright.GraphCore
