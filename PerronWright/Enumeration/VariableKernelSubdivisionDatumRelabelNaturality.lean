import PerronWright.Enumeration.VariableKernelGlobalPresentationAlignedDatum

/-!
# First-order naturality of variable-kernel subdivision relabelling

This module isolates the literal slot and label identities which precede the
positive-component and recovered-suppressed-edge naturality layer.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- The full subdivision-slot equivalence used by coordinate relabelling
pulls the relabelled label embedding back to the original embedding. -/
@[simp] theorem BoundedKernelSubdivisionDatum.coordinateRelabel_labels_apply
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (gamma : BoundedKernelCoordinatePerm K)
    (z : BoundedKernelSubdivisionSlot D.profile) :
    (D.coordinateRelabel gamma).labels
        (D.profile.coordinateRelabelSlotEquiv gamma z) =
      D.labels z := by
  change D.labels
      ((D.profile.coordinateRelabelSlotEquiv gamma).symm
        (D.profile.coordinateRelabelSlotEquiv gamma z)) = D.labels z
  rw [(D.profile.coordinateRelabelSlotEquiv gamma).symm_apply_apply]

/-- Coordinate relabelling preserves the used original-label embedding as a
whole, after precomposition with the canonical slot equivalence. -/
theorem BoundedKernelSubdivisionDatum.coordinateRelabel_labels_comp
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (gamma : BoundedKernelCoordinatePerm K) :
    (D.coordinateRelabel gamma).labels ∘
        D.profile.coordinateRelabelSlotEquiv gamma = D.labels := by
  funext z
  exact D.coordinateRelabel_labels_apply gamma z

/-- Equality-casting a datum changes neither its profile nor its label
embedding, in the precise heterogeneous sense forced by the dependent kernel
index. -/
theorem boundedKernelSubdivisionDatumCast_profile_labels_heq
    {k ell : ℕ} {K L : LabelledBoundedKernel ell}
    (h : K = L) (D : BoundedKernelSubdivisionDatum k K) :
    HEq (D.profile, D.labels)
      ((boundedKernelSubdivisionDatumCast h D).profile,
        (boundedKernelSubdivisionDatumCast h D).labels) := by
  subst L
  rfl

/-- Equality-casting a subdivision datum and immediately casting back is
heterogeneously the original datum. -/
theorem boundedKernelSubdivisionDatumCast_symm_heq
    {k ell : ℕ} {K L : LabelledBoundedKernel ell}
    (h : K = L) (D : BoundedKernelSubdivisionDatum k K) :
    HEq D
      (boundedKernelSubdivisionDatumCast h.symm
        (boundedKernelSubdivisionDatumCast h D)) := by
  subst L
  rfl

end PerronWright.GraphCore
