import PerronWright.Enumeration.VariableSubdivisionComponentRecovery
import Mathlib.Data.Fin.Rev

/-!
# Loop-orientation action on bounded-kernel subdivision labels

Reversing the ordered internal labels of a loop edge is a canonical
involution on subdivision data.  This is the explicit Boolean symmetry that
must eventually be divided out in the exact bounded-kernel classification.
-/

open scoped Classical

noncomputable section

namespace PerronWright.GraphCore

def boundedKernelLoopEdgeSlotReverseEquiv
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (e : BoundedKernelLoopEdge K) :
    BoundedKernelSubdivisionSlot L ≃ BoundedKernelSubdivisionSlot L :=
  Equiv.sumCongr (Equiv.refl _) <|
    Equiv.sigmaCongrRight fun f =>
      if h : f = e.1 then
        h ▸ Fin.revPerm
      else Equiv.refl _

@[simp]
theorem boundedKernelLoopEdgeSlotReverseEquiv_inl
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (e : BoundedKernelLoopEdge K) (v : Fin K.shape.1.val) :
    boundedKernelLoopEdgeSlotReverseEquiv L e (.inl v) = .inl v := by
  rfl

@[simp]
theorem boundedKernelLoopEdgeSlotReverseEquiv_same
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (e : BoundedKernelLoopEdge K) (i : Fin (L.length e.1).val) :
    boundedKernelLoopEdgeSlotReverseEquiv L e (.inr ⟨e.1, i⟩) =
      .inr ⟨e.1, Fin.rev i⟩ := by
  change Sum.map (id : Fin K.shape.1.val → Fin K.shape.1.val) _
    (Sum.inr (α := Fin K.shape.1.val)
      (⟨e.1, i⟩ : Σ f : Fin K.shape.2.1.val, Fin (L.length f).val)) = _
  rw [Sum.map_inr]
  congr 1
  rw [Equiv.sigmaCongrRight_apply]
  simp

@[simp]
theorem boundedKernelLoopEdgeSlotReverseEquiv_other
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (e : BoundedKernelLoopEdge K) (f : Fin K.shape.2.1.val)
    (hfe : f ≠ e.1) (i : Fin (L.length f).val) :
    boundedKernelLoopEdgeSlotReverseEquiv L e (.inr ⟨f, i⟩) = .inr ⟨f, i⟩ := by
  change Sum.map (id : Fin K.shape.1.val → Fin K.shape.1.val) _
    (Sum.inr (α := Fin K.shape.1.val)
      (⟨f, i⟩ : Σ j : Fin K.shape.2.1.val, Fin (L.length j).val)) = _
  rw [Sum.map_inr]
  congr 1
  rw [Equiv.sigmaCongrRight_apply]
  simp [hfe]

@[simp]
theorem boundedKernelLoopEdgeSlotReverseEquiv_apply_apply
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (e : BoundedKernelLoopEdge K) (z : BoundedKernelSubdivisionSlot L) :
    boundedKernelLoopEdgeSlotReverseEquiv L e (boundedKernelLoopEdgeSlotReverseEquiv L e z) = z := by
  cases z with
  | inl v => simp; rfl
  | inr p =>
      rcases p with ⟨f, i⟩
      by_cases hfe : f = e.1
      · subst f
        simp
        rfl
      · simp [boundedKernelLoopEdgeSlotReverseEquiv_other, hfe]
        rfl

/-- Reverse the ordered internal labels on one loop edge. -/
def BoundedKernelSubdivisionDatum.reverseLoop
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : BoundedKernelLoopEdge K) : BoundedKernelSubdivisionDatum k K where
  profile := D.profile
  labels := (boundedKernelLoopEdgeSlotReverseEquiv D.profile e).trans D.labels

@[simp]
theorem BoundedKernelSubdivisionDatum.reverseLoop_profile
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : BoundedKernelLoopEdge K) :
    (D.reverseLoop e).profile = D.profile := rfl

@[simp]
theorem BoundedKernelSubdivisionDatum.reverseLoop_branchLabel
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : BoundedKernelLoopEdge K) (v : Fin K.shape.1.val) :
    (D.reverseLoop e).branchLabel v = D.branchLabel v := by
  rfl

@[simp]
theorem BoundedKernelSubdivisionDatum.reverseLoop_pathLabel_same
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : BoundedKernelLoopEdge K) (i : Fin (D.profile.length e.1).val) :
    (D.reverseLoop e).pathLabel e.1 i = D.pathLabel e.1 (Fin.rev i) := by
  change D.labels (boundedKernelLoopEdgeSlotReverseEquiv D.profile e (.inr ⟨e.1, i⟩)) = _
  rw [boundedKernelLoopEdgeSlotReverseEquiv_same]
  rfl

@[simp]
theorem BoundedKernelSubdivisionDatum.reverseLoop_pathLabel_other
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : BoundedKernelLoopEdge K) (f : Fin K.shape.2.1.val)
    (hfe : f ≠ e.1) (i : Fin (D.profile.length f).val) :
    (D.reverseLoop e).pathLabel f i = D.pathLabel f i := by
  change D.labels (boundedKernelLoopEdgeSlotReverseEquiv D.profile e (.inr ⟨f, i⟩)) = _
  rw [boundedKernelLoopEdgeSlotReverseEquiv_other _ _ _ hfe]
  rfl

@[simp]
theorem BoundedKernelSubdivisionDatum.reverseLoop_labels_twice
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : BoundedKernelLoopEdge K) (z : BoundedKernelSubdivisionSlot D.profile) :
    ((D.reverseLoop e).reverseLoop e).labels z = D.labels z := by
  change D.labels
      (boundedKernelLoopEdgeSlotReverseEquiv D.profile e
        (boundedKernelLoopEdgeSlotReverseEquiv D.profile e z)) = D.labels z
  rw [boundedKernelLoopEdgeSlotReverseEquiv_apply_apply]

end PerronWright.GraphCore
