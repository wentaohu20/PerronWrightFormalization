import PerronWright.Enumeration.CubicSubdivisionComponentRecovery
import Mathlib.Data.Fin.Rev

/-!
# Loop-orientation action on cubic-kernel subdivision labels

Reversing the ordered internal labels of a loop edge is a canonical
involution on subdivision data.  This is the explicit Boolean symmetry that
must eventually be divided out in the exact cubic-core classification.
-/

open scoped Classical

noncomputable section

namespace PerronWright.GraphCore

def loopEdgeSlotReverseEquiv
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (e : CubicKernelLoopEdge H) :
    CubicKernelSubdivisionSlot L ≃ CubicKernelSubdivisionSlot L :=
  Equiv.sumCongr (Equiv.refl _) <|
    Equiv.sigmaCongrRight fun f =>
      if h : f = e.1 then
        h ▸ Fin.revPerm
      else Equiv.refl _

@[simp]
theorem loopEdgeSlotReverseEquiv_inl
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (e : CubicKernelLoopEdge H) (v : Fin (2 * ell)) :
    loopEdgeSlotReverseEquiv L e (.inl v) = .inl v := by
  rfl

@[simp]
theorem loopEdgeSlotReverseEquiv_same
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (e : CubicKernelLoopEdge H) (i : Fin (L.length e.1).val) :
    loopEdgeSlotReverseEquiv L e (.inr ⟨e.1, i⟩) =
      .inr ⟨e.1, Fin.rev i⟩ := by
  change Sum.map (id : Fin (2 * ell) → Fin (2 * ell)) _
    (Sum.inr (α := Fin (2 * ell))
      (⟨e.1, i⟩ : Σ f : Fin (3 * ell), Fin (L.length f).val)) = _
  rw [Sum.map_inr]
  congr 1
  rw [Equiv.sigmaCongrRight_apply]
  simp

@[simp]
theorem loopEdgeSlotReverseEquiv_other
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (e : CubicKernelLoopEdge H) (f : Fin (3 * ell))
    (hfe : f ≠ e.1) (i : Fin (L.length f).val) :
    loopEdgeSlotReverseEquiv L e (.inr ⟨f, i⟩) = .inr ⟨f, i⟩ := by
  change Sum.map (id : Fin (2 * ell) → Fin (2 * ell)) _
    (Sum.inr (α := Fin (2 * ell))
      (⟨f, i⟩ : Σ j : Fin (3 * ell), Fin (L.length j).val)) = _
  rw [Sum.map_inr]
  congr 1
  rw [Equiv.sigmaCongrRight_apply]
  simp [hfe]

@[simp]
theorem loopEdgeSlotReverseEquiv_apply_apply
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (e : CubicKernelLoopEdge H) (z : CubicKernelSubdivisionSlot L) :
    loopEdgeSlotReverseEquiv L e (loopEdgeSlotReverseEquiv L e z) = z := by
  cases z with
  | inl v => simp; rfl
  | inr p =>
      rcases p with ⟨f, i⟩
      by_cases hfe : f = e.1
      · subst f
        simp
        rfl
      · simp [loopEdgeSlotReverseEquiv_other, hfe]
        rfl

/-- Reverse the ordered internal labels on one loop edge. -/
def CubicKernelSubdivisionDatum.reverseLoop
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) : CubicKernelSubdivisionDatum k ell H where
  profile := D.profile
  labels := (loopEdgeSlotReverseEquiv D.profile e).trans D.labels

@[simp]
theorem CubicKernelSubdivisionDatum.reverseLoop_profile
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) :
    (D.reverseLoop e).profile = D.profile := rfl

@[simp]
theorem CubicKernelSubdivisionDatum.reverseLoop_branchLabel
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) (v : Fin (2 * ell)) :
    (D.reverseLoop e).branchLabel v = D.branchLabel v := by
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.reverseLoop_pathLabel_same
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) (i : Fin (D.profile.length e.1).val) :
    (D.reverseLoop e).pathLabel e.1 i = D.pathLabel e.1 (Fin.rev i) := by
  change D.labels (loopEdgeSlotReverseEquiv D.profile e (.inr ⟨e.1, i⟩)) = _
  rw [loopEdgeSlotReverseEquiv_same]
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.reverseLoop_pathLabel_other
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) (f : Fin (3 * ell))
    (hfe : f ≠ e.1) (i : Fin (D.profile.length f).val) :
    (D.reverseLoop e).pathLabel f i = D.pathLabel f i := by
  change D.labels (loopEdgeSlotReverseEquiv D.profile e (.inr ⟨f, i⟩)) = _
  rw [loopEdgeSlotReverseEquiv_other _ _ _ hfe]
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.reverseLoop_labels_twice
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) (z : CubicKernelSubdivisionSlot D.profile) :
    ((D.reverseLoop e).reverseLoop e).labels z = D.labels z := by
  change D.labels
      (loopEdgeSlotReverseEquiv D.profile e
        (loopEdgeSlotReverseEquiv D.profile e z)) = D.labels z
  rw [loopEdgeSlotReverseEquiv_apply_apply]

end PerronWright.GraphCore
