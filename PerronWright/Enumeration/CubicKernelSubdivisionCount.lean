import PerronWright.Enumeration.CubicKernelSubdivision
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm

/-!
# Cardinalities of cubic-kernel subdivision labels

This is the first exact counting layer for `CubicKernelSubdivision`.  It is
independent of graph reconstruction and of loop-orientation normalization.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- The branch slots together with all ordered internal path slots have
exactly the prescribed number `k` of original vertex labels. -/
theorem cubicKernelSubdivisionSlot_card
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H) :
    Fintype.card (CubicKernelSubdivisionSlot L) = k := by
  change
    Fintype.card
      (Fin (2 * ell) ⊕
        Σ e : Fin (3 * ell), Fin (L.length e).val) = k
  calc
    Fintype.card
        (Fin (2 * ell) ⊕
          Σ e : Fin (3 * ell), Fin (L.length e).val) =
      Fintype.card (Fin (2 * ell)) +
        Fintype.card (Σ e : Fin (3 * ell), Fin (L.length e).val) :=
          Fintype.card_sum
    _ = 2 * ell + ∑ e : Fin (3 * ell), (L.length e).val := by
      simp only [Fintype.card_fin, Fintype.card_sigma]
    _ = k := L.totalLength

/-- For one fixed admissible length profile, exact labellings of all
subdivision slots by `Fin k` are counted by `k!`. -/
theorem cubicKernelSubdivisionLabelEquiv_card
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H) :
    Fintype.card (CubicKernelSubdivisionSlot L ≃ Fin k) = k.factorial := by
  let e : CubicKernelSubdivisionSlot L ≃ Fin k :=
    Fintype.equivFinOfCardEq (cubicKernelSubdivisionSlot_card L)
  calc
    Fintype.card (CubicKernelSubdivisionSlot L ≃ Fin k) =
        (Fintype.card (CubicKernelSubdivisionSlot L)).factorial :=
      Fintype.card_equiv e
    _ = k.factorial := by
      rw [cubicKernelSubdivisionSlot_card L]

/-- The raw orientation choices are one independent Boolean choice for each
loop label of the fixed kernel. -/
theorem cubicKernelLoopOrientationBits_card
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :
    Fintype.card (CubicKernelLoopOrientationBits H) =
      2 ^ Fintype.card (CubicKernelLoopEdge H) := by
  classical
  change Fintype.card (CubicKernelLoopEdge H → Bool) = _
  rw [Fintype.card_fun, Fintype.card_bool]

end PerronWright.GraphCore
