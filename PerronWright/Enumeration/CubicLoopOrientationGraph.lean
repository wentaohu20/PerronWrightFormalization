import PerronWright.Enumeration.CubicLoopOrientationAction
import PerronWright.Enumeration.CubicSubdivisionSuppressionRecovery

/-!
# Edgewise graph invariance under reversal of a subdivided loop
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Reverse the edge positions on one subdivided loop. -/
def loopEdgeSubdivisionSlotReverseEquiv
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (e : CubicKernelLoopEdge H) :
    (Σ f : Fin (3 * ell), Fin ((L.length f).val + 1)) ≃
      (Σ f : Fin (3 * ell), Fin ((L.length f).val + 1)) :=
  Equiv.sigmaCongrRight fun f =>
    if h : f = e.1 then
      h ▸ Fin.revPerm
    else Equiv.refl _

@[simp]
theorem loopEdgeSubdivisionSlotReverseEquiv_same
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (e : CubicKernelLoopEdge H)
    (i : Fin ((L.length e.1).val + 1)) :
    loopEdgeSubdivisionSlotReverseEquiv L e ⟨e.1, i⟩ =
      ⟨e.1, Fin.rev i⟩ := by
  unfold loopEdgeSubdivisionSlotReverseEquiv
  rw [Equiv.sigmaCongrRight_apply]
  simp

@[simp]
theorem loopEdgeSubdivisionSlotReverseEquiv_other
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (e : CubicKernelLoopEdge H) (f : Fin (3 * ell))
    (hfe : f ≠ e.1) (i : Fin ((L.length f).val + 1)) :
    loopEdgeSubdivisionSlotReverseEquiv L e ⟨f, i⟩ = ⟨f, i⟩ := by
  unfold loopEdgeSubdivisionSlotReverseEquiv
  rw [Equiv.sigmaCongrRight_apply]
  simp [hfe]

@[simp]
theorem loopEdgeSubdivisionSlotReverseEquiv_zero
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (e : CubicKernelLoopEdge H) :
    loopEdgeSubdivisionSlotReverseEquiv L e
        ⟨e.1, (0 : Fin ((L.length e.1).val + 1))⟩ =
      ⟨e.1, Fin.last (L.length e.1).val⟩ := by
  rw [loopEdgeSubdivisionSlotReverseEquiv_same]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Fin.ext
    simp

@[simp]
theorem loopEdgeSubdivisionSlotReverseEquiv_last
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (e : CubicKernelLoopEdge H) :
    loopEdgeSubdivisionSlotReverseEquiv L e
        ⟨e.1, Fin.last (L.length e.1).val⟩ =
      ⟨e.1, (0 : Fin ((L.length e.1).val + 1))⟩ := by
  rw [loopEdgeSubdivisionSlotReverseEquiv_same]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Fin.ext
    simp

@[simp]
theorem loopEdgeSubdivisionSlotReverseEquiv_middle
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H)
    (i : Fin ((D.profile.length e.1).val - 1)) :
    loopEdgeSubdivisionSlotReverseEquiv D.profile e
        (D.middleEdgeSlot
          (⟨e.1, i⟩ : CubicKernelSubdivisionMiddleSlot D)) =
      D.middleEdgeSlot
        (⟨e.1, Fin.rev i⟩ : CubicKernelSubdivisionMiddleSlot D) := by
  unfold CubicKernelSubdivisionDatum.middleEdgeSlot
  rw [loopEdgeSubdivisionSlotReverseEquiv_same]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Fin.ext
    simp [Fin.val_rev]
    omega

theorem cubicKernelOrderedEndpoints_eq_of_loop
    {ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (e : CubicKernelLoopEdge H) :
    (cubicKernelOrderedEndpoints H e.1).1 =
      (cubicKernelOrderedEndpoints H e.1).2 :=
  (cubicKernelOrderedEndpoints_eq_iff_isDiag H e.1).2 e.2

theorem CubicKernelSubdivisionDatum.reverseLoop_subdivisionEdge_start
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) :
    (D.reverseLoop e).subdivisionEdge
        (⟨e.1, (0 : Fin
          (((D.reverseLoop e).profile.length e.1).val + 1))⟩ :
          CubicKernelSubdivisionEdgeSlot (D.reverseLoop e)) =
      D.subdivisionEdge
        (⟨e.1, Fin.last (D.profile.length e.1).val⟩ :
          CubicKernelSubdivisionEdgeSlot D) := by
  have hepos : 0 < (D.profile.length e.1).val :=
    lt_of_lt_of_le (by omega) (D.profile.loopLength e.1 e.2)
  have hepos' : 0 < ((D.reverseLoop e).profile.length e.1).val := by
    simpa only [D.reverseLoop_profile] using hepos
  rw [(D.reverseLoop e).subdivisionEdge_start e.1 hepos',
    D.subdivisionEdge_end e.1 hepos]
  apply (Sym2.eq_iff).2
  right
  constructor
  · exact congrArg D.branchLabel (cubicKernelOrderedEndpoints_eq_of_loop e)
  · have hlabel := D.reverseLoop_pathLabel_same e
        (⟨0, hepos⟩ : Fin (D.profile.length e.1).val)
    calc
      (D.reverseLoop e).pathLabel e.1 ⟨0, hepos'⟩ =
          D.pathLabel e.1
            (Fin.rev (⟨0, hepos⟩ : Fin (D.profile.length e.1).val)) := by
        simpa only [D.reverseLoop_profile] using hlabel
      _ = D.pathLabel e.1
          ⟨(D.profile.length e.1).val - 1, by omega⟩ := by
        congr 2

theorem CubicKernelSubdivisionDatum.reverseLoop_subdivisionEdge_end
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) :
    (D.reverseLoop e).subdivisionEdge
        (⟨e.1, Fin.last ((D.reverseLoop e).profile.length e.1).val⟩ :
          CubicKernelSubdivisionEdgeSlot (D.reverseLoop e)) =
      D.subdivisionEdge
        (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
          CubicKernelSubdivisionEdgeSlot D) := by
  have hepos : 0 < (D.profile.length e.1).val :=
    lt_of_lt_of_le (by omega) (D.profile.loopLength e.1 e.2)
  have hepos' : 0 < ((D.reverseLoop e).profile.length e.1).val := by
    simpa only [D.reverseLoop_profile] using hepos
  rw [(D.reverseLoop e).subdivisionEdge_end e.1 hepos',
    D.subdivisionEdge_start e.1 hepos]
  apply (Sym2.eq_iff).2
  right
  constructor
  · let i : Fin (D.profile.length e.1).val :=
      ⟨(D.profile.length e.1).val - 1, by omega⟩
    have hlabel := D.reverseLoop_pathLabel_same e i
    calc
      (D.reverseLoop e).pathLabel e.1
          ⟨((D.reverseLoop e).profile.length e.1).val - 1, by omega⟩ =
          D.pathLabel e.1 (Fin.rev i) := by
        simpa only [D.reverseLoop_profile, i] using hlabel
      _ = D.pathLabel e.1 ⟨0, hepos⟩ := by
        congr 2
        apply Fin.ext
        simp [i, Fin.val_rev]
        omega
  · exact congrArg D.branchLabel
      (cubicKernelOrderedEndpoints_eq_of_loop e).symm

theorem CubicKernelSubdivisionDatum.reverseLoop_subdivisionEdge_middle
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H)
    (i : Fin ((D.profile.length e.1).val - 1)) :
    (D.reverseLoop e).subdivisionEdge
        ((D.reverseLoop e).middleEdgeSlot
          (⟨e.1, i⟩ : CubicKernelSubdivisionMiddleSlot (D.reverseLoop e))) =
      D.subdivisionEdge
        (D.middleEdgeSlot
          (⟨e.1, Fin.rev i⟩ : CubicKernelSubdivisionMiddleSlot D)) := by
  rw [(D.reverseLoop e).subdivisionEdge_middle e.1 i,
    D.subdivisionEdge_middle e.1 (Fin.rev i)]
  apply (Sym2.eq_iff).2
  right
  constructor
  · let a : Fin (D.profile.length e.1).val :=
      ⟨i.val, by have := i.isLt; omega⟩
    let b : Fin (D.profile.length e.1).val :=
      ⟨(Fin.rev i).val + 1, by
        have hi := i.isLt
        simp only [Fin.val_rev]
        omega⟩
    have hlabel := D.reverseLoop_pathLabel_same e a
    calc
      (D.reverseLoop e).pathLabel e.1
          ⟨i.val, by
            have hi : i.val < (D.profile.length e.1).val := by
              have := i.isLt
              omega
            simpa only [D.reverseLoop_profile] using hi⟩ =
          D.pathLabel e.1 (Fin.rev a) := by
        simpa only [D.reverseLoop_profile, a] using hlabel
      _ = D.pathLabel e.1 b := by
        congr 2
        apply Fin.ext
        simp [a, b, Fin.val_rev]
        omega
      _ = D.pathLabel e.1
          ⟨(Fin.rev i).val + 1, by
            have hi := i.isLt
            simp only [Fin.val_rev]
            omega⟩ := rfl
  · let a : Fin (D.profile.length e.1).val :=
      ⟨i.val + 1, by have := i.isLt; omega⟩
    let b : Fin (D.profile.length e.1).val :=
      ⟨(Fin.rev i).val, by
        have hi := i.isLt
        simp only [Fin.val_rev]
        omega⟩
    have hlabel := D.reverseLoop_pathLabel_same e a
    calc
      (D.reverseLoop e).pathLabel e.1
          ⟨i.val + 1, by
            have hi : i.val + 1 < (D.profile.length e.1).val := by
              have := i.isLt
              omega
            simpa only [D.reverseLoop_profile] using hi⟩ =
          D.pathLabel e.1 (Fin.rev a) := by
        simpa only [D.reverseLoop_profile, a] using hlabel
      _ = D.pathLabel e.1 b := by
        congr 2
        apply Fin.ext
        simp [a, b, Fin.val_rev]
        omega
      _ = D.pathLabel e.1
          ⟨(Fin.rev i).val, by
            have hi := i.isLt
            simp only [Fin.val_rev]
            omega⟩ := rfl

theorem CubicKernelSubdivisionDatum.reverseLoop_subdivisionEdge_direct_other
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) (f : Fin (3 * ell))
    (_hfe : f ≠ e.1) (hf : (D.profile.length f).val = 0) :
    (D.reverseLoop e).subdivisionEdge
        (⟨f, (0 : Fin (((D.reverseLoop e).profile.length f).val + 1))⟩ :
          CubicKernelSubdivisionEdgeSlot (D.reverseLoop e)) =
      D.subdivisionEdge
        (⟨f, (0 : Fin ((D.profile.length f).val + 1))⟩ :
          CubicKernelSubdivisionEdgeSlot D) := by
  have hf' : ((D.reverseLoop e).profile.length f).val = 0 := by
    simpa only [D.reverseLoop_profile] using hf
  rw [(D.reverseLoop e).subdivisionEdge_direct f hf',
    D.subdivisionEdge_direct f hf]
  simp

theorem CubicKernelSubdivisionDatum.reverseLoop_subdivisionEdge_start_other
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) (f : Fin (3 * ell))
    (hfe : f ≠ e.1) (hf : 0 < (D.profile.length f).val) :
    (D.reverseLoop e).subdivisionEdge
        (⟨f, (0 : Fin (((D.reverseLoop e).profile.length f).val + 1))⟩ :
          CubicKernelSubdivisionEdgeSlot (D.reverseLoop e)) =
      D.subdivisionEdge
        (⟨f, (0 : Fin ((D.profile.length f).val + 1))⟩ :
          CubicKernelSubdivisionEdgeSlot D) := by
  have hf' : 0 < ((D.reverseLoop e).profile.length f).val := by
    simpa only [D.reverseLoop_profile] using hf
  rw [(D.reverseLoop e).subdivisionEdge_start f hf',
    D.subdivisionEdge_start f hf]
  simp [D.reverseLoop_pathLabel_other e f hfe]

theorem CubicKernelSubdivisionDatum.reverseLoop_subdivisionEdge_end_other
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) (f : Fin (3 * ell))
    (hfe : f ≠ e.1) (hf : 0 < (D.profile.length f).val) :
    (D.reverseLoop e).subdivisionEdge
        (⟨f, Fin.last ((D.reverseLoop e).profile.length f).val⟩ :
          CubicKernelSubdivisionEdgeSlot (D.reverseLoop e)) =
      D.subdivisionEdge
        (⟨f, Fin.last (D.profile.length f).val⟩ :
          CubicKernelSubdivisionEdgeSlot D) := by
  have hf' : 0 < ((D.reverseLoop e).profile.length f).val := by
    simpa only [D.reverseLoop_profile] using hf
  rw [(D.reverseLoop e).subdivisionEdge_end f hf',
    D.subdivisionEdge_end f hf]
  have hlabel := D.reverseLoop_pathLabel_other e f hfe
    (⟨(D.profile.length f).val - 1, by omega⟩ :
      Fin (D.profile.length f).val)
  have hbranch := D.reverseLoop_branchLabel e
    (cubicKernelOrderedEndpoints H f).2
  simpa only [D.reverseLoop_profile] using congrArg₂
    (fun x y => s(x, y)) hlabel hbranch

theorem CubicKernelSubdivisionDatum.reverseLoop_subdivisionEdge_middle_other
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) (f : Fin (3 * ell))
    (hfe : f ≠ e.1)
    (i : Fin ((D.profile.length f).val - 1)) :
    (D.reverseLoop e).subdivisionEdge
        ((D.reverseLoop e).middleEdgeSlot
          (⟨f, i⟩ : CubicKernelSubdivisionMiddleSlot (D.reverseLoop e))) =
      D.subdivisionEdge
        (D.middleEdgeSlot
          (⟨f, i⟩ : CubicKernelSubdivisionMiddleSlot D)) := by
  rw [(D.reverseLoop e).subdivisionEdge_middle f i,
    D.subdivisionEdge_middle f i]
  have h₀ := D.reverseLoop_pathLabel_other e f hfe
    (⟨i.val, by have := i.isLt; omega⟩ : Fin (D.profile.length f).val)
  have h₁ := D.reverseLoop_pathLabel_other e f hfe
    (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (D.profile.length f).val)
  simpa only [D.reverseLoop_profile] using
    congrArg₂ (fun x y => s(x, y)) h₀ h₁

/-- Reversing one subdivided loop only permutes the edge slots: every
unordered edge emitted after reversal is the edge emitted by the reversed
position in the original datum. -/
theorem CubicKernelSubdivisionDatum.reverseLoop_subdivisionEdge
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H)
    (q : CubicKernelSubdivisionEdgeSlot D) :
    (D.reverseLoop e).subdivisionEdge q =
      D.subdivisionEdge
        (loopEdgeSubdivisionSlotReverseEquiv D.profile e q) := by
  rcases D.edgeSlot_classification q with hq | hq | hq | hq
  · rcases hq with ⟨⟨f, hf⟩, rfl⟩
    by_cases hfe : f = e.1
    · subst f
      have hloop := D.profile.loopLength e.1 e.2
      omega
    · rw [loopEdgeSubdivisionSlotReverseEquiv_other _ _ _ hfe]
      exact D.reverseLoop_subdivisionEdge_direct_other e f hfe hf
  · rcases hq with ⟨⟨f, hf⟩, rfl⟩
    by_cases hfe : f = e.1
    · subst f
      rw [loopEdgeSubdivisionSlotReverseEquiv_zero]
      exact D.reverseLoop_subdivisionEdge_start e
    · rw [loopEdgeSubdivisionSlotReverseEquiv_other _ _ _ hfe]
      exact D.reverseLoop_subdivisionEdge_start_other e f hfe hf
  · rcases hq with ⟨⟨f, hf⟩, rfl⟩
    by_cases hfe : f = e.1
    · subst f
      rw [loopEdgeSubdivisionSlotReverseEquiv_last]
      exact D.reverseLoop_subdivisionEdge_end e
    · rw [loopEdgeSubdivisionSlotReverseEquiv_other _ _ _ hfe]
      exact D.reverseLoop_subdivisionEdge_end_other e f hfe hf
  · rcases hq with ⟨⟨f, i⟩, rfl⟩
    by_cases hfe : f = e.1
    · subst f
      rw [loopEdgeSubdivisionSlotReverseEquiv_middle]
      exact D.reverseLoop_subdivisionEdge_middle e i
    · change
        (D.reverseLoop e).subdivisionEdge
            ((D.reverseLoop e).middleEdgeSlot
              (⟨f, i⟩ :
                CubicKernelSubdivisionMiddleSlot (D.reverseLoop e))) = _
      rw [D.reverseLoop_subdivisionEdge_middle_other e f hfe i]
      congr 1
      unfold CubicKernelSubdivisionDatum.middleEdgeSlot
      rw [loopEdgeSubdivisionSlotReverseEquiv_other _ _ _ hfe]

/-- Reversing one loop preserves the finite edge set of the reconstructed
graph. -/
theorem CubicKernelSubdivisionDatum.reverseLoop_reconstructedGraph_edgeFinset
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) :
    (D.reverseLoop e).reconstructedGraph.edgeFinset =
      D.reconstructedGraph.edgeFinset := by
  rw [(D.reverseLoop e).reconstructedGraph_edgeFinset_eq_image',
    D.reconstructedGraph_edgeFinset_eq_image']
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨loopEdgeSubdivisionSlotReverseEquiv D.profile e q, ?_⟩
    rw [← D.reverseLoop_subdivisionEdge e q]
    exact hq
  · rintro ⟨q, hq⟩
    let E : CubicKernelSubdivisionEdgeSlot D ≃
        CubicKernelSubdivisionEdgeSlot D :=
      loopEdgeSubdivisionSlotReverseEquiv D.profile e
    refine ⟨E.symm q, ?_⟩
    calc
      (D.reverseLoop e).subdivisionEdge (E.symm q) =
          D.subdivisionEdge (E (E.symm q)) :=
        D.reverseLoop_subdivisionEdge e (E.symm q)
      _ = D.subdivisionEdge q := by rw [E.apply_symm_apply]
      _ = z := hq

/-- Reversing the internal order on one loop is an exact symmetry of the
reconstructed labelled simple graph. -/
theorem CubicKernelSubdivisionDatum.reverseLoop_reconstructedGraph
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) :
    (D.reverseLoop e).reconstructedGraph = D.reconstructedGraph := by
  apply SimpleGraph.edgeFinset_inj.mp
  exact D.reverseLoop_reconstructedGraph_edgeFinset e

end PerronWright.GraphCore
