import PerronWright.Enumeration.CubicLoopOrientationFreeness
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Powerset

/-!
# The Boolean action of loop orientations

A finite set of loop edges acts on a cubic-kernel subdivision datum by
reversing exactly the internal label orders carried by those loops.  The
composition law is symmetric difference.  Because every admissible loop has
at least two internal vertices, every nonempty orientation set acts without
fixed points.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical symmDiff

/-- Simultaneously reverse the internal slots on precisely the loop edges in
`A`.  Writing this equivalence coordinatewise makes the Boolean composition
law independent of an ordering of `A`. -/
def loopOrientationSetSlotEquiv
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (A : Finset (CubicKernelLoopEdge H)) :
    CubicKernelSubdivisionSlot L ≃ CubicKernelSubdivisionSlot L :=
  Equiv.sumCongr (Equiv.refl _) <|
    Equiv.sigmaCongrRight fun f =>
      if hf : (H.endpoints f).IsDiag then
        if (⟨f, hf⟩ : CubicKernelLoopEdge H) ∈ A then
          Fin.revPerm
        else
          Equiv.refl _
      else
        Equiv.refl _

@[simp]
theorem loopOrientationSetSlotEquiv_inl
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (A : Finset (CubicKernelLoopEdge H)) (v : Fin (2 * ell)) :
    loopOrientationSetSlotEquiv L A (.inl v) = .inl v :=
  rfl

@[simp]
theorem loopOrientationSetSlotEquiv_loop_mem
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (A : Finset (CubicKernelLoopEdge H))
    (e : CubicKernelLoopEdge H) (he : e ∈ A)
    (i : Fin (L.length e.1).val) :
    loopOrientationSetSlotEquiv L A (.inr ⟨e.1, i⟩) =
      .inr ⟨e.1, Fin.rev i⟩ := by
  change Sum.map (id : Fin (2 * ell) → Fin (2 * ell)) _
    (Sum.inr (α := Fin (2 * ell))
      (⟨e.1, i⟩ : Σ f : Fin (3 * ell), Fin (L.length f).val)) = _
  rw [Sum.map_inr]
  congr 1
  rw [Equiv.sigmaCongrRight_apply]
  simp only [e.2, dite_true]
  have hsub : (⟨e.1, e.2⟩ : CubicKernelLoopEdge H) = e :=
    Subtype.ext rfl
  simp only [hsub, he, if_true]
  rfl

@[simp]
theorem loopOrientationSetSlotEquiv_loop_not_mem
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (A : Finset (CubicKernelLoopEdge H))
    (e : CubicKernelLoopEdge H) (he : e ∉ A)
    (i : Fin (L.length e.1).val) :
    loopOrientationSetSlotEquiv L A (.inr ⟨e.1, i⟩) =
      .inr ⟨e.1, i⟩ := by
  change Sum.map (id : Fin (2 * ell) → Fin (2 * ell)) _
    (Sum.inr (α := Fin (2 * ell))
      (⟨e.1, i⟩ : Σ f : Fin (3 * ell), Fin (L.length f).val)) = _
  rw [Sum.map_inr]
  congr 1
  rw [Equiv.sigmaCongrRight_apply]
  simp only [e.2, dite_true]
  have hsub : (⟨e.1, e.2⟩ : CubicKernelLoopEdge H) = e :=
    Subtype.ext rfl
  simp only [hsub, he, if_false]
  rfl

@[simp]
theorem loopOrientationSetSlotEquiv_nonloop
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (A : Finset (CubicKernelLoopEdge H))
    (f : Fin (3 * ell)) (hf : ¬ (H.endpoints f).IsDiag)
    (i : Fin (L.length f).val) :
    loopOrientationSetSlotEquiv L A (.inr ⟨f, i⟩) =
      .inr ⟨f, i⟩ := by
  change Sum.map (id : Fin (2 * ell) → Fin (2 * ell)) _
    (Sum.inr (α := Fin (2 * ell))
      (⟨f, i⟩ : Σ j : Fin (3 * ell), Fin (L.length j).val)) = _
  rw [Sum.map_inr]
  congr 1
  rw [Equiv.sigmaCongrRight_apply]
  simp only [hf, dite_false]
  rfl

/-- The coordinatewise orientation equivalences compose by symmetric
difference of their loop sets. -/
theorem loopOrientationSetSlotEquiv_symmDiff_apply
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (A B : Finset (CubicKernelLoopEdge H))
    (z : CubicKernelSubdivisionSlot L) :
    loopOrientationSetSlotEquiv L (A ∆ B) z =
      loopOrientationSetSlotEquiv L A
        (loopOrientationSetSlotEquiv L B z) := by
  cases z with
  | inl v => rfl
  | inr p =>
      rcases p with ⟨f, i⟩
      by_cases hf : (H.endpoints f).IsDiag
      · let e : CubicKernelLoopEdge H := ⟨f, hf⟩
        change
          loopOrientationSetSlotEquiv L (A ∆ B)
              (.inr ⟨e.1, i⟩) =
            loopOrientationSetSlotEquiv L A
              (loopOrientationSetSlotEquiv L B (.inr ⟨e.1, i⟩))
        by_cases hA : e ∈ A <;> by_cases hB : e ∈ B
        · have hAB : e ∉ A ∆ B := by
            simp [Finset.mem_symmDiff, hA, hB]
          rw [loopOrientationSetSlotEquiv_loop_not_mem L (A ∆ B) e hAB,
            loopOrientationSetSlotEquiv_loop_mem L B e hB,
            loopOrientationSetSlotEquiv_loop_mem L A e hA,
            Fin.rev_rev]
        · have hAB : e ∈ A ∆ B := by
            simp [Finset.mem_symmDiff, hA, hB]
          rw [loopOrientationSetSlotEquiv_loop_mem L (A ∆ B) e hAB,
            loopOrientationSetSlotEquiv_loop_not_mem L B e hB,
            loopOrientationSetSlotEquiv_loop_mem L A e hA]
        · have hAB : e ∈ A ∆ B := by
            simp [Finset.mem_symmDiff, hA, hB]
          rw [loopOrientationSetSlotEquiv_loop_mem L (A ∆ B) e hAB,
            loopOrientationSetSlotEquiv_loop_mem L B e hB,
            loopOrientationSetSlotEquiv_loop_not_mem L A e hA]
        · have hAB : e ∉ A ∆ B := by
            simp [Finset.mem_symmDiff, hA, hB]
          rw [loopOrientationSetSlotEquiv_loop_not_mem L (A ∆ B) e hAB,
            loopOrientationSetSlotEquiv_loop_not_mem L B e hB,
            loopOrientationSetSlotEquiv_loop_not_mem L A e hA]
      · rw [loopOrientationSetSlotEquiv_nonloop L (A ∆ B) f hf,
          loopOrientationSetSlotEquiv_nonloop L B f hf,
          loopOrientationSetSlotEquiv_nonloop L A f hf]

/-- Reverse all and only the loop orientations belonging to `A`. -/
def CubicKernelSubdivisionDatum.reverseLoops
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (A : Finset (CubicKernelLoopEdge H)) :
    CubicKernelSubdivisionDatum k ell H where
  profile := D.profile
  labels := (loopOrientationSetSlotEquiv D.profile A).trans D.labels

@[simp]
theorem CubicKernelSubdivisionDatum.reverseLoops_profile
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (A : Finset (CubicKernelLoopEdge H)) :
    (D.reverseLoops A).profile = D.profile :=
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.reverseLoops_branchLabel
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (A : Finset (CubicKernelLoopEdge H)) (v : Fin (2 * ell)) :
    (D.reverseLoops A).branchLabel v = D.branchLabel v :=
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.reverseLoops_pathLabel_mem
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (A : Finset (CubicKernelLoopEdge H))
    (e : CubicKernelLoopEdge H) (he : e ∈ A)
    (i : Fin (D.profile.length e.1).val) :
    (D.reverseLoops A).pathLabel e.1 i =
      D.pathLabel e.1 (Fin.rev i) := by
  change D.labels
    (loopOrientationSetSlotEquiv D.profile A (.inr ⟨e.1, i⟩)) = _
  rw [loopOrientationSetSlotEquiv_loop_mem _ _ _ he]
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.reverseLoops_pathLabel_not_mem
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (A : Finset (CubicKernelLoopEdge H))
    (e : CubicKernelLoopEdge H) (he : e ∉ A)
    (i : Fin (D.profile.length e.1).val) :
    (D.reverseLoops A).pathLabel e.1 i = D.pathLabel e.1 i := by
  change D.labels
    (loopOrientationSetSlotEquiv D.profile A (.inr ⟨e.1, i⟩)) = _
  rw [loopOrientationSetSlotEquiv_loop_not_mem _ _ _ he]
  rfl

@[simp]
theorem CubicKernelSubdivisionDatum.reverseLoops_empty
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    D.reverseLoops ∅ = D := by
  cases D with
  | mk profile labels =>
      dsimp only [reverseLoops]
      congr 1
      apply Equiv.ext
      intro z
      cases z with
      | inl v => rfl
      | inr p =>
          rcases p with ⟨f, i⟩
          by_cases hf : (H.endpoints f).IsDiag
          · let e : CubicKernelLoopEdge H := ⟨f, hf⟩
            change labels
              (loopOrientationSetSlotEquiv profile ∅ (.inr ⟨f, i⟩)) =
              labels (.inr ⟨f, i⟩)
            rw [loopOrientationSetSlotEquiv_loop_not_mem profile ∅ e
              (by simp)]
          · change labels
              (loopOrientationSetSlotEquiv profile ∅ (.inr ⟨f, i⟩)) =
              labels (.inr ⟨f, i⟩)
            rw [loopOrientationSetSlotEquiv_nonloop profile ∅ f hf]

/-- This is a Boolean action: applying `B` after `A` is the same as
reversing the symmetric difference `A ∆ B`. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_reverseLoops
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (A B : Finset (CubicKernelLoopEdge H)) :
    (D.reverseLoops A).reverseLoops B = D.reverseLoops (A ∆ B) := by
  cases D with
  | mk profile labels =>
      dsimp only [reverseLoops]
      congr 1
      apply Equiv.ext
      intro z
      change labels
        (loopOrientationSetSlotEquiv profile A
          (loopOrientationSetSlotEquiv profile B z)) =
        labels (loopOrientationSetSlotEquiv profile (A ∆ B) z)
      rw [loopOrientationSetSlotEquiv_symmDiff_apply]

/-- Every Boolean orientation element is its own inverse. -/
@[simp]
theorem CubicKernelSubdivisionDatum.reverseLoops_reverseLoops_self
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (A : Finset (CubicKernelLoopEdge H)) :
    (D.reverseLoops A).reverseLoops A = D := by
  rw [D.reverseLoops_reverseLoops A A]
  rw [symmDiff_self]
  convert D.reverseLoops_empty using 1
  simp

/-- A nonempty set of loop reversals changes the complete slot labelling. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_labels_ne
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (A : Finset (CubicKernelLoopEdge H))
    (hA : A.Nonempty) :
    (D.reverseLoops A).labels ≠ D.labels := by
  rcases hA with ⟨e, he⟩
  intro hlabels
  have hlen : 2 ≤ (D.profile.length e.1).val :=
    D.profile.loopLength e.1 e.2
  let i : Fin (D.profile.length e.1).val := ⟨0, by omega⟩
  let z : CubicKernelSubdivisionSlot D.profile := .inr ⟨e.1, i⟩
  have hvalue := congrArg
    (fun f : CubicKernelSubdivisionSlot D.profile ≃ Fin k => f z) hlabels
  change D.labels (loopOrientationSetSlotEquiv D.profile A z) =
    D.labels z at hvalue
  rw [show z = (.inr ⟨e.1, i⟩ : CubicKernelSubdivisionSlot D.profile) by rfl,
    loopOrientationSetSlotEquiv_loop_mem _ _ _ he] at hvalue
  have hslot := D.labels.injective hvalue
  have hsigma :
      (⟨e.1, Fin.rev i⟩ :
          Σ f : Fin (3 * ell), Fin (D.profile.length f).val) =
        ⟨e.1, i⟩ := by
    exact Sum.inr.inj hslot
  have hfin : Fin.rev i = i :=
    eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
  have hrevpos : 0 < (Fin.rev i).val := by
    dsimp only [i]
    change 0 < (D.profile.length e.1).val - 1
    omega
  have hval := congrArg Fin.val hfin
  have hzero : (Fin.rev i).val = 0 := by
    simpa only [i, Fin.val_mk] using hval
  exact (Nat.ne_of_gt hrevpos) hzero

/-- Equivalently, every nonidentity element of the finite Boolean
loop-orientation group acts without fixed subdivision data. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_ne
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (A : Finset (CubicKernelLoopEdge H))
    (hA : A.Nonempty) :
    D.reverseLoops A ≠ D := by
  intro hdatum
  apply D.reverseLoops_labels_ne A hA
  have hsigma := congrArg
    (fun F : CubicKernelSubdivisionDatum k ell H =>
      (⟨F.profile, F.labels⟩ :
        Σ L : CubicKernelLengthProfile k ell H,
          CubicKernelSubdivisionSlot L ≃ Fin k)) hdatum
  exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2

/-- For a fixed labelled subdivision datum, distinct Boolean orientation
sets give distinct labelled subdivision data. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_injective
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    Function.Injective D.reverseLoops := by
  intro A B hAB
  by_contra hne
  have hnonempty : (A ∆ B).Nonempty :=
    Finset.symmDiff_nonempty.2 hne
  have hacted := congrArg
    (fun E : CubicKernelSubdivisionDatum k ell H => E.reverseLoops B) hAB
  rw [D.reverseLoops_reverseLoops A B,
    D.reverseLoops_reverseLoops_self B] at hacted
  exact D.reverseLoops_ne (A ∆ B) hnonempty hacted

/-- Hence the orbit of a fixed labelled subdivision datum under loop
orientation reversal has exactly one point for each Boolean loop choice. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_range_card
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    Fintype.card (Set.range D.reverseLoops) =
      2 ^ Fintype.card (CubicKernelLoopEdge H) := by
  rw [Set.card_range_of_injective D.reverseLoops_injective,
    Fintype.card_finset]

end PerronWright.GraphCore
