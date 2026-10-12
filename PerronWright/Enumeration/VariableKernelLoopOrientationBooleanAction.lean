import PerronWright.Enumeration.VariableKernelLoopOrientationAction
import PerronWright.Enumeration.VariableSubdivisionLengthRecovery
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Powerset

/-!
# The Boolean loop-orientation action for bounded kernels

A finite set of loop edges acts on a bounded-kernel subdivision datum by
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
def boundedKernelLoopOrientationSetSlotEquiv
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (A : Finset (BoundedKernelLoopEdge K)) :
    BoundedKernelSubdivisionSlot L ≃ BoundedKernelSubdivisionSlot L :=
  Equiv.sumCongr (Equiv.refl _) <|
    Equiv.sigmaCongrRight fun f =>
      if hf : ((boundedKernelFiniteMultiGraph K.shape).endpoints f).IsDiag then
        if (⟨f, hf⟩ : BoundedKernelLoopEdge K) ∈ A then
          Fin.revPerm
        else
          Equiv.refl _
      else
        Equiv.refl _

@[simp]
theorem boundedKernelLoopOrientationSetSlotEquiv_inl
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (A : Finset (BoundedKernelLoopEdge K)) (v : Fin K.shape.1.val) :
    boundedKernelLoopOrientationSetSlotEquiv L A (.inl v) = .inl v :=
  rfl

@[simp]
theorem boundedKernelLoopOrientationSetSlotEquiv_loop_mem
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (A : Finset (BoundedKernelLoopEdge K))
    (e : BoundedKernelLoopEdge K) (he : e ∈ A)
    (i : Fin (L.length e.1).val) :
    boundedKernelLoopOrientationSetSlotEquiv L A (.inr ⟨e.1, i⟩) =
      .inr ⟨e.1, Fin.rev i⟩ := by
  change Sum.map (id : Fin K.shape.1.val → Fin K.shape.1.val) _
    (Sum.inr (α := Fin K.shape.1.val)
      (⟨e.1, i⟩ : Σ f : Fin K.shape.2.1.val, Fin (L.length f).val)) = _
  rw [Sum.map_inr]
  congr 1
  rw [Equiv.sigmaCongrRight_apply]
  split
  · rename_i hloop
    simp only [Fin.revPerm_apply]
  · rename_i hnloop
    exact (hnloop e.2).elim

@[simp]
theorem boundedKernelLoopOrientationSetSlotEquiv_loop_not_mem
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (A : Finset (BoundedKernelLoopEdge K))
    (e : BoundedKernelLoopEdge K) (he : e ∉ A)
    (i : Fin (L.length e.1).val) :
    boundedKernelLoopOrientationSetSlotEquiv L A (.inr ⟨e.1, i⟩) =
      .inr ⟨e.1, i⟩ := by
  change Sum.map (id : Fin K.shape.1.val → Fin K.shape.1.val) _
    (Sum.inr (α := Fin K.shape.1.val)
      (⟨e.1, i⟩ : Σ f : Fin K.shape.2.1.val, Fin (L.length f).val)) = _
  rw [Sum.map_inr]
  congr 1
  rw [Equiv.sigmaCongrRight_apply]
  split
  · rename_i hloop
    simp only [Equiv.refl_apply]
  · rename_i hnloop
    exact (hnloop e.2).elim

@[simp]
theorem boundedKernelLoopOrientationSetSlotEquiv_nonloop
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (A : Finset (BoundedKernelLoopEdge K))
    (f : Fin K.shape.2.1.val) (hf : ¬ ((boundedKernelFiniteMultiGraph K.shape).endpoints f).IsDiag)
    (i : Fin (L.length f).val) :
    boundedKernelLoopOrientationSetSlotEquiv L A (.inr ⟨f, i⟩) =
      .inr ⟨f, i⟩ := by
  change Sum.map (id : Fin K.shape.1.val → Fin K.shape.1.val) _
    (Sum.inr (α := Fin K.shape.1.val)
      (⟨f, i⟩ : Σ j : Fin K.shape.2.1.val, Fin (L.length j).val)) = _
  rw [Sum.map_inr]
  congr 1
  rw [Equiv.sigmaCongrRight_apply]
  simp only [hf, dite_false]
  rfl

/-- The coordinatewise orientation equivalences compose by symmetric
difference of their loop sets. -/
theorem boundedKernelLoopOrientationSetSlotEquiv_symmDiff_apply
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (A B : Finset (BoundedKernelLoopEdge K))
    (z : BoundedKernelSubdivisionSlot L) :
    boundedKernelLoopOrientationSetSlotEquiv L (A ∆ B) z =
      boundedKernelLoopOrientationSetSlotEquiv L A
        (boundedKernelLoopOrientationSetSlotEquiv L B z) := by
  cases z with
  | inl v => rfl
  | inr p =>
      rcases p with ⟨f, i⟩
      by_cases hf : ((boundedKernelFiniteMultiGraph K.shape).endpoints f).IsDiag
      · let e : BoundedKernelLoopEdge K := ⟨f, hf⟩
        change
          boundedKernelLoopOrientationSetSlotEquiv L (A ∆ B)
              (.inr ⟨e.1, i⟩) =
            boundedKernelLoopOrientationSetSlotEquiv L A
              (boundedKernelLoopOrientationSetSlotEquiv L B (.inr ⟨e.1, i⟩))
        by_cases hA : e ∈ A <;> by_cases hB : e ∈ B
        · have hAB : e ∉ A ∆ B := by
            simp [Finset.mem_symmDiff, hA, hB]
          rw [boundedKernelLoopOrientationSetSlotEquiv_loop_not_mem L (A ∆ B) e hAB,
            boundedKernelLoopOrientationSetSlotEquiv_loop_mem L B e hB,
            boundedKernelLoopOrientationSetSlotEquiv_loop_mem L A e hA,
            Fin.rev_rev]
        · have hAB : e ∈ A ∆ B := by
            simp [Finset.mem_symmDiff, hA, hB]
          rw [boundedKernelLoopOrientationSetSlotEquiv_loop_mem L (A ∆ B) e hAB,
            boundedKernelLoopOrientationSetSlotEquiv_loop_not_mem L B e hB,
            boundedKernelLoopOrientationSetSlotEquiv_loop_mem L A e hA]
        · have hAB : e ∈ A ∆ B := by
            simp [Finset.mem_symmDiff, hA, hB]
          rw [boundedKernelLoopOrientationSetSlotEquiv_loop_mem L (A ∆ B) e hAB,
            boundedKernelLoopOrientationSetSlotEquiv_loop_mem L B e hB,
            boundedKernelLoopOrientationSetSlotEquiv_loop_not_mem L A e hA]
        · have hAB : e ∉ A ∆ B := by
            simp [Finset.mem_symmDiff, hA, hB]
          rw [boundedKernelLoopOrientationSetSlotEquiv_loop_not_mem L (A ∆ B) e hAB,
            boundedKernelLoopOrientationSetSlotEquiv_loop_not_mem L B e hB,
            boundedKernelLoopOrientationSetSlotEquiv_loop_not_mem L A e hA]
      · rw [boundedKernelLoopOrientationSetSlotEquiv_nonloop L (A ∆ B) f hf,
          boundedKernelLoopOrientationSetSlotEquiv_nonloop L B f hf,
          boundedKernelLoopOrientationSetSlotEquiv_nonloop L A f hf]

/-- Reverse all and only the loop orientations belonging to `A`. -/
def BoundedKernelSubdivisionDatum.reverseLoops
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K)) :
    BoundedKernelSubdivisionDatum k K where
  profile := D.profile
  labels := (boundedKernelLoopOrientationSetSlotEquiv D.profile A).trans D.labels

@[simp]
theorem BoundedKernelSubdivisionDatum.reverseLoops_profile
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K)) :
    (D.reverseLoops A).profile = D.profile :=
  rfl

@[simp]
theorem BoundedKernelSubdivisionDatum.reverseLoops_branchLabel
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K)) (v : Fin K.shape.1.val) :
    (D.reverseLoops A).branchLabel v = D.branchLabel v :=
  rfl

@[simp]
theorem BoundedKernelSubdivisionDatum.reverseLoops_pathLabel_mem
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K))
    (e : BoundedKernelLoopEdge K) (he : e ∈ A)
    (i : Fin (D.profile.length e.1).val) :
    (D.reverseLoops A).pathLabel e.1 i =
      D.pathLabel e.1 (Fin.rev i) := by
  change D.labels
    (boundedKernelLoopOrientationSetSlotEquiv D.profile A (.inr ⟨e.1, i⟩)) = _
  rw [boundedKernelLoopOrientationSetSlotEquiv_loop_mem _ _ _ he]
  rfl

@[simp]
theorem BoundedKernelSubdivisionDatum.reverseLoops_pathLabel_not_mem
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K))
    (e : BoundedKernelLoopEdge K) (he : e ∉ A)
    (i : Fin (D.profile.length e.1).val) :
    (D.reverseLoops A).pathLabel e.1 i = D.pathLabel e.1 i := by
  change D.labels
    (boundedKernelLoopOrientationSetSlotEquiv D.profile A (.inr ⟨e.1, i⟩)) = _
  rw [boundedKernelLoopOrientationSetSlotEquiv_loop_not_mem _ _ _ he]
  rfl

@[simp]
theorem BoundedKernelSubdivisionDatum.reverseLoops_empty
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
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
          by_cases hf : ((boundedKernelFiniteMultiGraph K.shape).endpoints f).IsDiag
          · let e : BoundedKernelLoopEdge K := ⟨f, hf⟩
            change labels
              (boundedKernelLoopOrientationSetSlotEquiv profile ∅ (.inr ⟨f, i⟩)) =
              labels (.inr ⟨f, i⟩)
            rw [boundedKernelLoopOrientationSetSlotEquiv_loop_not_mem profile ∅ e
              (by simp)]
          · change labels
              (boundedKernelLoopOrientationSetSlotEquiv profile ∅ (.inr ⟨f, i⟩)) =
              labels (.inr ⟨f, i⟩)
            rw [boundedKernelLoopOrientationSetSlotEquiv_nonloop profile ∅ f hf]

/-- This is a Boolean action: applying `B` after `A` is the same as
reversing the symmetric difference `A ∆ B`. -/
theorem BoundedKernelSubdivisionDatum.reverseLoops_reverseLoops
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (A B : Finset (BoundedKernelLoopEdge K)) :
    (D.reverseLoops A).reverseLoops B = D.reverseLoops (A ∆ B) := by
  cases D with
  | mk profile labels =>
      dsimp only [reverseLoops]
      congr 1
      apply Equiv.ext
      intro z
      change labels
        (boundedKernelLoopOrientationSetSlotEquiv profile A
          (boundedKernelLoopOrientationSetSlotEquiv profile B z)) =
        labels (boundedKernelLoopOrientationSetSlotEquiv profile (A ∆ B) z)
      rw [boundedKernelLoopOrientationSetSlotEquiv_symmDiff_apply]

/-- Every Boolean orientation element is its own inverse. -/
@[simp]
theorem BoundedKernelSubdivisionDatum.reverseLoops_reverseLoops_self
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K)) :
    (D.reverseLoops A).reverseLoops A = D := by
  rw [D.reverseLoops_reverseLoops A A]
  rw [symmDiff_self]
  convert D.reverseLoops_empty using 1
  simp

/-- A nonempty set of loop reversals changes the complete slot labelling. -/
theorem BoundedKernelSubdivisionDatum.reverseLoops_labels_ne
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K))
    (hA : A.Nonempty) :
    (D.reverseLoops A).labels ≠ D.labels := by
  rcases hA with ⟨e, he⟩
  intro hlabels
  have hlen : 2 ≤ (D.profile.length e.1).val :=
    D.profile.loopLength e.1 e.2
  let i : Fin (D.profile.length e.1).val := ⟨0, by omega⟩
  let z : BoundedKernelSubdivisionSlot D.profile := .inr ⟨e.1, i⟩
  have hvalue := congrArg
    (fun f : BoundedKernelSubdivisionSlot D.profile ≃ Fin k => f z) hlabels
  change D.labels (boundedKernelLoopOrientationSetSlotEquiv D.profile A z) =
    D.labels z at hvalue
  rw [show z = (.inr ⟨e.1, i⟩ : BoundedKernelSubdivisionSlot D.profile) by rfl,
    boundedKernelLoopOrientationSetSlotEquiv_loop_mem _ _ _ he] at hvalue
  have hslot := D.labels.injective hvalue
  have hsigma :
      (⟨e.1, Fin.rev i⟩ :
          Σ f : Fin K.shape.2.1.val, Fin (D.profile.length f).val) =
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
theorem BoundedKernelSubdivisionDatum.reverseLoops_ne
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K))
    (hA : A.Nonempty) :
    D.reverseLoops A ≠ D := by
  intro hdatum
  apply D.reverseLoops_labels_ne A hA
  have hsigma := congrArg
    (fun F : BoundedKernelSubdivisionDatum k K =>
      (⟨F.profile, F.labels⟩ :
        Σ L : BoundedKernelLengthProfile k K,
          BoundedKernelSubdivisionSlot L ≃ Fin k)) hdatum
  exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2

/-- For a fixed labelled subdivision datum, distinct Boolean orientation
sets give distinct labelled subdivision data. -/
theorem BoundedKernelSubdivisionDatum.reverseLoops_injective
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    Function.Injective D.reverseLoops := by
  intro A B hAB
  by_contra hne
  have hnonempty : (A ∆ B).Nonempty :=
    Finset.symmDiff_nonempty.2 hne
  have hacted := congrArg
    (fun E : BoundedKernelSubdivisionDatum k K => E.reverseLoops B) hAB
  rw [D.reverseLoops_reverseLoops A B,
    D.reverseLoops_reverseLoops_self B] at hacted
  exact D.reverseLoops_ne (A ∆ B) hnonempty hacted

/-- Hence the orbit of a fixed labelled subdivision datum under loop
orientation reversal has exactly one point for each Boolean loop choice. -/
theorem BoundedKernelSubdivisionDatum.reverseLoops_range_card
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    Fintype.card (Set.range D.reverseLoops) =
      2 ^ Fintype.card (BoundedKernelLoopEdge K) := by
  rw [Set.card_range_of_injective D.reverseLoops_injective,
    Fintype.card_finset]

end PerronWright.GraphCore
