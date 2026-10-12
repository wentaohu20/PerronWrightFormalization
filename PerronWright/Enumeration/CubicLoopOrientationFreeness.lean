import PerronWright.Enumeration.CubicLoopOrientationAction

/-!
# Freeness of one-loop orientation reversal

Every loop of an admissible cubic subdivision contains at least two internal
vertices.  Reversing their order is therefore a genuine, fixed-point-free
involution on the labelled subdivision data.  These are the local facts
needed to assemble the Boolean loop-orientation fibre.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Reversing one loop twice restores the complete subdivision datum, not
merely its reconstructed graph. -/
theorem CubicKernelSubdivisionDatum.reverseLoop_reverseLoop
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) :
    (D.reverseLoop e).reverseLoop e = D := by
  cases D with
  | mk profile labels =>
      dsimp only [CubicKernelSubdivisionDatum.reverseLoop]
      congr 1
      apply Equiv.ext
      intro z
      simp only [Equiv.trans_apply]
      exact congrArg labels
        (loopEdgeSlotReverseEquiv_apply_apply profile e z)

/-- Slot reversals on two loop labels commute. -/
theorem loopEdgeSlotReverseEquiv_commute
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (e f : CubicKernelLoopEdge H)
    (z : CubicKernelSubdivisionSlot L) :
    loopEdgeSlotReverseEquiv L e (loopEdgeSlotReverseEquiv L f z) =
      loopEdgeSlotReverseEquiv L f (loopEdgeSlotReverseEquiv L e z) := by
  cases z with
  | inl v =>
      simp only [loopEdgeSlotReverseEquiv_inl]
      rfl
  | inr p =>
      rcases p with ⟨g, i⟩
      by_cases hge : g = e.1
      · subst g
        by_cases hef : e = f
        · subst f
          simp only [loopEdgeSlotReverseEquiv_same]
          rfl
        · have hefval : e.1 ≠ f.1 := fun h => hef (Subtype.ext h)
          simp only [loopEdgeSlotReverseEquiv_same,
            loopEdgeSlotReverseEquiv_other L f e.1 hefval]
          rfl
      · by_cases hgf : g = f.1
        · subst g
          simp only [loopEdgeSlotReverseEquiv_same,
            loopEdgeSlotReverseEquiv_other L e f.1 hge]
          rfl
        · simp only [loopEdgeSlotReverseEquiv_other L e g hge,
            loopEdgeSlotReverseEquiv_other L f g hgf]
          rfl

/-- Reversals at arbitrary loop labels commute on complete subdivision
data. -/
theorem CubicKernelSubdivisionDatum.reverseLoop_commute
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e f : CubicKernelLoopEdge H) :
    (D.reverseLoop e).reverseLoop f =
      (D.reverseLoop f).reverseLoop e := by
  cases D with
  | mk profile labels =>
      dsimp only [CubicKernelSubdivisionDatum.reverseLoop]
      congr 1
      apply Equiv.ext
      intro z
      simp only [Equiv.trans_apply]
      exact congrArg labels
        (loopEdgeSlotReverseEquiv_commute profile e f z)

/-- On every admissible loop, reversal changes the slot labelling.  The
loop-length condition excludes the only possible fixed cases of reversal,
namely paths with at most one internal vertex. -/
theorem CubicKernelSubdivisionDatum.reverseLoop_labels_ne
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) :
    (D.reverseLoop e).labels ≠ D.labels := by
  intro hlabels
  have hlen : 2 ≤ (D.profile.length e.1).val :=
    D.profile.loopLength e.1 e.2
  let i : Fin (D.profile.length e.1).val := ⟨0, by omega⟩
  let z : CubicKernelSubdivisionSlot D.profile := .inr ⟨e.1, i⟩
  have hvalue := congrArg
    (fun f : CubicKernelSubdivisionSlot D.profile ≃ Fin k => f z) hlabels
  change D.labels (loopEdgeSlotReverseEquiv D.profile e z) =
    D.labels z at hvalue
  have hslot := D.labels.injective hvalue
  dsimp only [z] at hslot
  rw [loopEdgeSlotReverseEquiv_same] at hslot
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

/-- Consequently the one-loop reversal has no fixed subdivision datum. -/
theorem CubicKernelSubdivisionDatum.reverseLoop_ne
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : CubicKernelLoopEdge H) :
    D.reverseLoop e ≠ D := by
  intro hdatum
  apply D.reverseLoop_labels_ne e
  have hsigma := congrArg
    (fun F : CubicKernelSubdivisionDatum k ell H =>
      (⟨F.profile, F.labels⟩ :
        Σ L : CubicKernelLengthProfile k ell H,
          CubicKernelSubdivisionSlot L ≃ Fin k)) hdatum
  exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2

end PerronWright.GraphCore
