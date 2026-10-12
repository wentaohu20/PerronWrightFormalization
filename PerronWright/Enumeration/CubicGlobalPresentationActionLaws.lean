import PerronWright.Enumeration.CubicKernelCoordinateActionLaws

/-!
# The combined coordinate and loop action on cubic presentations

Loop-edge types depend on the endpoint table.  Consequently a loop set must
be transported along a coordinate relabelling before it can be combined with
a loop set chosen in the new coordinates.  This file supplies that exact
transport, proves that coordinate relabelling commutes with simultaneous loop
reversal, and packages the identity and composition codes on the global
sigma type of cubic presentations.

Nothing here asserts that the resulting code map is free or transitive on a
global reconstruction fibre.  Those are separate cross-kernel recovery
statements.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical symmDiff

private theorem cubicKernelSubdivisionDatum_eq_of_profile_labels
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    {D F : CubicKernelSubdivisionDatum k ell H}
    (hprofile : D.profile = F.profile)
    (hlabels : HEq D.labels F.labels) : D = F := by
  cases D with
  | mk profile labels =>
      cases F with
      | mk profile' labels' =>
          dsimp only at hprofile hlabels
          subst profile'
          have hl : labels = labels' := eq_of_heq hlabels
          subst labels'
          rfl

/-- Transport a finite set of loop labels along simultaneous kernel
coordinates. -/
def cubicKernelLoopSetCoordinateRelabel
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ : CubicKernelCoordinatePerm ell)
    (A : Finset (CubicKernelLoopEdge H)) :
    Finset (CubicKernelLoopEdge
      (finiteMultiGraphCoordinateRelabel γ H)) :=
  A.map (cubicKernelLoopEdgeCoordinateRelabelEquiv H γ).toEmbedding

/-- Membership is preserved exactly under loop-set coordinate transport. -/
@[simp]
theorem cubicKernelLoopSetCoordinateRelabel_mem
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ : CubicKernelCoordinatePerm ell)
    (A : Finset (CubicKernelLoopEdge H))
    (e : CubicKernelLoopEdge H) :
    cubicKernelLoopEdgeCoordinateRelabelEquiv H γ e ∈
        cubicKernelLoopSetCoordinateRelabel H γ A ↔
      e ∈ A := by
  simp [cubicKernelLoopSetCoordinateRelabel]

@[simp]
theorem cubicKernelLoopSetCoordinateRelabel_empty
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ : CubicKernelCoordinatePerm ell) :
    cubicKernelLoopSetCoordinateRelabel H γ ∅ = ∅ := by
  simp [cubicKernelLoopSetCoordinateRelabel]

/-- Coordinate transport preserves the size of every loop set. -/
theorem cubicKernelLoopSetCoordinateRelabel_card
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ : CubicKernelCoordinatePerm ell)
    (A : Finset (CubicKernelLoopEdge H)) :
    (cubicKernelLoopSetCoordinateRelabel H γ A).card = A.card := by
  exact Finset.card_map _

/-- A loop path is always transported in the direct branch: both ordered
endpoints coincide before and after coordinate relabelling. -/
theorem cubicKernelCoordinateRelabelDirect_of_loop
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (γ : CubicKernelCoordinatePerm ell)
    (e : CubicKernelLoopEdge H) :
    cubicKernelCoordinateRelabelDirect H γ e.1 := by
  rcases cubicKernelOrderedEndpoints_coordinateRelabel H γ e.1 with h | h
  · exact h.1
  · let e' := cubicKernelLoopEdgeCoordinateRelabelEquiv H γ e
    exact h.1.trans (cubicKernelOrderedEndpoints_eq_of_loop e').symm

/-- On a loop, coordinate transport commutes with reversal of the internal
finite path. -/
theorem CubicKernelLengthProfile.coordinatePathIndexEquiv_rev_of_loop
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ : CubicKernelCoordinatePerm ell)
    (e : CubicKernelLoopEdge H)
    (i : Fin (L.length e.1).val) :
    L.coordinatePathIndexEquiv γ e.1 (Fin.rev i) =
      Fin.rev (L.coordinatePathIndexEquiv γ e.1 i) := by
  apply Fin.ext
  rw [L.coordinatePathIndexEquiv_apply_val_of_direct γ e.1
      (cubicKernelCoordinateRelabelDirect_of_loop H γ e)]
  simp only [Fin.val_rev]
  rw [L.coordinatePathIndexEquiv_apply_val_of_direct γ e.1
      (cubicKernelCoordinateRelabelDirect_of_loop H γ e)]
  simp only [L.coordinateRelabel_length_apply]

/-- Transporting subdivision slots commutes with reversing a finite set of
loop paths, provided the loop set is transported to the new edge
coordinates. -/
theorem CubicKernelLengthProfile.coordinateRelabelSlotEquiv_loopOrientation
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H)
    (γ : CubicKernelCoordinatePerm ell)
    (A : Finset (CubicKernelLoopEdge H))
    (z : CubicKernelSubdivisionSlot L) :
    L.coordinateRelabelSlotEquiv γ (loopOrientationSetSlotEquiv L A z) =
      loopOrientationSetSlotEquiv (L.coordinateRelabel γ)
        (cubicKernelLoopSetCoordinateRelabel H γ A)
        (L.coordinateRelabelSlotEquiv γ z) := by
  cases z with
  | inl v => rfl
  | inr p =>
      rcases p with ⟨e, i⟩
      by_cases he : (H.endpoints e).IsDiag
      · let d : CubicKernelLoopEdge H := ⟨e, he⟩
        let d' : CubicKernelLoopEdge
            (finiteMultiGraphCoordinateRelabel γ H) :=
          ⟨γ.2 d.1, by
            rw [finiteMultiGraphCoordinateRelabel_endpoints]
            simp only [Equiv.symm_apply_apply]
            exact (Sym2.isDiag_map γ.1.injective).2 d.2⟩
        have hdEq :
            d' = cubicKernelLoopEdgeCoordinateRelabelEquiv H γ d := by
          apply Subtype.ext
          rfl
        by_cases hd : d ∈ A
        · have hd' : d' ∈ cubicKernelLoopSetCoordinateRelabel H γ A := by
            rw [hdEq]
            exact (cubicKernelLoopSetCoordinateRelabel_mem H γ A d).2 hd
          change
            L.coordinateRelabelSlotEquiv γ
                (loopOrientationSetSlotEquiv L A (.inr ⟨d.1, i⟩)) =
              loopOrientationSetSlotEquiv (L.coordinateRelabel γ)
                (cubicKernelLoopSetCoordinateRelabel H γ A)
                (L.coordinateRelabelSlotEquiv γ (.inr ⟨d.1, i⟩))
          rw [loopOrientationSetSlotEquiv_loop_mem L A d hd,
            L.coordinateRelabelSlotEquiv_inr]
          have htarget :
              loopOrientationSetSlotEquiv (L.coordinateRelabel γ)
                  (cubicKernelLoopSetCoordinateRelabel H γ A)
                  (.inr ⟨γ.2 d.1,
                    L.coordinatePathIndexEquiv γ d.1 i⟩) =
                .inr ⟨γ.2 d.1,
                  Fin.rev (L.coordinatePathIndexEquiv γ d.1 i)⟩ := by
            simpa only [d'] using
              loopOrientationSetSlotEquiv_loop_mem
                (L.coordinateRelabel γ)
                (cubicKernelLoopSetCoordinateRelabel H γ A) d' hd'
                (L.coordinatePathIndexEquiv γ d.1 i)
          have hrev :
              (Sum.inr
                ⟨γ.2 d.1,
                  L.coordinatePathIndexEquiv γ d.1 (Fin.rev i)⟩ :
              CubicKernelSubdivisionSlot (L.coordinateRelabel γ)) =
                .inr ⟨γ.2 d.1,
                  Fin.rev (L.coordinatePathIndexEquiv γ d.1 i)⟩ := by
            apply congrArg Sum.inr
            apply Sigma.ext
            · rfl
            · apply heq_of_eq
              exact L.coordinatePathIndexEquiv_rev_of_loop γ d i
          exact hrev.trans htarget.symm
        · have hd' : d' ∉ cubicKernelLoopSetCoordinateRelabel H γ A := by
            intro hd'
            apply hd
            apply (cubicKernelLoopSetCoordinateRelabel_mem H γ A d).mp
            rwa [← hdEq]
          change
            L.coordinateRelabelSlotEquiv γ
                (loopOrientationSetSlotEquiv L A (.inr ⟨d.1, i⟩)) =
              loopOrientationSetSlotEquiv (L.coordinateRelabel γ)
                (cubicKernelLoopSetCoordinateRelabel H γ A)
                (L.coordinateRelabelSlotEquiv γ (.inr ⟨d.1, i⟩))
          rw [loopOrientationSetSlotEquiv_loop_not_mem L A d hd,
            L.coordinateRelabelSlotEquiv_inr]
          have htarget :
              loopOrientationSetSlotEquiv (L.coordinateRelabel γ)
                  (cubicKernelLoopSetCoordinateRelabel H γ A)
                  (.inr ⟨γ.2 d.1,
                    L.coordinatePathIndexEquiv γ d.1 i⟩) =
                .inr ⟨γ.2 d.1,
                  L.coordinatePathIndexEquiv γ d.1 i⟩ := by
            simpa only [d'] using
              loopOrientationSetSlotEquiv_loop_not_mem
                (L.coordinateRelabel γ)
                (cubicKernelLoopSetCoordinateRelabel H γ A) d' hd'
                (L.coordinatePathIndexEquiv γ d.1 i)
          exact htarget.symm
      · have he' :
            ¬((finiteMultiGraphCoordinateRelabel γ H).endpoints
              (γ.2 e)).IsDiag := by
          intro hdiag
          apply he
          apply (Sym2.isDiag_map γ.1.injective).mp
          simpa only [finiteMultiGraphCoordinateRelabel_endpoints,
            Equiv.symm_apply_apply] using hdiag
        rw [loopOrientationSetSlotEquiv_nonloop L A e he,
          L.coordinateRelabelSlotEquiv_inr]
        exact (loopOrientationSetSlotEquiv_nonloop
          (L.coordinateRelabel γ)
          (cubicKernelLoopSetCoordinateRelabel H γ A) (γ.2 e) he'
          (L.coordinatePathIndexEquiv γ e i)).symm

/-- Coordinate relabelling and simultaneous loop reversal commute exactly
after transporting the loop set. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_coordinateRelabel
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (A : Finset (CubicKernelLoopEdge H))
    (γ : CubicKernelCoordinatePerm ell) :
    (D.reverseLoops A).coordinateRelabel γ =
      (D.coordinateRelabel γ).reverseLoops
        (cubicKernelLoopSetCoordinateRelabel H γ A) := by
  apply cubicKernelSubdivisionDatum_eq_of_profile_labels
  · rfl
  · apply heq_of_eq
    apply Equiv.ext
    intro y
    let E := D.profile.coordinateRelabelSlotEquiv γ
    obtain ⟨z, rfl⟩ := E.surjective y
    change
      D.labels
          (loopOrientationSetSlotEquiv D.profile A (E.symm (E z))) =
        D.labels
          (E.symm
            (loopOrientationSetSlotEquiv (D.profile.coordinateRelabel γ)
              (cubicKernelLoopSetCoordinateRelabel H γ A) (E z)))
    rw [E.symm_apply_apply,
      ← D.profile.coordinateRelabelSlotEquiv_loopOrientation γ A z,
      E.symm_apply_apply]

/-- Cast a loop set across an equality of endpoint tables.  This is used only
to reconcile the nested and composite coordinate transports. -/
def cubicKernelLoopSetCast
    {ell : ℕ}
    {H E : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (h : H = E)
    (A : Finset (CubicKernelLoopEdge H)) :
    Finset (CubicKernelLoopEdge E) := by
  subst E
  exact A

@[simp]
theorem cubicKernelLoopSetCast_rfl
    {ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (A : Finset (CubicKernelLoopEdge H)) :
    cubicKernelLoopSetCast rfl A = A :=
  rfl

/-- Loop reversal respects simultaneous transport of its endpoint-table
index, datum, and loop set. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_cast_heq
    {k ell : ℕ}
    {H E : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (hH : H = E)
    {D : CubicKernelSubdivisionDatum k ell H}
    {F : CubicKernelSubdivisionDatum k ell E}
    (hD : HEq D F)
    (A : Finset (CubicKernelLoopEdge H)) :
    HEq (D.reverseLoops A)
      (F.reverseLoops (cubicKernelLoopSetCast hH A)) := by
  cases hH
  have hDF : D = F := eq_of_heq hD
  cases hDF
  rfl

namespace CubicKernelPresentation

/-- The neutral dependent symmetry code. -/
def identitySymmetryCode {k ell : ℕ}
    (P : CubicKernelPresentation k ell) : P.SymmetryCode :=
  ⟨CubicKernelCoordinatePerm.refl ell, ∅⟩

/-- Compose two dependent symmetry codes.  The first loop set is transported
through the second coordinate change, combined with the second loop set by
symmetric difference, and finally cast from the nested endpoint table to the
endpoint table of the composite coordinate permutation. -/
def composeSymmetryCode {k ell : ℕ}
    (P : CubicKernelPresentation k ell)
    (c : P.SymmetryCode)
    (d : (P.applySymmetry c).SymmetryCode) :
    P.SymmetryCode :=
  let hH := finiteMultiGraphCoordinateRelabel_trans P.1.graph c.1 d.1
  ⟨CubicKernelCoordinatePerm.trans c.1 d.1,
    cubicKernelLoopSetCast hH
      (cubicKernelLoopSetCoordinateRelabel
        (finiteMultiGraphCoordinateRelabel c.1 P.1.graph) d.1 c.2 ∆ d.2)⟩

/-- Applying the neutral code fixes every global presentation. -/
@[simp]
theorem applySymmetry_identitySymmetryCode {k ell : ℕ}
    (P : CubicKernelPresentation k ell) :
    P.applySymmetry P.identitySymmetryCode = P := by
  change
    ⟨P.1.coordinateRelabel (CubicKernelCoordinatePerm.refl ell),
      (P.2.coordinateRelabel
        (CubicKernelCoordinatePerm.refl ell)).reverseLoops ∅⟩ = P
  rw [CubicKernelSubdivisionDatum.reverseLoops_empty]
  exact P.coordinateRelabel_refl

/-- Dependent composition law for the combined coordinate-and-loop codes.
The statement concerns only the action of the codes; it does not assert that
different codes give different presentations. -/
theorem applySymmetry_composeSymmetryCode {k ell : ℕ}
    (P : CubicKernelPresentation k ell)
    (c : P.SymmetryCode)
    (d : (P.applySymmetry c).SymmetryCode) :
    (P.applySymmetry c).applySymmetry d =
      P.applySymmetry (P.composeSymmetryCode c d) := by
  rcases c with ⟨γ, A⟩
  rcases d with ⟨η, B⟩
  change Finset (CubicKernelLoopEdge
    (finiteMultiGraphCoordinateRelabel γ P.1.graph)) at A
  change Finset (CubicKernelLoopEdge
    (finiteMultiGraphCoordinateRelabel η
      (finiteMultiGraphCoordinateRelabel γ P.1.graph))) at B
  let Aη := cubicKernelLoopSetCoordinateRelabel
    (finiteMultiGraphCoordinateRelabel γ P.1.graph) η A
  let hH := finiteMultiGraphCoordinateRelabel_trans P.1.graph γ η
  change
    (⟨(P.1.coordinateRelabel γ).coordinateRelabel η,
      ((((P.2.coordinateRelabel γ).reverseLoops A).coordinateRelabel η).reverseLoops B)⟩ :
        CubicKernelPresentation k ell) =
      (⟨P.1.coordinateRelabel (CubicKernelCoordinatePerm.trans γ η),
        (P.2.coordinateRelabel
          (CubicKernelCoordinatePerm.trans γ η)).reverseLoops
            (cubicKernelLoopSetCast hH (Aη ∆ B))⟩ :
        CubicKernelPresentation k ell)
  apply Sigma.ext (P.1.coordinateRelabel_trans γ η)
  have hcommute :
      (((P.2.coordinateRelabel γ).reverseLoops A).coordinateRelabel η) =
        ((P.2.coordinateRelabel γ).coordinateRelabel η).reverseLoops Aη :=
    (P.2.coordinateRelabel γ).reverseLoops_coordinateRelabel A η
  rw [hcommute,
    CubicKernelSubdivisionDatum.reverseLoops_reverseLoops]
  exact CubicKernelSubdivisionDatum.reverseLoops_cast_heq hH
    (P.2.coordinateRelabel_trans_heq γ η) (Aη ∆ B)

end CubicKernelPresentation

end PerronWright.GraphCore
