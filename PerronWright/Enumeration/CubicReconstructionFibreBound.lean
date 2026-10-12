import PerronWright.Enumeration.CubicRecoveredCoordinateGlobalFibre
import PerronWright.Enumeration.CubicKernelSubdivisionCount
import Mathlib.Data.Finite.Perm

/-!
# A finite bound for one cubic reconstruction fibre

The global recovered-coordinate theorem says that, after the branch and
kernel-edge coordinates of two subdivision data have been canonically
aligned, the only remaining ambiguity is reversal of loop paths.  The
coordinate permutations themselves must still be recorded: an equality of
reconstructed labelled graphs does not distinguish normalized coordinates,
and in particular may permute parallel kernel edges.

This file packages precisely those three pieces of finite information.  It
proves that the resulting code is injective and hence bounds every fibre of
`reconstructedGraph` by

`(2 * ell)! * (3 * ell)! * 2 ^ (# loop edge labels)`.

This is deliberately a bound rather than an asserted exact symmetry factor.
An exact formula would require identifying which pairs of coordinate
permutations are automorphisms of the fixed edge-labelled cubic kernel.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Subdivision data over the fixed edge-labelled kernel which reconstruct
the same labelled simple graph as `D`. -/
abbrev CubicReconstructionFibre {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :=
  {E : CubicKernelSubdivisionDatum k ell K.graph //
    D.reconstructedGraph = E.reconstructedGraph}

/-- The unique loop-reversal set left after expressing a fibre element in
the canonical recovered coordinates of the base datum. -/
noncomputable def CubicKernelSubdivisionDatum.reconstructionFibreLoopSet
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (E : CubicReconstructionFibre K D) :
    Finset (CubicKernelLoopEdge K.graph) :=
  Classical.choose
    (D.existsUnique_reverseLoops_eq_alignedDatum K E.1 E.2)

/-- The chosen loop set has the defining recovered-coordinate property. -/
theorem CubicKernelSubdivisionDatum.reverseLoops_reconstructionFibreLoopSet
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (E : CubicReconstructionFibre K D) :
    D.reverseLoops (D.reconstructionFibreLoopSet K E) =
      D.recoveredCoordinateAlignedDatum K E.1 E.2 :=
  (Classical.choose_spec
    (D.existsUnique_reverseLoops_eq_alignedDatum K E.1 E.2)).1

/-- The chosen loop set is characterized uniquely by the defining
recovered-coordinate property. -/
theorem CubicKernelSubdivisionDatum.reconstructionFibreLoopSet_eq
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (E : CubicReconstructionFibre K D)
    (A : Finset (CubicKernelLoopEdge K.graph))
    (hA : D.reverseLoops A =
      D.recoveredCoordinateAlignedDatum K E.1 E.2) :
    A = D.reconstructionFibreLoopSet K E :=
  (Classical.choose_spec
    (D.existsUnique_reverseLoops_eq_alignedDatum K E.1 E.2)).2 A hA

/-- A subdivision datum in one reconstruction fibre is encoded by its
canonical branch-coordinate permutation, its canonical kernel-edge
permutation, and its residual loop-reversal set. -/
noncomputable def CubicKernelSubdivisionDatum.reconstructionFibreCode
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :
    CubicReconstructionFibre K D →
      ((Equiv.Perm (Fin (2 * ell)) × Equiv.Perm (Fin (3 * ell))) ×
        Finset (CubicKernelLoopEdge K.graph)) :=
  fun E ↦
    ((D.recoveredBranchCoordinatePerm K E.1 E.2,
      D.recoveredKernelEdgeCoordinatePerm K E.1 E.2),
      D.reconstructionFibreLoopSet K E)

/-- Equality of the recovered kernel-edge permutations forces equality of
the complete admissible length profiles.  The proof fields in a profile are
then immaterial by proof irrelevance. -/
private theorem CubicKernelSubdivisionDatum.profile_eq_of_recoveredKernelEdgePerm_eq
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E F : CubicKernelSubdivisionDatum k ell K.graph)
    (hE : D.reconstructedGraph = E.reconstructedGraph)
    (hF : D.reconstructedGraph = F.reconstructedGraph)
    (hperm : D.recoveredKernelEdgeCoordinatePerm K E hE =
      D.recoveredKernelEdgeCoordinatePerm K F hF) :
    E.profile = F.profile := by
  have hlength : E.profile.length = F.profile.length := by
    funext f
    let e := (D.recoveredKernelEdgeCoordinatePerm K E hE).symm f
    have heqE :
        D.recoveredKernelEdgeCoordinatePerm K E hE e = f := by
      exact (D.recoveredKernelEdgeCoordinatePerm K E hE).apply_symm_apply f
    have heqF :
        D.recoveredKernelEdgeCoordinatePerm K F hF e = f := by
      rw [← hperm]
      exact heqE
    apply Fin.ext
    calc
      (E.profile.length f).val =
          (E.profile.length
            (D.recoveredKernelEdgeCoordinatePerm K E hE e)).val := by
        rw [heqE]
      _ = (D.profile.length e).val :=
        (D.profile_length_recoveredKernelEdgeCoordinatePerm K E hE e).symm
      _ = (F.profile.length
          (D.recoveredKernelEdgeCoordinatePerm K F hF e)).val :=
        D.profile_length_recoveredKernelEdgeCoordinatePerm K F hF e
      _ = (F.profile.length f).val := by rw [heqF]
  cases hprofileE : E.profile with
  | mk lengthE totalE loopE directE =>
      cases hprofileF : F.profile with
      | mk lengthF totalF loopF directF =>
          simp only [hprofileE, hprofileF] at hlength ⊢
          subst lengthF
          rfl

/-- Once the two recovered coordinate permutations and the two aligned data
agree, the original subdivision data agree.  This is the cancellation step
which makes the finite code faithful. -/
private theorem CubicKernelSubdivisionDatum.eq_of_recoveredCoordinateData_eq
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D E F : CubicKernelSubdivisionDatum k ell K.graph)
    (hE : D.reconstructedGraph = E.reconstructedGraph)
    (hF : D.reconstructedGraph = F.reconstructedGraph)
    (hbranch : D.recoveredBranchCoordinatePerm K E hE =
      D.recoveredBranchCoordinatePerm K F hF)
    (hedge : D.recoveredKernelEdgeCoordinatePerm K E hE =
      D.recoveredKernelEdgeCoordinatePerm K F hF)
    (haligned : D.recoveredCoordinateAlignedDatum K E hE =
      D.recoveredCoordinateAlignedDatum K F hF) :
    E = F := by
  have hprofile : E.profile = F.profile :=
    D.profile_eq_of_recoveredKernelEdgePerm_eq K E F hE hF hedge
  have halignedLabels :
      D.recoveredCoordinateAlignedLabels K E hE =
        D.recoveredCoordinateAlignedLabels K F hF :=
    by
      change
        (⟨D.profile, D.recoveredCoordinateAlignedLabels K E hE⟩ :
            CubicKernelSubdivisionDatum k ell K.graph) =
          ⟨D.profile, D.recoveredCoordinateAlignedLabels K F hF⟩ at haligned
      injection haligned
  cases E with
  | mk profileE labelsE =>
      cases F with
      | mk profileF labelsF =>
          dsimp only at hprofile
          subst profileF
          have hslot :
              D.recoveredSubdivisionSlotEquiv K
                  (⟨profileE, labelsE⟩ :
                    CubicKernelSubdivisionDatum k ell K.graph) hE =
                D.recoveredSubdivisionSlotEquiv K
                  (⟨profileE, labelsF⟩ :
                    CubicKernelSubdivisionDatum k ell K.graph) hF := by
            apply Equiv.ext
            intro x
            rcases x with v | ⟨e, i⟩
            · exact congrArg (fun σ ↦ Sum.inl (σ v)) hbranch
            · apply congrArg Sum.inr
              have hedge_e :
                  D.recoveredKernelEdgeCoordinatePerm K
                      (⟨profileE, labelsE⟩ :
                        CubicKernelSubdivisionDatum k ell K.graph) hE e =
                    D.recoveredKernelEdgeCoordinatePerm K
                      (⟨profileE, labelsF⟩ :
                        CubicKernelSubdivisionDatum k ell K.graph) hF e :=
                congrArg (fun σ ↦ σ e) hedge
              apply Sigma.ext hedge_e
              have hfirst_iff :
                  (D.recoveredBranchCoordinatePerm K
                        (⟨profileE, labelsE⟩ :
                          CubicKernelSubdivisionDatum k ell K.graph) hE
                        (cubicKernelOrderedEndpoints K.graph e).1 =
                      (cubicKernelOrderedEndpoints K.graph
                        (D.recoveredKernelEdgeCoordinatePerm K
                          (⟨profileE, labelsE⟩ :
                            CubicKernelSubdivisionDatum k ell K.graph)
                          hE e)).1) ↔
                    (D.recoveredBranchCoordinatePerm K
                        (⟨profileE, labelsF⟩ :
                          CubicKernelSubdivisionDatum k ell K.graph) hF
                        (cubicKernelOrderedEndpoints K.graph e).1 =
                      (cubicKernelOrderedEndpoints K.graph
                        (D.recoveredKernelEdgeCoordinatePerm K
                          (⟨profileE, labelsF⟩ :
                            CubicKernelSubdivisionDatum k ell K.graph)
                          hF e)).1) := by
                rw [hbranch, hedge_e]
              have hpathVal :
                  (D.recoveredPathIndexEquiv K
                    (⟨profileE, labelsE⟩ :
                      CubicKernelSubdivisionDatum k ell K.graph) hE e i).val =
                  (D.recoveredPathIndexEquiv K
                    (⟨profileE, labelsF⟩ :
                      CubicKernelSubdivisionDatum k ell K.graph) hF e i).val := by
                unfold CubicKernelSubdivisionDatum.recoveredPathIndexEquiv
                by_cases hloop : (K.graph.endpoints e).IsDiag
                · simp [hloop]
                · by_cases hfirstE :
                      D.recoveredBranchCoordinatePerm K
                            (⟨profileE, labelsE⟩ :
                              CubicKernelSubdivisionDatum k ell K.graph) hE
                            (cubicKernelOrderedEndpoints K.graph e).1 =
                          (cubicKernelOrderedEndpoints K.graph
                            (D.recoveredKernelEdgeCoordinatePerm K
                              (⟨profileE, labelsE⟩ :
                                CubicKernelSubdivisionDatum k ell K.graph)
                              hE e)).1
                  · have hfirstF := hfirst_iff.mp hfirstE
                    simp [hloop, hfirstE, hfirstF]
                  · have hfirstF : ¬
                        D.recoveredBranchCoordinatePerm K
                              (⟨profileE, labelsF⟩ :
                                CubicKernelSubdivisionDatum k ell K.graph) hF
                              (cubicKernelOrderedEndpoints K.graph e).1 =
                            (cubicKernelOrderedEndpoints K.graph
                              (D.recoveredKernelEdgeCoordinatePerm K
                                (⟨profileE, labelsF⟩ :
                                  CubicKernelSubdivisionDatum k ell K.graph)
                                hF e)).1 :=
                      fun h ↦ hfirstE (hfirst_iff.mpr h)
                    simp [hloop, hfirstE, hfirstF]
              exact (Fin.heq_ext_iff
                (congrArg (fun f ↦ (profileE.length f).val) hedge_e)).2
                hpathVal
          have hlabels : labelsE = labelsF := by
            change
              (D.recoveredSubdivisionSlotEquiv K
                    (⟨profileE, labelsE⟩ :
                      CubicKernelSubdivisionDatum k ell K.graph) hE).trans
                  labelsE =
                (D.recoveredSubdivisionSlotEquiv K
                    (⟨profileE, labelsF⟩ :
                      CubicKernelSubdivisionDatum k ell K.graph) hF).trans
                  labelsF at halignedLabels
            rw [hslot] at halignedLabels
            apply Equiv.ext
            intro x
            have hx := congrArg
              (fun q : CubicKernelSubdivisionSlot D.profile ≃ Fin k ↦
                q ((D.recoveredSubdivisionSlotEquiv K
                  (⟨profileE, labelsF⟩ :
                    CubicKernelSubdivisionDatum k ell K.graph) hF).symm x))
              halignedLabels
            simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using hx
          subst labelsF
          rfl

/-- The canonical coordinate-and-loop code is injective on every fibre of
`reconstructedGraph`. -/
theorem CubicKernelSubdivisionDatum.reconstructionFibreCode_injective
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :
    Function.Injective (D.reconstructionFibreCode K) := by
  intro E F hcode
  have hbranch :
      D.recoveredBranchCoordinatePerm K E.1 E.2 =
        D.recoveredBranchCoordinatePerm K F.1 F.2 :=
    congrArg (fun c ↦ c.1.1) hcode
  have hedge :
      D.recoveredKernelEdgeCoordinatePerm K E.1 E.2 =
        D.recoveredKernelEdgeCoordinatePerm K F.1 F.2 :=
    congrArg (fun c ↦ c.1.2) hcode
  have hloop :
      D.reconstructionFibreLoopSet K E =
        D.reconstructionFibreLoopSet K F :=
    congrArg Prod.snd hcode
  have haligned :
      D.recoveredCoordinateAlignedDatum K E.1 E.2 =
        D.recoveredCoordinateAlignedDatum K F.1 F.2 := by
    calc
      D.recoveredCoordinateAlignedDatum K E.1 E.2 =
          D.reverseLoops (D.reconstructionFibreLoopSet K E) :=
        (D.reverseLoops_reconstructionFibreLoopSet K E).symm
      _ = D.reverseLoops (D.reconstructionFibreLoopSet K F) := by
        rw [hloop]
      _ = D.recoveredCoordinateAlignedDatum K F.1 F.2 :=
        D.reverseLoops_reconstructionFibreLoopSet K F
  apply Subtype.ext
  exact D.eq_of_recoveredCoordinateData_eq K E.1 F.1 E.2 F.2
    hbranch hedge haligned

/-- Every cubic reconstruction fibre is finite, with finiteness witnessed by
the explicit coordinate-and-loop code rather than by an ambient
nonconstructive finiteness assertion. -/
noncomputable instance cubicReconstructionFibreFinite
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :
    Finite (CubicReconstructionFibre K D) :=
  Finite.of_injective (D.reconstructionFibreCode K)
    (D.reconstructionFibreCode_injective K)

/-- A reconstruction fibre is bounded by arbitrary branch-coordinate and
kernel-edge permutations, together with one Boolean choice per loop edge.
This is the finite multiplicity bound needed before regrouping by a fixed
cubic kernel and length profile. -/
theorem CubicKernelSubdivisionDatum.reconstructionFibre_natCard_le
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :
    Nat.card (CubicReconstructionFibre K D) ≤
      (2 * ell).factorial * (3 * ell).factorial *
        2 ^ Fintype.card (CubicKernelLoopEdge K.graph) := by
  calc
    Nat.card (CubicReconstructionFibre K D) ≤
        Nat.card
          ((Equiv.Perm (Fin (2 * ell)) × Equiv.Perm (Fin (3 * ell))) ×
            Finset (CubicKernelLoopEdge K.graph)) :=
      Nat.card_le_card_of_injective (D.reconstructionFibreCode K)
        (D.reconstructionFibreCode_injective K)
    _ = (2 * ell).factorial * (3 * ell).factorial *
        2 ^ Fintype.card (CubicKernelLoopEdge K.graph) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_prod,
        Fintype.card_prod, Fintype.card_perm, Fintype.card_perm,
        Fintype.card_finset]
      simp only [Fintype.card_fin]

end PerronWright.GraphCore
