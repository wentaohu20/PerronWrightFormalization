import PerronWright.Enumeration.VariableKernelConnectivity
import PerronWright.Enumeration.ActualCubicLengthProfile

/-!
# Canonical variable-valence kernel profile of an actual noncubic core

For a literal connected positive-surplus noncubic two-core, this file turns
the already defined canonical bounded kernel/length table into the raw
kernel and admissible length-profile structures used by variable-valence
reconstruction.  No connectivity proof for the suppressed support is
assumed here; it will be recovered after the exact graph reconstruction.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical BigOperators

set_option linter.style.haveILetI false in
/-- The canonical bounded endpoint table of an actual noncubic core has
literal multigraph degree equal to the degree of the corresponding original
branch vertex. -/
theorem noncubicCoreKernelLengthDatum_degree_eq_original
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell)
    (j : Fin (noncubicCoreKernelLengthDatum hell H).1.val) :
    (boundedKernelFiniteMultiGraph
      ⟨(noncubicCoreKernelLengthDatum hell H).1,
        (noncubicCoreKernelLengthDatum hell H).2.1,
        (noncubicCoreKernelLengthDatum hell H).2.2.1⟩).degree j =
      H.1.degree ((noncubicCoreBranchEquiv H).symm j).val := by
  classical
  let G := H.1
  let hmin := noncubicCore_minDegree_two H
  let hacyc := noncubicCore_twoGraph_isAcyclic hell H
  let B := branchingVertices G
  let E := KernelEdgeLabel G
  let eB : (B : Set (Fin q)) ≃
      Fin (noncubicCoreKernelLengthDatum hell H).1.val :=
    noncubicCoreBranchEquiv H
  let eE : E ≃
      Fin (noncubicCoreKernelLengthDatum hell H).2.1.val :=
    noncubicCoreKernelEdgeEquiv H
  let b : (B : Set (Fin q)) := eB.symm j
  letI : Fintype (twoGraph G).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype {e : Sym2 (Fin q) // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype E := by
    dsimp only [E, KernelEdgeLabel]
    infer_instance
  have hcount (e : E) :
      (Sym2.map eB
          (kernelBranchEndpoints G hmin hacyc e)).toMultiset.count j =
        (kernelEdgeEndpoints G hacyc e).toMultiset.count b.val := by
    have hm := sym2_map_injective_count
      (f := eB) eB.injective
      (kernelBranchEndpoints G hmin hacyc e) b
    rw [eB.apply_symm_apply] at hm
    calc
      _ = (kernelBranchEndpoints G hmin hacyc e).toMultiset.count b := hm
      _ = _ := kernelBranchEndpoints_count_eq_original
        G hmin hacyc e b.val b.property
  unfold boundedKernelFiniteMultiGraph PerronWright.FiniteMultiGraph.degree
  simp only [finiteMultiGraph_incidence_eq_count]
  calc
    (∑ i : Fin (noncubicCoreKernelLengthDatum hell H).2.1.val,
        ((noncubicCoreKernelLengthDatum hell H).2.2.1 i).toMultiset.count j) =
        ∑ i : Fin (noncubicCoreKernelLengthDatum hell H).2.1.val,
          (Sym2.map eB
            (kernelBranchEndpoints G hmin hacyc (eE.symm i))).toMultiset.count j := by
      rfl
    _ = ∑ e : E,
          (Sym2.map eB
            (kernelBranchEndpoints G hmin hacyc e)).toMultiset.count j := by
      exact Fintype.sum_equiv eE.symm _ _ (by intro i; simp)
    _ = ∑ e : E,
          (kernelEdgeEndpoints G hacyc e).toMultiset.count b.val := by
      apply Finset.sum_congr rfl
      intro e _
      exact hcount e
    _ = kernelEndpointValence G hacyc b.val := by
      exact (kernelEndpointValence_eq_sum_edgeLabels G hacyc b.val).symm
    _ = G.degree b.val := by
      exact kernelEndpointValence_eq_original_degree
        G hmin hacyc b.val b.property

/-- The raw bounded kernel associated with one actual noncubic core. -/
def noncubicCoreBoundedKernel
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell) :
    LabelledBoundedKernel ell where
  shape :=
    ⟨(noncubicCoreKernelLengthDatum hell H).1,
      (noncubicCoreKernelLengthDatum hell H).2.1,
      (noncubicCoreKernelLengthDatum hell H).2.2.1⟩
  minDegree := by
    intro j
    rw [noncubicCoreKernelLengthDatum_degree_eq_original hell H j]
    let b := (noncubicCoreBranchEquiv H).symm j
    have htwo := noncubicCore_minDegree_two H b.val
    have hne : H.1.degree b.val ≠ 2 :=
      (mem_branchingVertices_iff_degree_ne_two H.1
        (noncubicCore_minDegree_two H) b.val).mp b.property
    change 3 ≤ H.1.degree b.val
    omega
  excess := by
    change Nat.card (KernelEdgeLabel H.1) =
      (branchingVertices H.1).card + ell
    exact kernelEdgeLabel_card_eq_branching_add_surplus
      H.1 H.2.1.1 (noncubicCore_minDegree_two H) hell
        (noncubicCore_edgeCount H)

@[simp] theorem noncubicCoreBoundedKernel_shape
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell) :
    (noncubicCoreBoundedKernel hell H).shape =
      ⟨(noncubicCoreKernelLengthDatum hell H).1,
        (noncubicCoreKernelLengthDatum hell H).2.1,
        (noncubicCoreKernelLengthDatum hell H).2.2.1⟩ := rfl

set_option linter.style.haveILetI false in
/-- The intrinsic lengths of an actual noncubic core satisfy exactly the
admissibility conditions of variable-valence subdivision. -/
def noncubicCoreBoundedLengthProfile
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell) :
    BoundedKernelLengthProfile q (noncubicCoreBoundedKernel hell H) := by
  classical
  let G := H.1
  let hmin := noncubicCore_minDegree_two H
  let hacyc := noncubicCore_twoGraph_isAcyclic hell H
  let B := branchingVertices G
  let E := KernelEdgeLabel G
  have hb : B.card ≤ 2 * ell :=
    branchingVertices_card_le_two_surplus G hmin
      (noncubicCore_edgeCount H)
  have he : Nat.card E ≤ 3 * ell :=
    kernelEdgeLabel_card_le_three_surplus G H.2.1.1 hmin hell
      (noncubicCore_edgeCount H)
  let nv : Fin (2 * ell + 1) := ⟨B.card, by omega⟩
  let ne : Fin (3 * ell + 1) := ⟨Nat.card E, by omega⟩
  let eB : (B : Set (Fin q)) ≃ Fin nv.val := noncubicCoreBranchEquiv H
  let eE : E ≃ Fin ne.val := noncubicCoreKernelEdgeEquiv H
  letI : Fintype (twoGraph G).ConnectedComponent := Fintype.ofFinite _
  letI : ∀ C : (twoGraph G).ConnectedComponent, Fintype C :=
    fun C ↦ Fintype.ofFinite C
  letI : Fintype {e : Sym2 (Fin q) // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype E := by
    dsimp only [E, KernelEdgeLabel]
    infer_instance
  let length : Fin ne.val → Fin (q + 1) := fun j ↦
    ⟨noncubicCoreKernelEdgeLengthNat H (eE.symm j),
      Nat.lt_succ_of_le
        (noncubicCoreKernelEdgeLengthNat_le H (eE.symm j))⟩
  have hend (e : E) :
      Sym2.map eB (kernelBranchEndpoints G hmin hacyc e) =
        (noncubicCoreKernelLengthDatum hell H).2.2.1 (eE e) := by
    change Sym2.map eB (kernelBranchEndpoints G hmin hacyc e) =
      Sym2.map eB
        (kernelBranchEndpoints G hmin hacyc (eE.symm (eE e)))
    rw [eE.symm_apply_apply]
  have hbranchCard : Fintype.card (coreBranchIndex G) = B.card := by
    calc
      Fintype.card (coreBranchIndex G) =
          Fintype.card (B : Set (Fin q)) :=
        Fintype.card_congr (coreBranchEquivBranching G hmin)
      _ = B.card := Fintype.card_coe B
  have hcoordinateCard := Fintype.card_congr (coreCoordinateEquiv G)
  simp only [Fintype.card_sum, Fintype.card_sigma] at hcoordinateCard
  have hcomponentTotal :
      B.card +
        ∑ C : (twoGraph G).ConnectedComponent, Fintype.card C = q := by
    rw [← hbranchCard]
    simpa only [Fintype.card_fin] using hcoordinateCard
  have hlengthSum :
      (∑ j : Fin ne.val, (length j).val) =
        ∑ C : (twoGraph G).ConnectedComponent, Fintype.card C := by
    calc
      (∑ j : Fin ne.val, (length j).val) =
          ∑ e : E, noncubicCoreKernelEdgeLengthNat H e := by
        exact Fintype.sum_equiv eE.symm _ _ (by
          intro j
          simp [length])
      _ = ∑ C : (twoGraph G).ConnectedComponent, Fintype.card C := by
        let edgeLength : E → ℕ :=
          fun e ↦ noncubicCoreKernelEdgeLengthNat H e
        have hsplit :
            (∑ e : E, edgeLength e) =
              (∑ C : (twoGraph G).ConnectedComponent,
                edgeLength (Sum.inl C : KernelEdgeLabel G)) +
              ∑ d : {a : Sym2 (Fin q) // a ∈ directBranchEdges G},
                edgeLength (Sum.inr d : KernelEdgeLabel G) := by
          change
            (∑ e : (twoGraph G).ConnectedComponent ⊕
                {d : Sym2 (Fin q) // d ∈ directBranchEdges G},
              edgeLength e) = _
          exact Fintype.sum_sum_type edgeLength
        change (∑ e : E, edgeLength e) = _
        rw [hsplit]
        simp only [edgeLength, noncubicCoreKernelEdgeLengthNat,
          Finset.sum_const_zero, add_zero]
        apply Finset.sum_congr rfl
        intro C _
        exact Nat.card_eq_fintype_card
  exact {
    length := length
    totalLength := by
      change B.card +
        (∑ j : Fin ne.val, (length j).val) = q
      rw [hlengthSum]
      exact hcomponentTotal
    loopLength := by
      intro j hj
      let e : E := eE.symm j
      have hej : eE e = j := eE.apply_symm_apply j
      have hmapped :
          (Sym2.map eB
            (kernelBranchEndpoints G hmin hacyc e)).IsDiag := by
        rw [hend e, hej]
        exact hj
      have hbranchDiag :
          (kernelBranchEndpoints G hmin hacyc e).IsDiag :=
        (Sym2.isDiag_map eB.injective).mp hmapped
      have hactualDiag : (kernelEdgeEndpoints G hacyc e).IsDiag := by
        rw [← kernelBranchEndpoints_map_val G hmin hacyc e]
        exact hbranchDiag.map
      rcases he : eE.symm j with C | d
      · have hlen : (length j).val = Fintype.card C := by
          change noncubicCoreKernelEdgeLengthNat H (eE.symm j) = _
          rw [he]
          exact Nat.card_eq_fintype_card
        rw [hlen]
        have hdiagC : (degreeTwoPathEndpoints G hacyc C).IsDiag := by
          change (kernelEdgeEndpoints G hacyc (eE.symm j)).IsDiag at hactualDiag
          rw [he] at hactualDiag
          exact hactualDiag
        exact degreeTwoComponent_card_ge_two_of_endpoints_isDiag
          G hacyc C hdiagC
      · exfalso
        have hdiagD : d.val.IsDiag := by
          change (kernelEdgeEndpoints G hacyc (eE.symm j)).IsDiag at hactualDiag
          rw [he] at hactualDiag
          exact hactualDiag
        apply G.not_isDiag_of_mem_edgeFinset
          (directBranchEdges_subset_edgeFinset G d.property)
        exact hdiagD
    directEndpointsInjective := by
      change Function.Injective
        (fun a : {j : Fin ne.val // (length j).val = 0} ↦
          Sym2.map eB
            (kernelBranchEndpoints G hmin hacyc (eE.symm a.1)))
      intro a b hab
      have ha0 : noncubicCoreKernelEdgeLengthNat H (eE.symm a.1) = 0 := by
        simpa [length] using a.2
      have hb0 : noncubicCoreKernelEdgeLengthNat H (eE.symm b.1) = 0 := by
        simpa [length] using b.2
      rcases hea : eE.symm a.1 with C | d
      · have hpos : 0 < Fintype.card C :=
          Fintype.card_pos_iff.mpr
            ⟨⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩⟩
        have hzero : Fintype.card C = 0 := by
          simpa [noncubicCoreKernelEdgeLengthNat, hea,
            Nat.card_eq_fintype_card] using ha0
        omega
      · rcases heb : eE.symm b.1 with C | f
        · have hpos : 0 < Fintype.card C :=
            Fintype.card_pos_iff.mpr
              ⟨⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩⟩
          have hzero : Fintype.card C = 0 := by
            simpa [noncubicCoreKernelEdgeLengthNat, heb,
              Nat.card_eq_fintype_card] using hb0
          omega
        · have hmapped :
              Sym2.map eB
                  (kernelBranchEndpoints G hmin hacyc (Sum.inr d : E)) =
                Sym2.map eB
                  (kernelBranchEndpoints G hmin hacyc (Sum.inr f : E)) := by
            simpa only [hea, heb] using hab
          have hbranch := Sym2.map.injective eB.injective hmapped
          have hmapD := kernelBranchEndpoints_map_val
            G hmin hacyc (Sum.inr d : E)
          have hmapF := kernelBranchEndpoints_map_val
            G hmin hacyc (Sum.inr f : E)
          have hactual :
              kernelEdgeEndpoints G hacyc (Sum.inr d : E) =
                kernelEdgeEndpoints G hacyc (Sum.inr f : E) := by
            calc
              kernelEdgeEndpoints G hacyc (Sum.inr d : E) =
                  Sym2.map Subtype.val
                    (kernelBranchEndpoints G hmin hacyc (Sum.inr d : E)) :=
                hmapD.symm
              _ = Sym2.map Subtype.val
                    (kernelBranchEndpoints G hmin hacyc (Sum.inr f : E)) :=
                congrArg (Sym2.map Subtype.val) hbranch
              _ = kernelEdgeEndpoints G hacyc (Sum.inr f : E) := hmapF
          have hval : d.val = f.val := by
            simpa only [kernelEdgeEndpoints] using hactual
          have hdf : d = f := Subtype.ext hval
          apply Subtype.ext
          apply eE.symm.injective
          rw [hea, heb, hdf]
  }

@[simp] theorem noncubicCoreBoundedLengthProfile_length
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell)
    (j : Fin (noncubicCoreBoundedKernel hell H).shape.2.1.val) :
    ((noncubicCoreBoundedLengthProfile hell H).length j).val =
      ((noncubicCoreKernelLengthDatum hell H).2.2.2 j).val := by
  rfl

end PerronWright.GraphCore
