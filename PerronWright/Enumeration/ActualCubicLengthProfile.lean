import PerronWright.Enumeration.CubicKernelSubdivision
import PerronWright.Enumeration.KernelGraphWeight

/-!
# Actual cubic cores give admissible subdivision-length profiles

This module constructs the length profile carried by the canonical
normalized cubic kernel of an actual finite simple two-core.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- A degree-two component whose two suppressed endpoints coincide contains
at least two original vertices.  For a singleton component, its two distinct
boundary stubs would otherwise be the same sigma pair. -/
theorem degreeTwoComponent_card_ge_two_of_endpoints_isDiag
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (twoGraph G).IsAcyclic)
    (C : (twoGraph G).ConnectedComponent) [Fintype C]
    (hdiag : (degreeTwoPathEndpoints G hacyc C).IsDiag) :
    2 ≤ Fintype.card C := by
  obtain ⟨n, hn, order, qL, qR, hne, _hleft, _hright⟩ :=
    exists_componentPathOrder_with_boundaryStubs G hacyc C
  have hend :=
    degreeTwoPathEndpoints_eq_boundaryStubPair G hacyc C qL qR hne
  rw [hend, Sym2.mk_isDiag_iff] at hdiag
  by_contra hcard
  have hle : Fintype.card C ≤ 1 := by omega
  have hfirst : qL.val.1 = qR.val.1 :=
    (Fintype.card_le_one_iff.mp hle) qL.val.1 qR.val.1
  apply hne
  apply Subtype.ext
  apply Sigma.ext hfirst
  exact heq_of_eq hdiag

set_option linter.style.haveILetI false in
/-- The normalized cubic endpoint table of an actual cubic core carries the
literal admissible length profile: a degree-two component has length its
cardinality and a direct branch edge has length zero.  The returned endpoint
and length identities retain the concrete relabellings needed by the later
inverse classification. -/
theorem exists_actual_cubic_kernel_length_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell)
    (hcubic : ∀ v ∈ branchingVertices G, G.degree v = 3) :
    ∃ (eB : (branchingVertices G : Set V) ≃ Fin (2 * ell))
      (eE : KernelEdgeLabel G ≃ Fin (3 * ell))
      (L : CubicKernelLengthProfile (Fintype.card V) ell
        (normalizedCubicFiniteMultiGraph
          G hconn hmin hell hs hcubic)),
      (∀ e : KernelEdgeLabel G,
        (normalizedCubicFiniteMultiGraph
          G hconn hmin hell hs hcubic).endpoints (eE e) =
          Sym2.map eB
            (kernelBranchEndpoints G hmin
              (degreeTwo_induced_isAcyclic G hconn hmin hell hs) e)) ∧
      (∀ C : (twoGraph G).ConnectedComponent,
        (L.length (eE (Sum.inl C))).val = Fintype.card C) ∧
      (∀ d : {e : Sym2 V // e ∈ directBranchEdges G},
        (L.length (eE (Sum.inr d))).val = 0) := by
  classical
  let hacyc : (twoGraph G).IsAcyclic :=
    degreeTwo_induced_isAcyclic G hconn hmin hell hs
  letI : Fintype (twoGraph G).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype {e : Sym2 V // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype (KernelEdgeLabel G) := by
    dsimp only [KernelEdgeLabel]
    infer_instance
  obtain ⟨eB, eE, hend⟩ :=
    exists_exact_cubic_kernel_relabeling
      G hconn hmin hell hs hcubic
  let edgeLength : KernelEdgeLabel G → ℕ
    | Sum.inl C => Fintype.card C
    | Sum.inr _ => 0
  have hedgeLength_le (e : KernelEdgeLabel G) :
      edgeLength e ≤ Fintype.card V := by
    cases e with
    | inl C =>
        exact Fintype.card_le_of_injective
          (fun x : C => x.val.val)
          (fun x y hxy => Subtype.ext (Subtype.ext hxy))
    | inr d =>
        simp only [edgeLength]
        exact Nat.zero_le _
  let length : Fin (3 * ell) → Fin (Fintype.card V + 1) := fun j =>
    ⟨edgeLength (eE.symm j),
      Nat.lt_succ_of_le (hedgeLength_le (eE.symm j))⟩

  have hbranchCard : Fintype.card (coreBranchIndex G) = 2 * ell := by
    calc
      Fintype.card (coreBranchIndex G) =
          Fintype.card (branchingVertices G : Set V) :=
        Fintype.card_congr (coreBranchEquivBranching G hmin)
      _ = Fintype.card (Fin (2 * ell)) := Fintype.card_congr eB
      _ = 2 * ell := Fintype.card_fin _
  have hcoordinateCard := Fintype.card_congr (coreCoordinateEquiv G)
  simp only [Fintype.card_sum, Fintype.card_sigma] at hcoordinateCard
  have hcomponentTotal :
      2 * ell +
        ∑ C : (twoGraph G).ConnectedComponent, Fintype.card C =
          Fintype.card V := by
    rw [← hbranchCard]
    exact hcoordinateCard
  have hlengthSum :
      (∑ j : Fin (3 * ell), (length j).val) =
        ∑ C : (twoGraph G).ConnectedComponent, Fintype.card C := by
    calc
      (∑ j : Fin (3 * ell), (length j).val) =
          ∑ e : KernelEdgeLabel G, edgeLength e := by
        exact Fintype.sum_equiv eE.symm _ _ (by
          intro j
          simp [length])
      _ = ∑ C : (twoGraph G).ConnectedComponent, Fintype.card C := by
        change
          (∑ e : (twoGraph G).ConnectedComponent ⊕
              {d : Sym2 V // d ∈ directBranchEdges G}, edgeLength e) = _
        rw [Fintype.sum_sum_type]
        simp

  let L : CubicKernelLengthProfile (Fintype.card V) ell
      (normalizedCubicFiniteMultiGraph
        G hconn hmin hell hs hcubic) := {
    length := length
    totalLength := by
      rw [hlengthSum]
      exact hcomponentTotal
    loopLength := by
      intro j hj
      let e : KernelEdgeLabel G := eE.symm j
      have hej : eE e = j := eE.apply_symm_apply j
      have hmapped :
          (Sym2.map eB
            (kernelBranchEndpoints G hmin hacyc e)).IsDiag := by
        rw [← hend e, hej]
        exact hj
      have hbranchDiag :
          (kernelBranchEndpoints G hmin hacyc e).IsDiag :=
        (Sym2.isDiag_map eB.injective).mp hmapped
      have hactualDiag : (kernelEdgeEndpoints G hacyc e).IsDiag := by
        rw [← kernelBranchEndpoints_map_val G hmin hacyc e]
        exact hbranchDiag.map
      rcases he : eE.symm j with C | d
      · have hlen : (length j).val = Fintype.card C := by
          simp [length, edgeLength, he]
        rw [hlen]
        have hdiagC :
            (degreeTwoPathEndpoints G hacyc C).IsDiag := by
          have h := hactualDiag
          change (kernelEdgeEndpoints G hacyc (eE.symm j)).IsDiag at h
          rw [he] at h
          exact h
        apply degreeTwoComponent_card_ge_two_of_endpoints_isDiag G hacyc C
        exact hdiagC
      · exfalso
        have hdiagD : d.val.IsDiag := by
          have h := hactualDiag
          change (kernelEdgeEndpoints G hacyc (eE.symm j)).IsDiag at h
          rw [he] at h
          exact h
        apply G.not_isDiag_of_mem_edgeFinset
          (directBranchEdges_subset_edgeFinset G d.property)
        exact hdiagD
    directEndpointsInjective := by
      intro a b hab
      have ha0 : edgeLength (eE.symm a.1) = 0 := by
        simpa [length] using a.2
      have hb0 : edgeLength (eE.symm b.1) = 0 := by
        simpa [length] using b.2
      rcases hea : eE.symm a.1 with C | d
      · have hpos : 0 < Fintype.card C :=
          Fintype.card_pos_iff.mpr
            ⟨⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩⟩
        have hzero : Fintype.card C = 0 := by
          simpa [edgeLength, hea] using ha0
        omega
      · rcases heb : eE.symm b.1 with C | f
        · have hpos : 0 < Fintype.card C :=
            Fintype.card_pos_iff.mpr
              ⟨⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩⟩
          have hzero : Fintype.card C = 0 := by
            simpa [edgeLength, heb] using hb0
          omega
        · have hea' : eE (Sum.inr d : KernelEdgeLabel G) = a.1 := by
            calc
              eE (Sum.inr d : KernelEdgeLabel G) =
                  eE (eE.symm a.1) := by rw [hea]
              _ = a.1 := eE.apply_symm_apply a.1
          have heb' : eE (Sum.inr f : KernelEdgeLabel G) = b.1 := by
            calc
              eE (Sum.inr f : KernelEdgeLabel G) =
                  eE (eE.symm b.1) := by rw [heb]
              _ = b.1 := eE.apply_symm_apply b.1
          have hmapped :
              Sym2.map eB
                  (kernelBranchEndpoints G hmin hacyc
                    (Sum.inr d : KernelEdgeLabel G)) =
                Sym2.map eB
                  (kernelBranchEndpoints G hmin hacyc
                    (Sum.inr f : KernelEdgeLabel G)) := by
            rw [← hend (Sum.inr d), ← hend (Sum.inr f), hea', heb']
            exact hab
          have hbranch := Sym2.map.injective eB.injective hmapped
          have hmapD := kernelBranchEndpoints_map_val G hmin hacyc
            (Sum.inr d : KernelEdgeLabel G)
          have hmapF := kernelBranchEndpoints_map_val G hmin hacyc
            (Sum.inr f : KernelEdgeLabel G)
          have hactual :
              kernelEdgeEndpoints G hacyc
                  (Sum.inr d : KernelEdgeLabel G) =
                kernelEdgeEndpoints G hacyc
                  (Sum.inr f : KernelEdgeLabel G) := by
            calc
              kernelEdgeEndpoints G hacyc
                  (Sum.inr d : KernelEdgeLabel G) =
                  Sym2.map Subtype.val
                    (kernelBranchEndpoints G hmin hacyc
                      (Sum.inr d : KernelEdgeLabel G)) := hmapD.symm
              _ = Sym2.map Subtype.val
                    (kernelBranchEndpoints G hmin hacyc
                      (Sum.inr f : KernelEdgeLabel G)) :=
                congrArg (Sym2.map Subtype.val) hbranch
              _ = kernelEdgeEndpoints G hacyc
                    (Sum.inr f : KernelEdgeLabel G) := hmapF
          have hval : d.val = f.val := by
            simpa only [kernelEdgeEndpoints] using hactual
          have hdf : d = f := Subtype.ext hval
          apply Subtype.ext
          apply eE.symm.injective
          rw [hea, heb, hdf]
    }
  refine ⟨eB, eE, L, hend, ?_, ?_⟩
  · intro C
    change edgeLength
      (eE.symm (eE (Sum.inl C : KernelEdgeLabel G))) = Fintype.card C
    exact (congrArg edgeLength
      (eE.symm_apply_apply (Sum.inl C : KernelEdgeLabel G))).trans rfl
  · intro d
    change edgeLength
      (eE.symm (eE (Sum.inr d : KernelEdgeLabel G))) = 0
    exact (congrArg edgeLength
      (eE.symm_apply_apply (Sum.inr d : KernelEdgeLabel G))).trans rfl

end PerronWright.GraphCore
