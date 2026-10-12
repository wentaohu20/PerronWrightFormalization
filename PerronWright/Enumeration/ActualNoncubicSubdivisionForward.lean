import PerronWright.Enumeration.ActualNoncubicKernelProfile
import PerronWright.Enumeration.MarkedCoreFactorization
import PerronWright.Enumeration.PathGraphAutomorphismRigidity

/-!
# Exact reconstruction of an actual noncubic core

The canonical variable-valence kernel profile of an actual noncubic core is
equipped here with one global labelling equivalence.  Compatible Hamilton
orders on the degree-two components identify every emitted subdivision edge
with an original graph edge.  Equality of edge counts then gives literal
equality of the reconstructed and original labelled simple graphs.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Orient the Hamilton order of an actual degree-two component so that its
boundary stubs agree with the canonical ordered endpoints of the bounded
kernel edge. -/
theorem exists_oriented_bounded_componentPathOrder
    {q ell : ℕ}
    (G : SimpleGraph (Fin q)) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (twoGraph G).IsAcyclic)
    (K : LabelledBoundedKernel ell)
    (eB : (branchingVertices G : Set (Fin q)) ≃ Fin K.shape.1.val)
    (eE : KernelEdgeLabel G ≃ Fin K.shape.2.1.val)
    (hend : ∀ e : KernelEdgeLabel G,
      K.shape.2.2 (eE e) =
        Sym2.map eB (kernelBranchEndpoints G hmin hacyc e))
    (C : (twoGraph G).ConnectedComponent) :
    ∃ n : ℕ, Fintype.card C = n + 1 ∧
      ∃ e : SimpleGraph.pathGraph (n + 1) ≃g C.toSimpleGraph,
      ∃ q₀ q₁ : {q // q ∈ componentBoundaryStubs G C},
        q₀ ≠ q₁ ∧ e 0 = q₀.val.1 ∧ e (Fin.last n) = q₁.val.1 ∧
        eB.symm
            (boundedKernelOrderedEndpoints K.shape
              (eE (Sum.inl C : KernelEdgeLabel G))).1 =
          coreBranchEquivBranching G hmin
            (componentBoundaryStubBranchIndex G C q₀) ∧
        eB.symm
            (boundedKernelOrderedEndpoints K.shape
              (eE (Sum.inl C : KernelEdgeLabel G))).2 =
          coreBranchEquivBranching G hmin
            (componentBoundaryStubBranchIndex G C q₁) := by
  classical
  obtain ⟨n, hn, e, qL, qR, hne, hleft, hright⟩ :=
    exists_componentPathOrder_with_boundaryStubs G hacyc C
  let bL : (branchingVertices G : Set (Fin q)) :=
    coreBranchEquivBranching G hmin
      (componentBoundaryStubBranchIndex G C qL)
  let bR : (branchingVertices G : Set (Fin q)) :=
    coreBranchEquivBranching G hmin
      (componentBoundaryStubBranchIndex G C qR)
  let j : Fin K.shape.2.1.val := eE (Sum.inl C : KernelEdgeLabel G)
  let o := boundedKernelOrderedEndpoints K.shape j
  have hpair : s(o.1, o.2) = s(eB bL, eB bR) := by
    calc
      s(o.1, o.2) = K.shape.2.2 j := boundedKernelOrderedEndpoints_mk K j
      _ = Sym2.map eB
          (kernelBranchEndpoints G hmin hacyc
            (Sum.inl C : KernelEdgeLabel G)) :=
        hend (Sum.inl C : KernelEdgeLabel G)
      _ = Sym2.map eB s(bL, bR) := by
        rw [kernelBranchEndpoints_eq_boundaryStubBranchPair
          G hmin hacyc C qL qR hne]
      _ = s(eB bL, eB bR) := by rw [Sym2.map_mk]
  rcases Sym2.eq_iff.mp hpair with hdir | hswap
  · refine ⟨n, hn, e, qL, qR, hne, hleft, hright, ?_, ?_⟩
    · apply eB.injective
      simpa [o, j, bL] using hdir.1
    · apply eB.injective
      simpa [o, j, bR] using hdir.2
  · let er : SimpleGraph.pathGraph (n + 1) ≃g C.toSimpleGraph :=
      (pathGraphRevIso (n + 1)).trans e
    refine ⟨n, hn, er, qR, qL, hne.symm, ?_, ?_, ?_, ?_⟩
    · change e ((pathGraphRevIso (n + 1)) 0) = qR.val.1
      have hrev : (pathGraphRevIso (n + 1)) 0 = Fin.last n := by
        exact Fin.rev_zero n
      rw [hrev, hright]
    · change e ((pathGraphRevIso (n + 1)) (Fin.last n)) = qL.val.1
      have hrev : (pathGraphRevIso (n + 1)) (Fin.last n) = 0 := by
        exact Fin.rev_last n
      rw [hrev, hleft]
    · apply eB.injective
      simpa [o, j, bR] using hswap.1
    · apply eB.injective
      simpa [o, j, bL] using hswap.2

set_option linter.style.haveILetI false in
/-- Every actual noncubic admissible core is literally reconstructed from
its canonical bounded kernel and intrinsic length profile. -/
theorem exists_actual_noncubic_subdivision_labels
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell) :
    let K := noncubicCoreBoundedKernel hell H
    let L := noncubicCoreBoundedLengthProfile hell H
    ∃ labels : BoundedKernelSubdivisionSlot L ≃ Fin q,
      (({ profile := L, labels := labels } :
          BoundedKernelSubdivisionDatum q K).reconstructedGraph = H.1) := by
  classical
  dsimp only
  let G := H.1
  let hconn : G.Connected := H.2.1.1
  let hmin : ∀ v, 2 ≤ G.degree v := noncubicCore_minDegree_two H
  let hacyc : (twoGraph G).IsAcyclic :=
    noncubicCore_twoGraph_isAcyclic hell H
  let K := noncubicCoreBoundedKernel hell H
  let L := noncubicCoreBoundedLengthProfile hell H
  let eB : (branchingVertices G : Set (Fin q)) ≃ Fin K.shape.1.val :=
    noncubicCoreBranchEquiv H
  let eE : KernelEdgeLabel G ≃ Fin K.shape.2.1.val :=
    noncubicCoreKernelEdgeEquiv H
  letI : Fintype (twoGraph G).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype {e : Sym2 (Fin q) // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype (KernelEdgeLabel G) := by
    dsimp only [KernelEdgeLabel]
    infer_instance
  have hend (e : KernelEdgeLabel G) :
      K.shape.2.2 (eE e) =
        Sym2.map eB (kernelBranchEndpoints G hmin hacyc e) := by
    change Sym2.map eB
        (kernelBranchEndpoints G hmin hacyc (eE.symm (eE e))) = _
    rw [eE.symm_apply_apply]
  have hcomponentLength (C : (twoGraph G).ConnectedComponent) :
      (L.length (eE (Sum.inl C))).val = Fintype.card C := by
    let z : KernelEdgeLabel G := Sum.inl C
    change noncubicCoreKernelEdgeLengthNat H
      (eE.symm (eE z)) = _
    rw [eE.symm_apply_apply z]
    change Nat.card C = Fintype.card C
    exact Nat.card_eq_fintype_card
  have hdirectLength
      (d : {e : Sym2 (Fin q) // e ∈ directBranchEdges G}) :
      (L.length (eE (Sum.inr d))).val = 0 := by
    let z : KernelEdgeLabel G := Sum.inr d
    change noncubicCoreKernelEdgeLengthNat H
      (eE.symm (eE z)) = 0
    rw [eE.symm_apply_apply z]
    change 0 = 0
    rfl
  have hchoice := fun C : (twoGraph G).ConnectedComponent ↦
    exists_oriented_bounded_componentPathOrder
      G hmin hacyc K eB eE hend C
  choose n hn order qL qR hstub_ne hleft hright
    hbranchLeft hbranchRight using hchoice

  let internalReindex :
      (Σ j : Fin K.shape.2.1.val, Fin (L.length j).val) ≃
        Σ z : ((twoGraph G).ConnectedComponent ⊕
          {e : Sym2 (Fin q) // e ∈ directBranchEdges G}),
          Fin (L.length (eE z)).val :=
    Equiv.sigmaCongrLeft' eE.symm
  let kernelInternalSlot :
      (Σ z : ((twoGraph G).ConnectedComponent ⊕
          {e : Sym2 (Fin q) // e ∈ directBranchEdges G}),
          Fin (L.length (eE z)).val) →
        Σ C : (twoGraph G).ConnectedComponent, C
    | ⟨.inl C, i⟩ =>
        ⟨C, order C (Fin.cast ((hcomponentLength C).trans (hn C)) i)⟩
    | ⟨.inr d, i⟩ => Fin.elim0 (Fin.cast (hdirectLength d) i)
  have kernelInternalSlot_injective :
      Function.Injective kernelInternalSlot := by
    rintro ⟨z, i⟩ ⟨z', i'⟩ hp
    rcases z with C | d
    · rcases z' with C' | d'
      · change
          (⟨C, order C
              (Fin.cast ((hcomponentLength C).trans (hn C)) i)⟩ :
              Σ A : (twoGraph G).ConnectedComponent, A) =
            ⟨C', order C'
              (Fin.cast ((hcomponentLength C').trans (hn C')) i')⟩ at hp
        have hC : C = C' := congrArg Sigma.fst hp
        subst C'
        have hvertex := eq_of_heq (Sigma.mk.inj_iff.mp hp).2
        have hindex := (order C).injective hvertex
        apply Sigma.ext
        · rfl
        · apply heq_of_eq
          apply Fin.ext
          simpa using congrArg Fin.val hindex
      · exact Fin.elim0 (Fin.cast (hdirectLength d') i')
    · exact Fin.elim0 (Fin.cast (hdirectLength d) i)
  let internalSlot := kernelInternalSlot ∘ internalReindex
  have internalSlot_injective : Function.Injective internalSlot := by
    intro p p' hp
    apply internalReindex.injective
    exact kernelInternalSlot_injective hp

  let slotLabel : BoundedKernelSubdivisionSlot L → Fin q
    | .inl u => (eB.symm u).val
    | .inr p => (internalSlot p).2.val.val
  have slotLabel_injective : Function.Injective slotLabel := by
    intro z z' hzz'
    rcases z with u | p
    · rcases z' with u' | p'
      · have huu : u = u' := by
          apply eB.symm.injective
          apply Subtype.ext
          exact hzz'
        exact congrArg
          (fun x : Fin K.shape.1.val ↦
            (Sum.inl x : BoundedKernelSubdivisionSlot L)) huu
      · exfalso
        have hbranchNe : G.degree (eB.symm u).val ≠ 2 :=
          (mem_branchingVertices_iff_degree_ne_two G hmin _).mp
            (eB.symm u).property
        have hinternal : G.degree ((internalSlot p').2.val.val) = 2 :=
          (internalSlot p').2.val.property
        change (eB.symm u).val = (internalSlot p').2.val.val at hzz'
        rw [hzz', hinternal] at hbranchNe
        exact hbranchNe rfl
    · rcases z' with u' | p'
      · exfalso
        have hbranchNe : G.degree (eB.symm u').val ≠ 2 :=
          (mem_branchingVertices_iff_degree_ne_two G hmin _).mp
            (eB.symm u').property
        have hinternal : G.degree ((internalSlot p).2.val.val) = 2 :=
          (internalSlot p).2.val.property
        change (internalSlot p).2.val.val = (eB.symm u').val at hzz'
        rw [← hzz', hinternal] at hbranchNe
        exact hbranchNe rfl
      · have hpp : p = p' := by
          apply internalSlot_injective
          change (internalSlot p).2.val.val =
            (internalSlot p').2.val.val at hzz'
          rcases hx : internalSlot p with ⟨C, x⟩
          rcases hy : internalSlot p' with ⟨C', y⟩
          rw [hx, hy] at hzz'
          change x.val.val = y.val.val at hzz'
          have hval : x.val = y.val := Subtype.ext hzz'
          have hcomponent : C = C' :=
            SimpleGraph.ConnectedComponent.eq_of_common_vertex
              x.property (hval.symm ▸ y.property)
          subst C'
          have hxy : x = y := Subtype.ext hval
          subst y
          rfl
        exact congrArg
          (fun x : Σ j : Fin K.shape.2.1.val, Fin (L.length j).val ↦
            (Sum.inr x : BoundedKernelSubdivisionSlot L)) hpp
  have slotLabel_bijective : Function.Bijective slotLabel :=
    (Fintype.bijective_iff_injective_and_card slotLabel).mpr
      ⟨slotLabel_injective, by
        rw [boundedKernelSubdivisionSlot_card L, Fintype.card_fin]⟩
  let labels : BoundedKernelSubdivisionSlot L ≃ Fin q :=
    Equiv.ofBijective slotLabel slotLabel_bijective
  let D : BoundedKernelSubdivisionDatum q K :=
    { profile := L, labels := labels }
  have labels_component
      (C : (twoGraph G).ConnectedComponent)
      (i : Fin (L.length (eE (Sum.inl C))).val) :
      labels (.inr ⟨eE (Sum.inl C), i⟩) =
        (order C
          (Fin.cast ((hcomponentLength C).trans (hn C)) i)).val.val := by
    change slotLabel (.inr ⟨eE (Sum.inl C), i⟩) = _
    have hreindex :
        internalReindex ⟨eE (Sum.inl C), i⟩ = ⟨Sum.inl C, i⟩ := by
      change internalReindex
          (internalReindex.symm ⟨Sum.inl C, i⟩) = ⟨Sum.inl C, i⟩
      exact internalReindex.apply_symm_apply ⟨Sum.inl C, i⟩
    simp only [slotLabel, internalSlot, Function.comp_apply]
    rw [hreindex]

  have orderedEndpoints_original (z : KernelEdgeLabel G) :
      s((eB.symm
            (boundedKernelOrderedEndpoints K.shape (eE z)).1).val,
        (eB.symm
            (boundedKernelOrderedEndpoints K.shape (eE z)).2).val) =
        kernelEdgeEndpoints G hacyc z := by
    have hpair := (boundedKernelOrderedEndpoints_mk K (eE z)).trans (hend z)
    have hmapped := congrArg
      (Sym2.map (fun u : Fin K.shape.1.val ↦ (eB.symm u).val)) hpair
    calc
      s((eB.symm (boundedKernelOrderedEndpoints K.shape (eE z)).1).val,
          (eB.symm (boundedKernelOrderedEndpoints K.shape (eE z)).2).val) =
          Sym2.map Subtype.val
            (kernelBranchEndpoints G hmin hacyc z) := by
        simpa only [Sym2.map_mk, Sym2.map_map, Function.comp_apply,
          eB.symm_apply_apply] using hmapped
      _ = kernelEdgeEndpoints G hacyc z :=
        kernelBranchEndpoints_map_val G hmin hacyc z

  have componentStartEdge (C : (twoGraph G).ConnectedComponent) :
      s((eB.symm
            (boundedKernelOrderedEndpoints K.shape
              (eE (Sum.inl C))).1).val,
        ((order C) 0).val.val) ∈ G.edgeFinset := by
    have hq := (qL C).property
    simp only [componentBoundaryStubs, Finset.mem_sigma, Finset.mem_univ,
      true_and, Finset.mem_filter, G.mem_neighborFinset] at hq
    apply G.mem_edgeFinset.mpr
    apply G.mem_edgeSet.mpr
    have hb := congrArg Subtype.val (hbranchLeft C)
    have hx := congrArg (fun x : C ↦ x.val.val) (hleft C)
    rw [hb, hx]
    exact hq.1.symm
  have componentEndEdge (C : (twoGraph G).ConnectedComponent) :
      s(((order C) (Fin.last (n C))).val.val,
        (eB.symm
            (boundedKernelOrderedEndpoints K.shape
              (eE (Sum.inl C))).2).val) ∈ G.edgeFinset := by
    have hq := (qR C).property
    simp only [componentBoundaryStubs, Finset.mem_sigma, Finset.mem_univ,
      true_and, Finset.mem_filter, G.mem_neighborFinset] at hq
    apply G.mem_edgeFinset.mpr
    apply G.mem_edgeSet.mpr
    have hb := congrArg Subtype.val (hbranchRight C)
    have hx := congrArg (fun x : C ↦ x.val.val) (hright C)
    rw [hb, hx]
    exact hq.1
  have componentMiddleEdge
      (C : (twoGraph G).ConnectedComponent) (i : Fin (n C)) :
      s(((order C) i.castSucc).val.val,
        ((order C) i.succ).val.val) ∈ G.edgeFinset := by
    have hpath : (SimpleGraph.pathGraph (n C + 1)).Adj
        i.castSucc i.succ := by
      simp [SimpleGraph.pathGraph_adj]
    have hcomponent : C.toSimpleGraph.Adj
        ((order C) i.castSucc) ((order C) i.succ) :=
      (order C).map_rel_iff.mpr hpath
    exact G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hcomponent)

  have hEdgeDirect
      (e : Fin K.shape.2.1.val)
      (he : (D.profile.length e).val = 0) :
      D.subdivisionEdge
          (⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ :
            BoundedKernelSubdivisionEdgeSlot D) =
        s(D.branchLabel (boundedKernelOrderedEndpoints K.shape e).1,
          D.branchLabel (boundedKernelOrderedEndpoints K.shape e).2) := by
    let a : BoundedKernelSubdivisionEdgeSlot D :=
      ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩
    change D.subdivisionEdge a = _
    have hslot := D.subdivisionSlotEdge_direct e he
    change D.subdivisionSlotEdge a = _ at hslot
    calc
      D.subdivisionEdge a = Sym2.map D.labels (D.subdivisionSlotEdge a) :=
        D.subdivisionEdge_eq_map_slotEdge a
      _ = _ := by rw [hslot]; rfl

  have hEdgeStart
      (e : Fin K.shape.2.1.val)
      (he : 0 < (D.profile.length e).val) :
      D.subdivisionEdge
          (⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ :
            BoundedKernelSubdivisionEdgeSlot D) =
        s(D.branchLabel (boundedKernelOrderedEndpoints K.shape e).1,
          D.pathLabel e ⟨0, he⟩) := by
    let a : BoundedKernelSubdivisionEdgeSlot D :=
      ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩
    change D.subdivisionEdge a = _
    have hslot := D.subdivisionSlotEdge_start e he
    change D.subdivisionSlotEdge a = _ at hslot
    calc
      D.subdivisionEdge a = Sym2.map D.labels (D.subdivisionSlotEdge a) :=
        D.subdivisionEdge_eq_map_slotEdge a
      _ = _ := by rw [hslot]; rfl

  have hEdgeEnd
      (e : Fin K.shape.2.1.val)
      (he : 0 < (D.profile.length e).val) :
      D.subdivisionEdge
          (⟨e, Fin.last (D.profile.length e).val⟩ :
            BoundedKernelSubdivisionEdgeSlot D) =
        s(D.pathLabel e
            ⟨(D.profile.length e).val - 1, by omega⟩,
          D.branchLabel (boundedKernelOrderedEndpoints K.shape e).2) := by
    let a : BoundedKernelSubdivisionEdgeSlot D :=
      ⟨e, Fin.last (D.profile.length e).val⟩
    change D.subdivisionEdge a = _
    have hslot := D.subdivisionSlotEdge_end e he
    change D.subdivisionSlotEdge a = _ at hslot
    calc
      D.subdivisionEdge a = Sym2.map D.labels (D.subdivisionSlotEdge a) :=
        D.subdivisionEdge_eq_map_slotEdge a
      _ = _ := by rw [hslot]; rfl

  have hEdgeMiddle
      (e : Fin K.shape.2.1.val)
      (i : Fin ((D.profile.length e).val - 1)) :
      D.subdivisionEdge
          (D.middleEdgeSlot
            (⟨e, i⟩ : BoundedKernelSubdivisionMiddleSlot D)) =
        s(D.pathLabel e ⟨i.val, by have := i.isLt; omega⟩,
          D.pathLabel e ⟨i.val + 1, by have := i.isLt; omega⟩) := by
    rw [D.subdivisionEdge_eq_map_slotEdge,
      D.subdivisionSlotEdge_middle e i]
    rfl

  have subdivisionEdge_mem (a : BoundedKernelSubdivisionEdgeSlot D) :
      D.subdivisionEdge a ∈ G.edgeFinset := by
    rcases D.edgeSlot_classification a with
        hdirect | hstart | hendSlot | hmiddle
    · obtain ⟨e, rfl⟩ := hdirect
      rcases hz : eE.symm e.1 with C | d
      · have hj : eE (Sum.inl C) = e.1 := by
          rw [← hz, eE.apply_symm_apply]
        have hlen := hcomponentLength C
        rw [hj] at hlen
        have hcard := hn C
        have hezero : (L.length e.1).val = 0 := by simpa [D] using e.2
        omega
      · have hj : eE (Sum.inr d) = e.1 := by
          rw [← hz, eE.apply_symm_apply]
        rw [hEdgeDirect e.1 e.2, ← hj]
        change
          s((eB.symm
                (boundedKernelOrderedEndpoints K.shape
                  (eE (Sum.inr d))).1).val,
            (eB.symm
                (boundedKernelOrderedEndpoints K.shape
                  (eE (Sum.inr d))).2).val) ∈ G.edgeFinset
        rw [orderedEndpoints_original (Sum.inr d)]
        exact directBranchEdges_subset_edgeFinset G d.property
    · obtain ⟨⟨f, hf⟩, rfl⟩ := hstart
      rcases hz : eE.symm f with C | d
      · have hj : eE (Sum.inl C) = f := by
          rw [← hz, eE.apply_symm_apply]
        subst f
        rw [hEdgeStart (eE (Sum.inl C)) hf]
        change
          s((eB.symm
                (boundedKernelOrderedEndpoints K.shape
                  (eE (Sum.inl C))).1).val,
            labels (.inr ⟨eE (Sum.inl C), _⟩)) ∈ G.edgeFinset
        rw [labels_component C]
        convert componentStartEdge C using 1
        congr 2
      · have hj : eE (Sum.inr d) = f := by
          rw [← hz, eE.apply_symm_apply]
        have hzero := hdirectLength d
        rw [hj] at hzero
        have hepos : 0 < (L.length f).val := by simpa [D] using hf
        omega
    · obtain ⟨⟨f, hf⟩, rfl⟩ := hendSlot
      rcases hz : eE.symm f with C | d
      · have hj : eE (Sum.inl C) = f := by
          rw [← hz, eE.apply_symm_apply]
        subst f
        rw [hEdgeEnd (eE (Sum.inl C)) hf]
        change
          s(labels (.inr ⟨eE (Sum.inl C), _⟩),
            (eB.symm
                (boundedKernelOrderedEndpoints K.shape
                  (eE (Sum.inl C))).2).val) ∈ G.edgeFinset
        rw [labels_component C]
        convert componentEndEdge C using 1
        congr 2
        apply congrArg (fun x : C ↦ x.val)
        apply congrArg (order C)
        apply Fin.ext
        simp
        have hsize := (hcomponentLength C).trans (hn C)
        have hprofile :
            (D.profile.length (eE (Sum.inl C))).val = n C + 1 := by
          simpa [D] using hsize
        omega
      · have hj : eE (Sum.inr d) = f := by
          rw [← hz, eE.apply_symm_apply]
        have hzero := hdirectLength d
        rw [hj] at hzero
        have hepos : 0 < (L.length f).val := by simpa [D] using hf
        omega
    · obtain ⟨⟨j, i⟩, rfl⟩ := hmiddle
      rcases hz : eE.symm j with C | d
      · have hj : eE (Sum.inl C) = j := by
          rw [← hz, eE.apply_symm_apply]
        subst j
        have hsize : (L.length (eE (Sum.inl C))).val = n C + 1 :=
          (hcomponentLength C).trans (hn C)
        let iC : Fin (n C) :=
          ⟨i.val, by
            have hp := i.isLt
            simp only [D] at hp
            omega⟩
        rw [hEdgeMiddle (eE (Sum.inl C)) i]
        change
          s(labels (.inr ⟨eE (Sum.inl C), _⟩),
            labels (.inr ⟨eE (Sum.inl C), _⟩)) ∈ G.edgeFinset
        rw [labels_component C, labels_component C]
        convert componentMiddleEdge C iC using 1
        congr 2
      · have hj : eE (Sum.inr d) = j := by
          rw [← hz, eE.apply_symm_apply]
        have hzero := hdirectLength d
        have hp := i.isLt
        simp only [D] at hp
        have hzeroP : (L.length j).val = 0 := by
          rw [← hj]
          exact hzero
        omega
  have reconstructedGraph_eq : D.reconstructedGraph = G := by
    apply SimpleGraph.edgeFinset_inj.mp
    apply Finset.eq_of_subset_of_card_le
    · rw [D.reconstructedGraph_edgeFinset_eq_image]
      intro z hz
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
      exact subdivisionEdge_mem a
    · rw [D.reconstructedGraph_edgeFinset_card,
        noncubicCore_edgeCount H]
      simp only [Fintype.card_fin]
      exact le_rfl
  exact ⟨labels, by simpa [D, G] using reconstructedGraph_eq⟩

/-- The support of the canonical suppressed kernel is connected, now as a
consequence of exact reconstruction rather than a circular input. -/
theorem noncubicCoreBoundedKernel_connected
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell) :
    (finiteMultiGraphSupportGraph
      (boundedKernelFiniteMultiGraph
        (noncubicCoreBoundedKernel hell H).shape)).Connected := by
  obtain ⟨labels, hgraph⟩ := exists_actual_noncubic_subdivision_labels hell H
  let D : BoundedKernelSubdivisionDatum q
      (noncubicCoreBoundedKernel hell H) :=
    { profile := noncubicCoreBoundedLengthProfile hell H, labels := labels }
  apply D.kernelSupport_connected_of_reconstructed
  have hD : D.reconstructedGraph = H.1 := by
    simpa [D] using hgraph
  rw [hD]
  exact H.2.1.1

/-- The canonical actual noncubic kernel, now packaged in the connected
finite type used by global kernel sums. -/
def noncubicCoreConnectedBoundedKernel
    {q ell : ℕ} (hell : 0 < ell)
    (H : NoncubicAdmissibleAttachmentCore q ell) :
    LabelledConnectedBoundedKernel ell where
  toLabelledBoundedKernel := noncubicCoreBoundedKernel hell H
  connected := noncubicCoreBoundedKernel_connected hell H

end PerronWright.GraphCore
