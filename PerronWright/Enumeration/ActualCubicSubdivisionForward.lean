import PerronWright.Enumeration.ActualCubicLengthProfile
import PerronWright.Enumeration.CubicKernelSubdivisionCount
import PerronWright.Enumeration.CubicKernelReconstruction
import PerronWright.Enumeration.CubicSubdivisionSuppressionRecovery
import PerronWright.Enumeration.MarkedCoreFactorization
import PerronWright.Enumeration.PathGraphAutomorphismRigidity

/-!
# Forward subdivision data of an actual cubic core

This module assembles the global original-vertex labelling equivalence
from the normalized branch relabelling and compatible Hamilton orders on all
actual degree-two components.  The compatible endpoint orientation identifies
the reconstructed edge finset with the original graph edge finset, and hence
recovers the original labelled graph exactly.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- The actual Hamilton order on one degree-two component can be oriented so
that its two boundary stubs agree with the canonical sorted order of the
corresponding normalized kernel edge. -/
theorem exists_oriented_componentPathOrder
    {k ell : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (twoGraph G).IsAcyclic)
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (eB : (branchingVertices G : Set (Fin k)) ≃ Fin (2 * ell))
    (eE : KernelEdgeLabel G ≃ Fin (3 * ell))
    (hend : ∀ e : KernelEdgeLabel G,
      H.endpoints (eE e) =
        Sym2.map eB (kernelBranchEndpoints G hmin hacyc e))
    (C : (twoGraph G).ConnectedComponent) :
    ∃ n : ℕ, Fintype.card C = n + 1 ∧
      ∃ e : SimpleGraph.pathGraph (n + 1) ≃g C.toSimpleGraph,
      ∃ q₀ q₁ : {q // q ∈ componentBoundaryStubs G C},
        q₀ ≠ q₁ ∧ e 0 = q₀.val.1 ∧ e (Fin.last n) = q₁.val.1 ∧
        eB.symm
            (cubicKernelOrderedEndpoints H
              (eE (Sum.inl C : KernelEdgeLabel G))).1 =
          coreBranchEquivBranching G hmin
            (componentBoundaryStubBranchIndex G C q₀) ∧
        eB.symm
            (cubicKernelOrderedEndpoints H
              (eE (Sum.inl C : KernelEdgeLabel G))).2 =
          coreBranchEquivBranching G hmin
            (componentBoundaryStubBranchIndex G C q₁) := by
  classical
  obtain ⟨n, hn, e, qL, qR, hne, hleft, hright⟩ :=
    exists_componentPathOrder_with_boundaryStubs G hacyc C
  let bL : (branchingVertices G : Set (Fin k)) :=
    coreBranchEquivBranching G hmin
      (componentBoundaryStubBranchIndex G C qL)
  let bR : (branchingVertices G : Set (Fin k)) :=
    coreBranchEquivBranching G hmin
      (componentBoundaryStubBranchIndex G C qR)
  let j : Fin (3 * ell) := eE (Sum.inl C : KernelEdgeLabel G)
  let o := cubicKernelOrderedEndpoints H j
  have hpair : s(o.1, o.2) = s(eB bL, eB bR) := by
    calc
      s(o.1, o.2) = H.endpoints j := cubicKernelOrderedEndpoints_mk H j
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
/-- Every actual labelled cubic core has a normalized admissible length
profile and one global equivalence from its branch and ordered internal slots
to the original vertex labels.  Branch slots use the exact normalized branch
relabeling, while every internal slot is sent through a genuine Hamilton
order of its degree-two component. -/
theorem exists_actual_cubic_subdivision_labels
    {k ell : ℕ}
    (G : SimpleGraph (Fin k)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    (hell : 0 < ell)
    (hs : G.edgeFinset.card = k + ell)
    (hcubic : ∀ v ∈ branchingVertices G, G.degree v = 3) :
    ∃ (eB : (branchingVertices G : Set (Fin k)) ≃ Fin (2 * ell))
      (eE : KernelEdgeLabel G ≃ Fin (3 * ell))
      (L : CubicKernelLengthProfile k ell
        (normalizedCubicFiniteMultiGraph G hconn hmin hell
          (by simpa using hs) hcubic))
      (labels : CubicKernelSubdivisionSlot L ≃ Fin k),
      (∀ e : KernelEdgeLabel G,
        (normalizedCubicFiniteMultiGraph G hconn hmin hell
          (by simpa using hs) hcubic).endpoints (eE e) =
          Sym2.map eB
            (kernelBranchEndpoints G hmin
              (degreeTwo_induced_isAcyclic G hconn hmin hell
                (by simpa using hs)) e)) ∧
      (∀ C : (twoGraph G).ConnectedComponent,
        (L.length (eE (Sum.inl C))).val = Fintype.card C) ∧
      (∀ d : {e : Sym2 (Fin k) // e ∈ directBranchEdges G},
        (L.length (eE (Sum.inr d))).val = 0) ∧
      (∀ u : Fin (2 * ell),
        labels (.inl u) = (eB.symm u).val) ∧
      (∀ j : Fin (3 * ell),
        ∀ i : Fin (L.length j).val,
          G.degree (labels (.inr ⟨j, i⟩)) = 2) ∧
      (({ profile := L, labels := labels } :
          CubicKernelSubdivisionDatum k ell
            (normalizedCubicFiniteMultiGraph G hconn hmin hell
              (by simpa using hs) hcubic)).reconstructedGraph = G) := by
  classical
  let hscard : G.edgeFinset.card = Fintype.card (Fin k) + ell := by
    simpa using hs
  let hacyc : (twoGraph G).IsAcyclic :=
    degreeTwo_induced_isAcyclic G hconn hmin hell hscard
  letI : Fintype (twoGraph G).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype {e : Sym2 (Fin k) // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype (KernelEdgeLabel G) := by
    dsimp only [KernelEdgeLabel]
    infer_instance
  obtain ⟨eB, eE, Lraw, hend, hcomponentLengthRaw,
      hdirectLengthRaw⟩ :=
    exists_actual_cubic_kernel_length_profile
      G hconn hmin hell hscard hcubic
  change ((twoGraph G).ConnectedComponent ⊕
      {e : Sym2 (Fin k) // e ∈ directBranchEdges G}) ≃
        Fin (3 * ell) at eE

  /- The constructor naturally records the ambient cardinal as
  `Fintype.card (Fin k)`.  Repackage the same length function at the
  definitionally intended parameter `k`; only the total-length proof
  changes, via `Fintype.card_fin`. -/
  let L : CubicKernelLengthProfile k ell
      (normalizedCubicFiniteMultiGraph G hconn hmin hell hscard hcubic) :=
    { length := fun e => Fin.cast
          (congrArg (fun m : ℕ => m + 1) (Fintype.card_fin k))
          (Lraw.length e)
      totalLength := by simpa using Lraw.totalLength
      loopLength := by
        intro e he
        simpa using Lraw.loopLength e he
      directEndpointsInjective := by
        intro e f hef
        let eraw : {a : Fin (3 * ell) // (Lraw.length a).val = 0} :=
          ⟨e.val, by simpa using e.property⟩
        let fraw : {a : Fin (3 * ell) // (Lraw.length a).val = 0} :=
          ⟨f.val, by simpa using f.property⟩
        have heraw : eraw = fraw :=
          Lraw.directEndpointsInjective (by simpa [eraw, fraw] using hef)
        exact Subtype.ext (congrArg Subtype.val heraw) }
  have hcomponentLength
      (C : (twoGraph G).ConnectedComponent) :
      (L.length (eE (Sum.inl C))).val = Fintype.card C :=
    hcomponentLengthRaw C
  have hdirectLength
      (d : {e : Sym2 (Fin k) // e ∈ directBranchEdges G}) :
      (L.length (eE (Sum.inr d))).val = 0 :=
    hdirectLengthRaw d

  have hchoice := fun C : (twoGraph G).ConnectedComponent =>
    exists_oriented_componentPathOrder G hmin hacyc
      (normalizedCubicFiniteMultiGraph G hconn hmin hell hscard hcubic)
      eB eE hend C
  choose n hn order qL qR hstub_ne hleft hright
    hbranchLeft hbranchRight using hchoice

  /- Reindex internal fibres by the actual kernel-edge label before sending
  component fibres through their oriented Hamilton orders.  This explicit
  sigma equivalence avoids any transparency issue around `KernelEdgeLabel`.
  Direct-edge fibres are empty by their proved length zero. -/
  let internalReindex :
      (Σ j : Fin (3 * ell), Fin (L.length j).val) ≃
        Σ z : ((twoGraph G).ConnectedComponent ⊕
          {e : Sym2 (Fin k) // e ∈ directBranchEdges G}),
          Fin (L.length (eE z)).val :=
    Equiv.sigmaCongrLeft' eE.symm
  let kernelInternalSlot :
      (Σ z : ((twoGraph G).ConnectedComponent ⊕
          {e : Sym2 (Fin k) // e ∈ directBranchEdges G}),
          Fin (L.length (eE z)).val) →
        Σ C : (twoGraph G).ConnectedComponent, C
    | ⟨.inl C, i⟩ =>
        ⟨C, order C
          (Fin.cast ((hcomponentLength C).trans (hn C)) i)⟩
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
        have hvertex :
            order C
                (Fin.cast ((hcomponentLength C).trans (hn C)) i) =
              order C
                (Fin.cast ((hcomponentLength C).trans (hn C)) i') :=
          eq_of_heq (Sigma.mk.inj_iff.mp hp).2
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

  let slotLabel : CubicKernelSubdivisionSlot L → Fin k
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
          (fun x : Fin (2 * ell) =>
            (Sum.inl x : CubicKernelSubdivisionSlot L)) huu
      · exfalso
        have hbranch : G.degree (eB.symm u).val = 3 :=
          hcubic (eB.symm u).val (eB.symm u).property
        have hinternal :
            G.degree ((internalSlot p').2.val.val) = 2 :=
          (internalSlot p').2.val.property
        change (eB.symm u).val = (internalSlot p').2.val.val at hzz'
        rw [hzz'] at hbranch
        omega
    · rcases z' with u' | p'
      · exfalso
        have hbranch : G.degree (eB.symm u').val = 3 :=
          hcubic (eB.symm u').val (eB.symm u').property
        have hinternal :
            G.degree ((internalSlot p).2.val.val) = 2 :=
          (internalSlot p).2.val.property
        change (internalSlot p).2.val.val = (eB.symm u').val at hzz'
        rw [← hzz'] at hbranch
        omega
      · have hpp : p = p' := by
          apply internalSlot_injective
          change (internalSlot p).2.val.val =
            (internalSlot p').2.val.val at hzz'
          rcases hx : internalSlot p with ⟨C, x⟩
          rcases hy : internalSlot p' with ⟨C', y⟩
          rw [hx, hy] at hzz'
          change x.val.val = y.val.val at hzz'
          have hval : x.val = y.val := by
            apply Subtype.ext
            exact hzz'
          have hcomponent : C = C' :=
            SimpleGraph.ConnectedComponent.eq_of_common_vertex
              x.property (hval.symm ▸ y.property)
          subst C'
          have hxy : x = y := Subtype.ext hval
          subst y
          rfl
        exact congrArg
          (fun x : Σ j : Fin (3 * ell), Fin (L.length j).val =>
            (Sum.inr x : CubicKernelSubdivisionSlot L)) hpp

  have slotLabel_bijective : Function.Bijective slotLabel :=
    (Fintype.bijective_iff_injective_and_card slotLabel).mpr
      ⟨slotLabel_injective, by
        rw [cubicKernelSubdivisionSlot_card L, Fintype.card_fin]⟩
  let labels : CubicKernelSubdivisionSlot L ≃ Fin k :=
    Equiv.ofBijective slotLabel slotLabel_bijective
  let D : CubicKernelSubdivisionDatum k ell
      (normalizedCubicFiniteMultiGraph G hconn hmin hell hscard hcubic) :=
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
      apply internalReindex.symm.injective
      simp [internalReindex, Equiv.sigmaCongrLeft',
        Equiv.sigmaCongrLeft]
    simp only [slotLabel, internalSlot, Function.comp_apply]
    rw [hreindex]
  have orderedEndpoints_original (z : KernelEdgeLabel G) :
      s((eB.symm
            (cubicKernelOrderedEndpoints
              (normalizedCubicFiniteMultiGraph G hconn hmin hell hscard hcubic)
              (eE z)).1).val,
        (eB.symm
            (cubicKernelOrderedEndpoints
              (normalizedCubicFiniteMultiGraph G hconn hmin hell hscard hcubic)
              (eE z)).2).val) =
        kernelEdgeEndpoints G hacyc z := by
    have hpair :=
      (cubicKernelOrderedEndpoints_mk
        (normalizedCubicFiniteMultiGraph G hconn hmin hell hscard hcubic)
        (eE z)).trans (hend z)
    have hmapped := congrArg
      (Sym2.map (fun u : Fin (2 * ell) => (eB.symm u).val)) hpair
    calc
      s((eB.symm
              (cubicKernelOrderedEndpoints
                (normalizedCubicFiniteMultiGraph G hconn hmin hell
                  hscard hcubic) (eE z)).1).val,
          (eB.symm
              (cubicKernelOrderedEndpoints
                (normalizedCubicFiniteMultiGraph G hconn hmin hell
                  hscard hcubic) (eE z)).2).val) =
          Sym2.map Subtype.val
            (kernelBranchEndpoints G hmin hacyc z) := by
        simpa only [Sym2.map_mk, Sym2.map_map, Function.comp_apply,
          eB.symm_apply_apply] using hmapped
      _ = kernelEdgeEndpoints G hacyc z :=
        kernelBranchEndpoints_map_val G hmin hacyc z
  have componentStartEdge
      (C : (twoGraph G).ConnectedComponent) :
      s((eB.symm
            (cubicKernelOrderedEndpoints
              (normalizedCubicFiniteMultiGraph G hconn hmin hell hscard hcubic)
              (eE (Sum.inl C))).1).val,
        ((order C) 0).val.val) ∈ G.edgeFinset := by
    have hq := (qL C).property
    simp only [componentBoundaryStubs, Finset.mem_sigma,
      Finset.mem_univ, true_and, Finset.mem_filter,
      G.mem_neighborFinset] at hq
    apply G.mem_edgeFinset.mpr
    apply G.mem_edgeSet.mpr
    have hb := congrArg Subtype.val (hbranchLeft C)
    change
      (eB.symm
        (cubicKernelOrderedEndpoints
          (normalizedCubicFiniteMultiGraph G hconn hmin hell hscard hcubic)
          (eE (Sum.inl C))).1).val = (qL C).val.2 at hb
    have hx := congrArg (fun x : C => x.val.val) (hleft C)
    rw [hb, hx]
    exact hq.1.symm
  have componentEndEdge
      (C : (twoGraph G).ConnectedComponent) :
      s(((order C) (Fin.last (n C))).val.val,
        (eB.symm
            (cubicKernelOrderedEndpoints
              (normalizedCubicFiniteMultiGraph G hconn hmin hell hscard hcubic)
              (eE (Sum.inl C))).2).val) ∈ G.edgeFinset := by
    have hq := (qR C).property
    simp only [componentBoundaryStubs, Finset.mem_sigma,
      Finset.mem_univ, true_and, Finset.mem_filter,
      G.mem_neighborFinset] at hq
    apply G.mem_edgeFinset.mpr
    apply G.mem_edgeSet.mpr
    have hb := congrArg Subtype.val (hbranchRight C)
    change
      (eB.symm
        (cubicKernelOrderedEndpoints
          (normalizedCubicFiniteMultiGraph G hconn hmin hell hscard hcubic)
          (eE (Sum.inl C))).2).val = (qR C).val.2 at hb
    have hx := congrArg (fun x : C => x.val.val) (hright C)
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
    apply G.mem_edgeFinset.mpr
    apply G.mem_edgeSet.mpr
    exact hcomponent
  have subdivisionEdge_mem (q : CubicKernelSubdivisionEdgeSlot D) :
      D.subdivisionEdge q ∈ G.edgeFinset := by
    rcases D.edgeSlot_classification q with hdirect | hstart | hendSlot | hmiddle
    · obtain ⟨e, rfl⟩ := hdirect
      rcases hz : eE.symm e.1 with C | d
      · have hj : eE (Sum.inl C) = e.1 := by
          rw [← hz, eE.apply_symm_apply]
        have hlen := hcomponentLength C
        rw [hj] at hlen
        have hcard := hn C
        have hezero : (L.length e.1).val = 0 := by
          simpa [D] using e.2
        omega
      · have hj : eE (Sum.inr d) = e.1 := by
          rw [← hz, eE.apply_symm_apply]
        rw [D.subdivisionEdge_direct e.1 e.2, ← hj]
        change
          s((eB.symm
                (cubicKernelOrderedEndpoints
                  (normalizedCubicFiniteMultiGraph G hconn hmin hell
                    hscard hcubic) (eE (Sum.inr d))).1).val,
            (eB.symm
                (cubicKernelOrderedEndpoints
                  (normalizedCubicFiniteMultiGraph G hconn hmin hell
                    hscard hcubic) (eE (Sum.inr d))).2).val) ∈
            G.edgeFinset
        rw [orderedEndpoints_original (Sum.inr d)]
        exact directBranchEdges_subset_edgeFinset G d.property
    · obtain ⟨⟨f, hf⟩, rfl⟩ := hstart
      rcases hz : eE.symm f with C | d
      · have hj : eE (Sum.inl C) = f := by
          rw [← hz, eE.apply_symm_apply]
        subst f
        rw [D.subdivisionEdge_start (eE (Sum.inl C)) hf]
        change
          s((eB.symm
                (cubicKernelOrderedEndpoints
                  (normalizedCubicFiniteMultiGraph G hconn hmin hell
                    hscard hcubic) (eE (Sum.inl C))).1).val,
            labels (.inr ⟨eE (Sum.inl C), _⟩)) ∈ G.edgeFinset
        rw [labels_component C]
        convert componentStartEdge C using 1
        congr 2
      · have hj : eE (Sum.inr d) = f := by
          rw [← hz, eE.apply_symm_apply]
        have hzero := hdirectLength d
        rw [hj] at hzero
        have hepos : 0 < (L.length f).val := by
          simpa [D] using hf
        omega
    · obtain ⟨⟨f, hf⟩, rfl⟩ := hendSlot
      rcases hz : eE.symm f with C | d
      · have hj : eE (Sum.inl C) = f := by
          rw [← hz, eE.apply_symm_apply]
        subst f
        rw [D.subdivisionEdge_end (eE (Sum.inl C)) hf]
        change
          s(labels (.inr ⟨eE (Sum.inl C), _⟩),
            (eB.symm
                (cubicKernelOrderedEndpoints
                  (normalizedCubicFiniteMultiGraph G hconn hmin hell
                    hscard hcubic) (eE (Sum.inl C))).2).val) ∈
            G.edgeFinset
        rw [labels_component C]
        convert componentEndEdge C using 1
        congr 2
        apply congrArg (fun x : C => x.val)
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
        have hepos : 0 < (L.length f).val := by
          simpa [D] using hf
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
            have hp : i.val < (L.length (eE (Sum.inl C))).val - 1 := by
              have hp := i.isLt
              simp only [D] at hp
              exact hp
            omega⟩
        rw [D.subdivisionEdge_middle (eE (Sum.inl C)) i]
        change
          s(labels (.inr ⟨eE (Sum.inl C), _⟩),
            labels (.inr ⟨eE (Sum.inl C), _⟩)) ∈ G.edgeFinset
        rw [labels_component C, labels_component C]
        convert componentMiddleEdge C iC using 1
        all_goals congr 2
      · have hj : eE (Sum.inr d) = j := by
          rw [← hz, eE.apply_symm_apply]
        have hzero := hdirectLength d
        have hp : i.val < (L.length j).val - 1 := by
          have hp := i.isLt
          simp only [D] at hp
          exact hp
        have hzeroP : (L.length j).val = 0 := by
          rw [← hj]
          exact hzero
        omega
  have reconstructedGraph_eq : D.reconstructedGraph = G := by
    apply SimpleGraph.edgeFinset_inj.mp
    apply Finset.eq_of_subset_of_card_le
    · rw [D.reconstructedGraph_edgeFinset_eq_image']
      intro z hz
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz
      exact subdivisionEdge_mem q
    · rw [D.reconstructedGraph_edgeFinset_card_eq, hs]
  refine ⟨eB, eE, L, labels, hend, hcomponentLength,
    hdirectLength, ?_, ?_, ?_⟩
  · intro u
    rfl
  · intro j i
    change G.degree ((internalSlot ⟨j, i⟩).2.val.val) = 2
    exact (internalSlot ⟨j, i⟩).2.val.property
  · simpa [D] using reconstructedGraph_eq

end PerronWright.GraphCore
