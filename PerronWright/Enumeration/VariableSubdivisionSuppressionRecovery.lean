import PerronWright.Enumeration.VariableSubdivisionComponentRecovery
import PerronWright.Enumeration.FiniteKernelShape

/-!
# Recovering the suppressed kernel of a bounded-kernel subdivision

The degree-two components have already been identified with the
positive-length normalized kernel edges.  This module treats the complementary
part: direct branch edges are exactly the zero-length normalized kernel edges.
The two equivalences can then be combined into the recovered suppressed-edge
labelling.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

theorem BoundedKernelSubdivisionDatum.subdivisionEdge_direct
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (he : (D.profile.length e).val = 0) :
    D.subdivisionEdge
        (⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ :
          BoundedKernelSubdivisionEdgeSlot D) =
      s(D.branchLabel (boundedKernelOrderedEndpoints K.shape e).1,
        D.branchLabel (boundedKernelOrderedEndpoints K.shape e).2) := by
  let q : BoundedKernelSubdivisionEdgeSlot D :=
    ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩
  change D.subdivisionEdge q = _
  have hslot := D.subdivisionSlotEdge_direct e he
  change D.subdivisionSlotEdge q = _ at hslot
  calc
    D.subdivisionEdge q =
        Sym2.map D.labels (D.subdivisionSlotEdge q) :=
      D.subdivisionEdge_eq_map_slotEdge q
    _ = _ := by rw [hslot]; rfl

theorem BoundedKernelSubdivisionDatum.subdivisionEdge_start
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (he : 0 < (D.profile.length e).val) :
    D.subdivisionEdge
        (⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ :
          BoundedKernelSubdivisionEdgeSlot D) =
      s(D.branchLabel (boundedKernelOrderedEndpoints K.shape e).1,
        D.pathLabel e ⟨0, he⟩) := by
  let q : BoundedKernelSubdivisionEdgeSlot D :=
    ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩
  change D.subdivisionEdge q = _
  have hslot := D.subdivisionSlotEdge_start e he
  change D.subdivisionSlotEdge q = _ at hslot
  calc
    D.subdivisionEdge q =
        Sym2.map D.labels (D.subdivisionSlotEdge q) :=
      D.subdivisionEdge_eq_map_slotEdge q
    _ = _ := by rw [hslot]; rfl

theorem BoundedKernelSubdivisionDatum.subdivisionEdge_end
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (he : 0 < (D.profile.length e).val) :
    D.subdivisionEdge
        (⟨e, Fin.last (D.profile.length e).val⟩ :
          BoundedKernelSubdivisionEdgeSlot D) =
      s(D.pathLabel e
          ⟨(D.profile.length e).val - 1, by omega⟩,
        D.branchLabel (boundedKernelOrderedEndpoints K.shape e).2) := by
  let q : BoundedKernelSubdivisionEdgeSlot D :=
    ⟨e, Fin.last (D.profile.length e).val⟩
  change D.subdivisionEdge q = _
  have hslot := D.subdivisionSlotEdge_end e he
  change D.subdivisionSlotEdge q = _ at hslot
  calc
    D.subdivisionEdge q =
        Sym2.map D.labels (D.subdivisionSlotEdge q) :=
      D.subdivisionEdge_eq_map_slotEdge q
    _ = _ := by rw [hslot]; rfl

theorem BoundedKernelSubdivisionDatum.subdivisionEdge_middle
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
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

/-- An emitted reconstructed edge is direct branch-to-branch precisely when
its normalized kernel edge has zero internal length. -/
theorem BoundedKernelSubdivisionDatum.subdivisionEdge_mem_directBranchEdges_iff
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (q : BoundedKernelSubdivisionEdgeSlot D) :
    D.subdivisionEdge q ∈ directBranchEdges D.reconstructedGraph ↔
      (D.profile.length q.1).val = 0 := by
  constructor
  · intro hdirect
    have hdirect' :
        D.subdivisionEdge q ∈ D.reconstructedGraph.edgeFinset ∧
          ∀ b ∈ D.subdivisionEdge q,
            b ∈ branchingVertices D.reconstructedGraph := by
      simpa only [directBranchEdges, Finset.mem_filter] using hdirect
    have hall := hdirect'.2
    rcases D.edgeSlot_classification q with hq | hq | hq | hq
    · rcases hq with ⟨e, rfl⟩
      exact e.2
    · rcases hq with ⟨e, rfl⟩
      have hbranch := hall (D.pathLabel e.1 ⟨0, e.2⟩) (by
        rw [D.subdivisionEdge_start e.1 e.2]
        exact Sym2.mem_mk_right _ _)
      have hthree : 3 ≤ D.reconstructedGraph.degree
          (D.pathLabel e.1 ⟨0, e.2⟩) := by
        simpa only [branchingVertices, Finset.mem_filter,
          Finset.mem_univ, true_and] using hbranch
      have htwo := D.internalVertex_degree_eq_two e.1 ⟨0, e.2⟩
      omega
    · rcases hq with ⟨e, rfl⟩
      let i : Fin (D.profile.length e.1).val :=
        ⟨(D.profile.length e.1).val - 1, by omega⟩
      have hbranch := hall (D.pathLabel e.1 i) (by
        rw [D.subdivisionEdge_end e.1 e.2]
        exact Sym2.mem_mk_left _ _)
      have hthree : 3 ≤ D.reconstructedGraph.degree
          (D.pathLabel e.1 i) := by
        simpa only [branchingVertices, Finset.mem_filter,
          Finset.mem_univ, true_and] using hbranch
      have htwo := D.internalVertex_degree_eq_two e.1 i
      omega
    · rcases hq with ⟨⟨e, i⟩, rfl⟩
      let j : Fin (D.profile.length e).val :=
        ⟨i.val, by have := i.isLt; omega⟩
      have hbranch := hall (D.pathLabel e j) (by
        rw [D.subdivisionEdge_middle e i]
        exact Sym2.mem_mk_left _ _)
      have hthree : 3 ≤ D.reconstructedGraph.degree
          (D.pathLabel e j) := by
        simpa only [branchingVertices, Finset.mem_filter,
          Finset.mem_univ, true_and] using hbranch
      have htwo := D.internalVertex_degree_eq_two e j
      omega
  · intro hzero
    have hq : q =
        ⟨q.1, (0 : Fin ((D.profile.length q.1).val + 1))⟩ := by
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Fin.ext
        have hlt := q.2.isLt
        simp only [Fin.val_zero]
        omega
    rw [hq, D.subdivisionEdge_direct q.1 hzero]
    have hmem :
        s(D.branchLabel (boundedKernelOrderedEndpoints K.shape q.1).1,
            D.branchLabel (boundedKernelOrderedEndpoints K.shape q.1).2) ∈
            D.reconstructedGraph.edgeFinset ∧
          ∀ b ∈
              s(D.branchLabel (boundedKernelOrderedEndpoints K.shape q.1).1,
                D.branchLabel (boundedKernelOrderedEndpoints K.shape q.1).2),
            b ∈ branchingVertices D.reconstructedGraph := by
      constructor
      · rw [D.reconstructedGraph_edgeFinset_eq_image]
        apply Finset.mem_image.mpr
        refine ⟨(⟨q.1,
            (0 : Fin ((D.profile.length q.1).val + 1))⟩ :
              BoundedKernelSubdivisionEdgeSlot D), Finset.mem_univ _, ?_⟩
        exact D.subdivisionEdge_direct q.1 hzero
      · intro b hb
        rw [Sym2.mem_iff] at hb
        rcases hb with rfl | rfl
        · exact (D.mem_branchingVertices_iff_exists_branchLabel _).mpr
            ⟨(boundedKernelOrderedEndpoints K.shape q.1).1, rfl⟩
        · exact (D.mem_branchingVertices_iff_exists_branchLabel _).mpr
            ⟨(boundedKernelOrderedEndpoints K.shape q.1).2, rfl⟩
    simpa only [directBranchEdges, Finset.mem_filter] using hmem

/-- The direct branch edge emitted by a zero-length normalized kernel edge. -/
noncomputable def BoundedKernelSubdivisionDatum.zeroLengthEdgeToDirectBranchEdge
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // (D.profile.length e).val = 0}) :
    {z : Sym2 (Fin k) // z ∈ directBranchEdges D.reconstructedGraph} :=
  ⟨D.subdivisionEdge
      (⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ :
        BoundedKernelSubdivisionEdgeSlot D),
    (D.subdivisionEdge_mem_directBranchEdges_iff K _).mpr e.2⟩

theorem BoundedKernelSubdivisionDatum.zeroLengthEdgeToDirectBranchEdge_injective
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K) :
    Function.Injective (D.zeroLengthEdgeToDirectBranchEdge K) := by
  intro e f hef
  have hslot := D.subdivisionEdge_injective (congrArg Subtype.val hef)
  apply Subtype.ext
  exact congrArg Sigma.fst hslot

theorem BoundedKernelSubdivisionDatum.zeroLengthEdgeToDirectBranchEdge_surjective
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K) :
    Function.Surjective (D.zeroLengthEdgeToDirectBranchEdge K) := by
  intro z
  have hzmem : z.1 ∈ D.reconstructedGraph.edgeFinset ∧
      ∀ b ∈ z.1, b ∈ branchingVertices D.reconstructedGraph := by
    simpa only [directBranchEdges, Finset.mem_filter] using z.2
  have hzedge : z.1 ∈ D.reconstructedGraph.edgeFinset := hzmem.1
  rw [D.reconstructedGraph_edgeFinset_eq_image] at hzedge
  obtain ⟨q, _hqmem, hq⟩ := Finset.mem_image.mp hzedge
  have hqdirect :
      D.subdivisionEdge q ∈ directBranchEdges D.reconstructedGraph := by
    rw [hq]
    exact z.2
  have hzero : (D.profile.length q.1).val = 0 :=
    (D.subdivisionEdge_mem_directBranchEdges_iff K q).mp hqdirect
  let e : {e : Fin K.shape.2.1.val // (D.profile.length e).val = 0} :=
    ⟨q.1, hzero⟩
  refine ⟨e, ?_⟩
  apply Subtype.ext
  unfold BoundedKernelSubdivisionDatum.zeroLengthEdgeToDirectBranchEdge
  have hqzero : q =
      ⟨q.1, (0 : Fin ((D.profile.length q.1).val + 1))⟩ := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      have hlt := q.2.isLt
      simp only [Fin.val_zero]
      omega
  change D.subdivisionEdge
      (⟨q.1, (0 : Fin ((D.profile.length q.1).val + 1))⟩ :
        BoundedKernelSubdivisionEdgeSlot D) = z.1
  calc
    _ = D.subdivisionEdge q := congrArg D.subdivisionEdge hqzero.symm
    _ = z.1 := hq

/-- Zero-length normalized kernel edges are exactly the direct branch edges
of the reconstructed graph. -/
noncomputable def BoundedKernelSubdivisionDatum.zeroLengthEdgeEquivDirectBranchEdge
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K) :
    {e : Fin K.shape.2.1.val // (D.profile.length e).val = 0} ≃
      {z : Sym2 (Fin k) // z ∈ directBranchEdges D.reconstructedGraph} :=
  Equiv.ofBijective (D.zeroLengthEdgeToDirectBranchEdge K)
    ⟨D.zeroLengthEdgeToDirectBranchEdge_injective K,
      D.zeroLengthEdgeToDirectBranchEdge_surjective K⟩

/-- Forgetting the proof of the sign of the subdivision length identifies the
disjoint union of positive- and zero-length kernel edges with all normalized
kernel-edge labels. -/
noncomputable def BoundedKernelSubdivisionDatum.lengthSignEquivKernelEdge
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    Sum {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}
        {e : Fin K.shape.2.1.val // (D.profile.length e).val = 0} ≃
      Fin K.shape.2.1.val := by
  apply Equiv.ofBijective
    (Sum.elim Subtype.val Subtype.val)
  constructor
  · intro x y hxy
    cases x with
    | inl e =>
        cases y with
        | inl f =>
            exact congrArg Sum.inl (Subtype.ext hxy)
        | inr f =>
            exfalso
            change e.1 = f.1 at hxy
            have hzero : (D.profile.length e.1).val = 0 := by
              rw [hxy]
              exact f.2
            omega
    | inr e =>
        cases y with
        | inl f =>
            exfalso
            change e.1 = f.1 at hxy
            have hzero : (D.profile.length f.1).val = 0 := by
              rw [← hxy]
              exact e.2
            omega
        | inr f =>
            exact congrArg Sum.inr (Subtype.ext hxy)
  · intro e
    by_cases he : 0 < (D.profile.length e).val
    · exact ⟨Sum.inl ⟨e, he⟩, rfl⟩
    · have hzero : (D.profile.length e).val = 0 := Nat.eq_zero_of_not_pos he
      exact ⟨Sum.inr ⟨e, hzero⟩, rfl⟩

/-- The canonical recovered labelling of suppressed edges by the original
normalized kernel-edge labels.  Degree-two components recover positive-length
edges, while direct branch edges recover zero-length edges. -/
noncomputable def BoundedKernelSubdivisionDatum.recoveredKernelEdgeEquiv
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K) :
    KernelEdgeLabel D.reconstructedGraph ≃ Fin K.shape.2.1.val :=
  (Equiv.sumCongr
      (D.positiveKernelEdgeEquivTwoComponent K).symm
      (D.zeroLengthEdgeEquivDirectBranchEdge K).symm).trans
    D.lengthSignEquivKernelEdge

@[simp] theorem BoundedKernelSubdivisionDatum.recoveredKernelEdgeEquiv_positive
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    D.recoveredKernelEdgeEquiv K
        (.inl (D.positiveEdgeComponent K e)) = e.1 := by
  change ((D.positiveKernelEdgeEquivTwoComponent K).symm
    (D.positiveEdgeComponent K e)).1 = e.1
  exact congrArg Subtype.val
    ((D.positiveKernelEdgeEquivTwoComponent K).symm_apply_apply e)

@[simp] theorem BoundedKernelSubdivisionDatum.recoveredKernelEdgeEquiv_zero
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // (D.profile.length e).val = 0}) :
    D.recoveredKernelEdgeEquiv K
        (.inr (D.zeroLengthEdgeToDirectBranchEdge K e)) = e.1 := by
  change ((D.zeroLengthEdgeEquivDirectBranchEdge K).symm
    (D.zeroLengthEdgeToDirectBranchEdge K e)).1 = e.1
  exact congrArg Subtype.val
    ((D.zeroLengthEdgeEquivDirectBranchEdge K).symm_apply_apply e)

/-- The ordered internal positions of a positive-length kernel edge, viewed
as vertices of its recovered degree-two component. -/
noncomputable def BoundedKernelSubdivisionDatum.positiveEdgeIndexToComponent
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val})
    (i : Fin (D.profile.length e.1).val) :
    D.positiveEdgeComponent K e := by
  let x : {v : Fin k // D.reconstructedGraph.degree v = 2} :=
    ⟨D.pathLabel e.1 i, D.internalVertex_degree_eq_two e.1 i⟩
  refine ⟨x, ?_⟩
  change (twoGraph D.reconstructedGraph).connectedComponentMk x =
    D.positiveEdgeComponent K e
  unfold BoundedKernelSubdivisionDatum.positiveEdgeComponent
  apply SimpleGraph.ConnectedComponent.eq.mpr
  exact D.internalPath_reachable_twoGraph K e.1 i ⟨0, e.2⟩

theorem BoundedKernelSubdivisionDatum.positiveEdgeIndexToComponent_injective
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    Function.Injective (D.positiveEdgeIndexToComponent K e) := by
  intro i j hij
  have hlabel : D.pathLabel e.1 i = D.pathLabel e.1 j :=
    congrArg (fun x ↦ x.1.1) hij
  unfold BoundedKernelSubdivisionDatum.pathLabel at hlabel
  have hslot := D.labels.injective hlabel
  have hsigma := Sum.inr.inj hslot
  apply Fin.ext
  exact congrArg
    (fun z : Σ a : Fin K.shape.2.1.val, Fin (D.profile.length a).val ↦ z.2.val)
    hsigma

theorem BoundedKernelSubdivisionDatum.positiveEdgeIndexToComponent_surjective
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    Function.Surjective (D.positiveEdgeIndexToComponent K e) := by
  intro x
  let v : {v : Fin k // D.reconstructedGraph.degree v = 2} := x.1
  obtain ⟨f, i, hv⟩ :=
    (D.degree_eq_two_iff_exists_pathLabel v.1).mp v.2
  have hcomponent :
      (twoGraph D.reconstructedGraph).connectedComponentMk v =
        D.positiveEdgeComponent K e := x.2
  have hreach : (twoGraph D.reconstructedGraph).Reachable v
      ⟨D.pathLabel e.1 ⟨0, e.2⟩,
        D.internalVertex_degree_eq_two e.1 ⟨0, e.2⟩⟩ := by
    apply SimpleGraph.ConnectedComponent.eq.mp
    simpa only [BoundedKernelSubdivisionDatum.positiveEdgeComponent] using
      hcomponent
  have hedge := D.degreeTwoKernelEdge_eq_of_reachable K hreach
  have hvpath : v =
      ⟨D.pathLabel f i, D.internalVertex_degree_eq_two f i⟩ := by
    apply Subtype.ext
    exact hv
  have hfe : f = e.1 := by
    rw [hvpath, D.degreeTwoKernelEdge_pathLabel K,
      D.degreeTwoKernelEdge_pathLabel K] at hedge
    exact hedge
  subst f
  refine ⟨i, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hv.symm

/-- The vertices in the recovered degree-two component of a positive-length
kernel edge are canonically its ordered internal positions. -/
noncomputable def BoundedKernelSubdivisionDatum.positiveEdgeIndexEquivComponent
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    Fin (D.profile.length e.1).val ≃ D.positiveEdgeComponent K e :=
  Equiv.ofBijective (D.positiveEdgeIndexToComponent K e)
    ⟨D.positiveEdgeIndexToComponent_injective K e,
      D.positiveEdgeIndexToComponent_surjective K e⟩

/-- Suppression remembers the exact number of internal subdivision vertices
on every positive-length normalized kernel edge. -/
theorem BoundedKernelSubdivisionDatum.positiveEdgeComponent_card
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val}) :
    Fintype.card (D.positiveEdgeComponent K e) =
      (D.profile.length e.1).val := by
  rw [← Fintype.card_fin (D.profile.length e.1).val]
  exact Fintype.card_congr (D.positiveEdgeIndexEquivComponent K e).symm

/-- The original branch labels give the canonical relabelling of the
reconstructed branching vertices. -/
noncomputable def BoundedKernelSubdivisionDatum.branchLabelEquivBranching
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K) :
    Fin K.shape.1.val ≃ (branchingVertices D.reconstructedGraph : Set (Fin k)) := by
  apply Equiv.ofBijective
    (fun u ↦ ⟨D.branchLabel u,
      (D.mem_branchingVertices_iff_exists_branchLabel _).mpr ⟨u, rfl⟩⟩)
  constructor
  · intro u v huv
    have hlabel : D.branchLabel u = D.branchLabel v := congrArg Subtype.val huv
    unfold BoundedKernelSubdivisionDatum.branchLabel at hlabel
    exact Sum.inl.inj (D.labels.injective hlabel)
  · intro x
    obtain ⟨u, hu⟩ :=
      (D.mem_branchingVertices_iff_exists_branchLabel x.1).mp x.2
    refine ⟨u, ?_⟩
    exact Subtype.ext hu.symm

@[simp] theorem BoundedKernelSubdivisionDatum.branchLabelEquivBranching_apply
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (u : Fin K.shape.1.val) :
    (D.branchLabelEquivBranching K u).1 = D.branchLabel u := rfl

/-- On a zero-length edge, the recovered suppressed endpoint pair is the
original kernel endpoint pair transported by the branch-label map. -/
theorem BoundedKernelSubdivisionDatum.kernelEdgeEndpoints_zero
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (hacyc : (twoGraph D.reconstructedGraph).IsAcyclic)
    (e : {e : Fin K.shape.2.1.val // (D.profile.length e).val = 0}) :
    kernelEdgeEndpoints D.reconstructedGraph hacyc
        ((.inr (D.zeroLengthEdgeToDirectBranchEdge K e)) :
          KernelEdgeLabel D.reconstructedGraph) =
      Sym2.map D.branchLabel ((boundedKernelFiniteMultiGraph K.shape).endpoints e.1) := by
  change D.subdivisionEdge
      ⟨e.1, (0 : Fin ((D.profile.length e.1).val + 1))⟩ = _
  rw [D.subdivisionEdge_direct e.1 e.2]
  change
    s(D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).1,
        D.branchLabel (boundedKernelOrderedEndpoints K.shape e.1).2) =
      Sym2.map D.branchLabel (K.shape.2.2 e.1)
  rw [← boundedKernelOrderedEndpoints_mk K e.1, Sym2.map_mk]

/-- The branch-endpoint table of a recovered zero-length edge becomes the
literal original endpoint table after transporting both branch labels back. -/
theorem BoundedKernelSubdivisionDatum.kernelBranchEndpoints_zero
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (hmin : ∀ v, 2 ≤ D.reconstructedGraph.degree v)
    (hacyc : (twoGraph D.reconstructedGraph).IsAcyclic)
    (e : {e : Fin K.shape.2.1.val // (D.profile.length e).val = 0}) :
    Sym2.map (D.branchLabelEquivBranching K).symm
        (kernelBranchEndpoints D.reconstructedGraph hmin hacyc
          ((.inr (D.zeroLengthEdgeToDirectBranchEdge K e)) :
            KernelEdgeLabel D.reconstructedGraph)) =
      (boundedKernelFiniteMultiGraph K.shape).endpoints e.1 := by
  let E := D.branchLabelEquivBranching K
  let z : KernelEdgeLabel D.reconstructedGraph :=
    (.inr (D.zeroLengthEdgeToDirectBranchEdge K e) :
      KernelEdgeLabel D.reconstructedGraph)
  change Sym2.map E.symm
      (kernelBranchEndpoints D.reconstructedGraph hmin hacyc z) = _
  apply Sym2.map.injective E.injective
  rw [Sym2.map_map, Equiv.self_comp_symm, Sym2.map_id]
  apply Sym2.map.injective Subtype.val_injective
  rw [Sym2.map_map]
  change Sym2.map Subtype.val
      (kernelBranchEndpoints D.reconstructedGraph hmin hacyc z) =
    Sym2.map (fun u ↦ D.branchLabel u) ((boundedKernelFiniteMultiGraph K.shape).endpoints e.1)
  have hmap := kernelBranchEndpoints_map_val
    D.reconstructedGraph hmin hacyc z
  rw [hmap]
  simpa only [z] using D.kernelEdgeEndpoints_zero K hacyc e

end PerronWright.GraphCore
