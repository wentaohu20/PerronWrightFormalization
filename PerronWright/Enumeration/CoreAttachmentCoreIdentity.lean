import PerronWright.Enumeration.CoreAttachmentWeightArbitrary
import PerronWright.Enumeration.DegreeTwoPaths

/-!
# The greatest two-core of an explicit core/forest assembly

This file proves the missing structural inverse lemma without choosing a
representative of an unspecified classification fibre.
-/

open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore

set_option linter.style.haveILetI false in
/-- A finite nonempty forest with no isolated vertices has two distinct
leaves.  We only need this form: choose one connected component, use positive
degree to see that it is nontrivial, and apply the two-leaves theorem there. -/
theorem isAcyclic_exists_two_leaves_of_forall_degree_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (hacyc : G.IsAcyclic) (hpos : ∀ v, 0 < G.degree v) :
    ∃ u v : V, u ≠ v ∧ G.degree u = 1 ∧ G.degree v = 1 := by
  classical
  let x : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (hpos x)
  let C : G.ConnectedComponent := G.connectedComponentMk x
  have hxC : x ∈ C.supp := by
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hyC : y ∈ C.supp := C.mem_supp_of_adj_mem_supp hxC hxy
  let xC : C := ⟨x, hxC⟩
  let yC : C := ⟨y, hyC⟩
  have hxyC : xC ≠ yC := by
    intro h
    exact G.ne_of_adj hxy (congrArg Subtype.val h)
  letI : Nontrivial C := ⟨⟨xC, yC, hxyC⟩⟩
  obtain ⟨u, v, huv, hu, hv⟩ :=
    (hacyc.isTree_connectedComponent C).exists_ne_and_degree_eq_one
  refine ⟨u.1, v.1, ?_, ?_, ?_⟩
  · intro h
    exact huv (Subtype.ext h)
  · rw [← connectedComponent_degree_eq G C u]
    exact hu
  · rw [← connectedComponent_degree_eq G C v]
    exact hv

/-- For a vertex in a fixed attachment block, adjacency to the core occurs
exactly at the stored root, and then only at the stored core colour. -/
theorem LabelledCoreForestAttachment.assembleGraph_adj_off_core_iff_eq_root
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n) (B : D.1.parts)
    (x : B.1) (c : Fin q) :
    (D.assembleGraph H).Adj (Sum.inr x.1) (Sum.inl c) ↔
      (D.2 B).1 = c ∧ (D.2 B).2.root = x := by
  rw [D.assembleGraph_adj_off_core]
  constructor
  · rintro ⟨C, hc, hx⟩
    have hCB : C = B := by
      apply Subtype.ext
      calc
        C.1 = D.1.part (D.2 C).2.root.1 :=
          (D.1.part_eq_of_mem C.2 (D.2 C).2.root.2).symm
        _ = D.1.part x.1 := congrArg D.1.part hx
        _ = B.1 := D.1.part_eq_of_mem B.2 x.2
    subst C
    exact ⟨hc, Subtype.ext hx⟩
  · rintro ⟨hc, hx⟩
    subst c
    subst x
    exact ⟨B, rfl, rfl⟩

set_option linter.style.haveILetI false in
/-- No vertex in one of the attached rooted trees can belong to any
two-core of the assembled graph.  The proof is local to its actual partition
block and uses only the one stored boundary edge of that block. -/
theorem LabelledCoreForestAttachment.isTwoCore_subset_range_inl
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n)
    {s : Set (Fin q ⊕ Fin n)}
    (hs : IsTwoCore (D.assembleGraph H) s) :
    s ⊆ Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n) := by
  classical
  intro v hv
  rcases v with c | i
  · exact ⟨c, rfl⟩
  · exfalso
    let B : D.1.parts :=
      ⟨D.1.part i, D.1.part_mem.mpr (Finset.mem_univ i)⟩
    have hiB : i ∈ B.1 := D.1.mem_part_self.mpr (Finset.mem_univ i)
    let x₀ : B.1 := ⟨i, hiB⟩
    let U : Set B.1 := {x | Sum.inr x.1 ∈ s}
    let K : SimpleGraph U := (D.2 B).2.graph.induce U
    letI : Nonempty U := ⟨⟨x₀, hv⟩⟩
    letI : DecidableRel K.Adj := fun x y ↦
      Classical.propDecidable (K.Adj x y)
    have hKacyc : K.IsAcyclic := (D.2 B).2.isTree.isAcyclic.induce U

    have liftOffNeighbor (x : U) (j : Fin n)
        (hj : Sum.inr j ∈ s)
        (hxj : (D.assembleGraph H).Adj
          (Sum.inr x.1.1) (Sum.inr j)) :
        ∃ y : U, K.Adj x y ∧ y.1.1 = j := by
      have hpart : D.1.part x.1.1 = D.1.part j :=
        D.off_adj_part_eq H hxj
      have hxpart : D.1.part x.1.1 = B.1 :=
        D.1.part_eq_of_mem B.2 x.1.2
      have hjself : j ∈ D.1.part j :=
        D.1.mem_part_self.mpr (Finset.mem_univ j)
      have hjB : j ∈ B.1 := by
        rw [← hpart, hxpart] at hjself
        exact hjself
      let yB : B.1 := ⟨j, hjB⟩
      have hbranch : (D.2 B).2.graph.Adj x.1 yB := by
        rw [← D.induce_off_assembleGraph_block H B]
        exact hxj
      let y : U := ⟨yB, hj⟩
      refine ⟨y, ?_, rfl⟩
      exact hbranch

    have hpos (x : U) : 0 < K.degree x := by
      obtain ⟨w, hw, z, hz, hwz, hxw, hxz⟩ := hs _ x.2
      rcases w with c | j
      · rcases z with d | l
        · have hwroot :=
            (LabelledCoreForestAttachment.assembleGraph_adj_off_core_iff_eq_root
              H D B x.1 c).mp hxw
          have hzroot :=
            (LabelledCoreForestAttachment.assembleGraph_adj_off_core_iff_eq_root
              H D B x.1 d).mp hxz
          have hcd : c = d := hwroot.1.symm.trans hzroot.1
          exact False.elim (hwz (congrArg Sum.inl hcd))
        · obtain ⟨y, hxy, -⟩ := liftOffNeighbor x l hz hxz
          exact (K.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩
      · obtain ⟨y, hxy, -⟩ := liftOffNeighbor x j hw hxw
        exact (K.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩

    have htwo (x : U) (hxroot : x.1 ≠ (D.2 B).2.root) :
        2 ≤ K.degree x := by
      obtain ⟨w, hw, z, hz, hwz, hxw, hxz⟩ := hs _ x.2
      rcases w with c | j
      · have hroot :=
          (LabelledCoreForestAttachment.assembleGraph_adj_off_core_iff_eq_root
            H D B x.1 c).mp hxw
        exact False.elim (hxroot hroot.2.symm)
      · rcases z with d | l
        · have hroot :=
            (LabelledCoreForestAttachment.assembleGraph_adj_off_core_iff_eq_root
              H D B x.1 d).mp hxz
          exact False.elim (hxroot hroot.2.symm)
        · obtain ⟨y, hxy, hy⟩ := liftOffNeighbor x j hw hxw
          obtain ⟨z, hxz', hz'⟩ := liftOffNeighbor x l hz hxz
          have hyz : y ≠ z := by
            intro h
            apply hwz
            apply congrArg Sum.inr
            calc
              j = y.1.1 := hy.symm
              _ = z.1.1 := congrArg (fun a : U ↦ a.1.1) h
              _ = l := hz'
          have hyMem : y ∈ K.neighborFinset x :=
            (K.mem_neighborFinset x y).mpr hxy
          have hzMem : z ∈ K.neighborFinset x :=
            (K.mem_neighborFinset x z).mpr hxz'
          have hcard : 1 < (K.neighborFinset x).card :=
            Finset.one_lt_card_iff.mpr ⟨y, z, hyMem, hzMem, hyz⟩
          rw [K.card_neighborFinset_eq_degree] at hcard
          omega

    have hone (x : U) (hx : K.degree x = 1) :
        x.1 = (D.2 B).2.root := by
      by_contra hne
      have hge := htwo x hne
      omega

    obtain ⟨x, y, hxy, hx, hy⟩ :=
      isAcyclic_exists_two_leaves_of_forall_degree_pos K hKacyc hpos
    have hxroot := hone x hx
    have hyroot := hone y hy
    exact hxy (Subtype.ext (hxroot.trans hyroot.symm))

/-- The literal greatest two-core of an explicitly assembled admissible core
with rooted-tree attachments is exactly the left summand. -/
theorem LabelledCoreForestAttachment.greatestTwoCore_assembleGraph_eq_range_inl
    {q n : ℕ} (H : SimpleGraph (Fin q))
    (D : LabelledCoreForestAttachment q n)
    (hH : IsTwoCore H Set.univ) :
    greatestTwoCore (D.assembleGraph H) =
      Set.range (Sum.inl : Fin q → Fin q ⊕ Fin n) := by
  apply Set.Subset.antisymm
  · exact LabelledCoreForestAttachment.isTwoCore_subset_range_inl H D
      (isTwoCore_greatest (D.assembleGraph H))
  · apply isTwoCore_subset_greatest
    intro v hv
    obtain ⟨i, rfl⟩ := hv
    obtain ⟨w, -, z, -, hwz, hiw, hiz⟩ := hH i (Set.mem_univ i)
    refine ⟨Sum.inl w, ⟨w, rfl⟩, Sum.inl z, ⟨z, rfl⟩, ?_, hiw, hiz⟩
    intro h
    exact hwz (Sum.inl_injective h)

end GraphCore
end PerronWright
