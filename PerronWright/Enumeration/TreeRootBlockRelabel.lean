import PerronWright.Enumeration.TreeRootBlockNeighbor

/-!
# Relabelling one root-deleted tree block

For a tree on `Fin (n+1)`, fix a nonroot vertex `i` and hence the block of
the rootless partition containing it.  If `i` is adjacent to the root, it is
the unique such vertex in the block.  The genuine block integrand is then a
single parent kernel factor times the zero-field graph integrand of the
relabelled block tree `finRootlessBlockTreeGraph n H i`.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright

set_option linter.style.haveILetI false in
theorem CompactBJRModel.tree_rootBlockWeightIntegrand_relabel
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (i : Fin n) (hi : H.Adj 0 i.succ)
    (root : S)
    (y : ((finRootlessPartition n H).part i) → S) :
    M.rootBlockWeightIntegrand H ((finRootlessPartition n H).part i)
        (Fin.cons root
          (extendBlock ((finRootlessPartition n H).part i) root y)) =
      M.kernel root
          (y ⟨i, (finRootlessPartition n H).mem_part_self.mpr
            (Finset.mem_univ i)⟩) *
        M.fieldGraphWeightIntegrand 0
          (finRootlessBlockTreeGraph n H i)
          (fun q => y (((finRootlessPartition n H).part i).equivFin.symm q)) := by
  classical
  let P := finRootlessPartition n H
  let B := P.part i
  letI : Fintype B :=
    Subtype.fintype (fun x : Fin n => x ∈ (B : Set (Fin n)))
  have hiB : i ∈ B := P.mem_part_self.mpr (Finset.mem_univ i)
  have hB : B ∈ P.parts := P.part_mem.mpr (Finset.mem_univ i)
  obtain ⟨j, hjB, hjroot, hjprod⟩ :=
    M.tree_root_block_kernel_product_eq_single H hT B hB
  have hji : j = i := by
    obtain ⟨_, _, huniq⟩ :=
      finRootlessPartition_part_existsUnique_root_neighbor H hT B hB
    exact huniq j ⟨hjB, hjroot⟩ |>.trans (huniq i ⟨hiB, hi⟩).symm
  subst j
  have hrootprod := hjprod root
    (extendBlock B root y)
  have hrootprod' :
      (∏ j ∈ B, if H.Adj 0 j.succ then
          M.kernel root ((extendBlock B root y) j) else 1) =
        M.kernel root (y ⟨i, hiB⟩) := by
    simpa only [extendBlock, dif_pos hiB] using hrootprod
  have hvert :
      (∏ j ∈ B,
          M.zeroTreeVertexFactor ((extendBlock B root y) j)) =
        ∏ q : Fin B.card,
          Real.exp (-M.degreeFunction (y (B.equivFin.symm q))) := by
    calc
      _ = ∏ b : B, M.zeroTreeVertexFactor ((extendBlock B root y) b.1) := by
        exact Finset.prod_subtype B (fun _ => Iff.rfl)
          (fun j => M.zeroTreeVertexFactor ((extendBlock B root y) j))
      _ = ∏ b : B, M.zeroTreeVertexFactor (y b) := by
        apply Finset.prod_congr rfl
        intro b _
        simp only [extendBlock, dif_pos b.property]
      _ = ∏ q : Fin B.card, M.zeroTreeVertexFactor (y (B.equivFin.symm q)) := by
        exact Fintype.prod_equiv B.equivFin
          (fun b : B => M.zeroTreeVertexFactor (y b))
          (fun q : Fin B.card => M.zeroTreeVertexFactor (y (B.equivFin.symm q)))
          (fun b => by simp only [Equiv.symm_apply_apply])
      _ = _ := by
        apply Finset.prod_congr rfl
        intro q _
        rw [M.zeroTreeVertexFactor_apply]
  have hedge :
      (∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset
          with e.out.1 ∈ B ∧ e.out.2 ∈ B,
        M.edgeFactor 1 (extendBlock B root y) e) =
      ∏ e ∈ (finRootlessBlockTreeGraph n H i).edgeFinset,
        M.edgeFactor 1 (fun q => y (B.equivFin.symm q)) e := by
    let G := H.comap (Fin.succ : Fin n → Fin (n + 1))
    change (∏ e ∈ G.edgeFinset
        with e.out.1 ∈ (B : Set (Fin n)) ∧ e.out.2 ∈ (B : Set (Fin n)),
          M.edgeFactor 1 (extendBlock B root y) e) = _
    rw [← finRootless_block_edgeFinset_eq H (B : Set (Fin n))]
    rw [Finset.prod_map]
    let eSym : Sym2 B ≃ Sym2 (Fin B.card) :=
      { toFun := Sym2.map B.equivFin
        invFun := Sym2.map B.equivFin.symm
        left_inv := by
          intro e
          induction e using Sym2.inductionOn with
          | _ a b => simp only [Sym2.map_mk, Equiv.symm_apply_apply]
        right_inv := by
          intro e
          induction e using Sym2.inductionOn with
          | _ a b => simp only [Sym2.map_mk, Equiv.apply_symm_apply] }
    apply Finset.prod_equiv eSym
    · intro e
      induction e using Sym2.inductionOn with
      | _ a b =>
          rw [show eSym s(a, b) = s(B.equivFin a, B.equivFin b) from rfl]
          constructor
          · intro hab
            have hab' : (G.induce (B : Set (Fin n))).Adj a b :=
              (SimpleGraph.mem_edgeSet (G.induce (B : Set (Fin n)))).mp
                (SimpleGraph.mem_edgeFinset.mp hab)
            apply SimpleGraph.mem_edgeFinset.mpr
            apply (SimpleGraph.mem_edgeSet
              (finRootlessBlockTreeGraph n H i)).mpr
            simpa only [finRootlessBlockTreeGraph, B, P, G,
              SimpleGraph.comap_adj, Equiv.symm_apply_apply,
              Function.Embedding.subtype_apply] using hab'
          · intro hab
            have hab' :
                (finRootlessBlockTreeGraph n H i).Adj
                  (B.equivFin a) (B.equivFin b) :=
              (SimpleGraph.mem_edgeSet
                (finRootlessBlockTreeGraph n H i)).mp
                (SimpleGraph.mem_edgeFinset.mp hab)
            apply SimpleGraph.mem_edgeFinset.mpr
            apply (SimpleGraph.mem_edgeSet
              (G.induce (B : Set (Fin n)))).mpr
            simpa only [finRootlessBlockTreeGraph, B, P, G,
              SimpleGraph.comap_adj, Equiv.symm_apply_apply,
              Function.Embedding.subtype_apply] using hab'
    · intro e he
      induction e using Sym2.inductionOn with
      | _ a b =>
          rw [show eSym s(a, b) = s(B.equivFin a, B.equivFin b) from rfl]
          change M.edgeFactor 1 (extendBlock B root y) s(a.1, b.1) =
            M.edgeFactor 1 (fun q => y (B.equivFin.symm q))
              s(B.equivFin a, B.equivFin b)
          rw [M.edgeFactor_mk, M.edgeFactor_mk]
          simp only [one_mul, extendBlock, dif_pos a.property,
            dif_pos b.property, Equiv.symm_apply_apply]
  unfold CompactBJRModel.rootBlockWeightIntegrand
    CompactBJRModel.rootlessBlockWeightIntegrand
    CompactBJRModel.fieldGraphWeightIntegrand
  simp only [Fin.cons_zero, Fin.cons_succ, ContinuousMap.zero_apply, zero_sub]
  rw [hrootprod']
  change M.kernel root (y ⟨i, hiB⟩) *
      ((∏ j ∈ B, M.zeroTreeVertexFactor ((extendBlock B root y) j)) *
        ∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset
            with e.out.1 ∈ B ∧ e.out.2 ∈ B,
          M.edgeFactor 1 (extendBlock B root y) e) =
    M.kernel root (y ⟨i, hiB⟩) *
      ((∏ q : Fin B.card,
          Real.exp (-M.degreeFunction (y (B.equivFin.symm q)))) *
        ∏ e ∈ (finRootlessBlockTreeGraph n H i).edgeFinset,
          M.edgeFactor 1 (fun q => y (B.equivFin.symm q)) e)
  rw [hvert, hedge]

/-- The blockwise pointwise relabelling above preserves the full product
measure.  Thus the genuine integral over the original block coordinates is
the parent-kernel-weighted integral of the corresponding relabelled tree.
This is the measure-theoretic block identity used by the all-size rooted-tree
recursion. -/
theorem CompactBJRModel.tree_rootBlock_integral_relabel
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (hT : H.IsTree)
    (i : Fin n) (hi : H.Adj 0 i.succ) (root : S) :
    (∫ y : ((finRootlessPartition n H).part i) → S,
      M.rootBlockWeightIntegrand H ((finRootlessPartition n H).part i)
        (Fin.cons root
          (extendBlock ((finRootlessPartition n H).part i) root y))
        ∂Measure.pi
          (fun _ : ((finRootlessPartition n H).part i) => M.mu)) =
      ∫ z : Fin ((finRootlessPartition n H).part i).card → S,
        M.kernel root
            (z (((finRootlessPartition n H).part i).equivFin
              ⟨i, (finRootlessPartition n H).mem_part_self.mpr
                (Finset.mem_univ i)⟩)) *
          M.fieldGraphWeightIntegrand 0
            (finRootlessBlockTreeGraph n H i) z
        ∂Measure.pi
          (fun _ : Fin ((finRootlessPartition n H).part i).card => M.mu) := by
  classical
  let P := finRootlessPartition n H
  let B := P.part i
  have hiB : i ∈ B := P.mem_part_self.mpr (Finset.mem_univ i)
  let e : (Fin B.card → S) ≃ᵐ (B → S) :=
    MeasurableEquiv.piCongrLeft (fun _ : B => S) B.equivFin.symm
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin B.card => M.mu))
      (Measure.pi (fun _ : B => M.mu)) :=
    measurePreserving_piCongrLeft (fun _ : B => M.mu) B.equivFin.symm
  calc
    _ = ∫ z : Fin B.card → S,
        M.rootBlockWeightIntegrand H B
          (Fin.cons root (extendBlock B root (e z)))
          ∂Measure.pi (fun _ : Fin B.card => M.mu) := by
      exact (hmp.integral_comp'
        (fun y : B → S =>
          M.rootBlockWeightIntegrand H B
            (Fin.cons root (extendBlock B root y)))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [M.tree_rootBlockWeightIntegrand_relabel H hT i hi root (e z)]
      have hroot : e z ⟨i, hiB⟩ = z (B.equivFin ⟨i, hiB⟩) := by
        simpa only [Equiv.symm_apply_apply] using
          (MeasurableEquiv.piCongrLeft_apply_apply
            (β := fun _ : B => S) B.equivFin.symm z
            (B.equivFin ⟨i, hiB⟩))
      have hcoords :
          (fun q => e z (B.equivFin.symm q)) = z := by
        funext q
        exact MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : B => S) B.equivFin.symm z q
      rw [hroot, hcoords]

end PerronWright
