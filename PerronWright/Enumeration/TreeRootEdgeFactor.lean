import PerronWright.Enumeration.TreeRootVertexFactor
import PerronWright.Enumeration.LeafIterate

/-!
# Edge factors across root-deleted tree blocks

This module gives exact finite-set and zero-field kernel-factor decompositions
for a labelled graph rooted at zero. The equalities are combinatorial and do
not yet assert the corresponding product-measure integral factorisation.
-/

open scoped Classical

namespace PerronWright

theorem finRootless_edge_product_partition {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (w : Sym2 (Fin n) → ℝ) :
    (∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset, w e) =
      ∏ B ∈ (finRootlessPartition n H).parts,
        ∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset
            with (finRootlessPartition n H).part e.out.1 = B,
          w e := by
  classical
  symm
  apply Finset.prod_fiberwise_of_maps_to
  intro e he
  exact (finRootlessPartition n H).part_mem.mpr (Finset.mem_univ e.out.1)

theorem finRootless_edge_endpoints_same_part {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (e : Sym2 (Fin n))
    (he : e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset) :
    e.out.1 ∈ (finRootlessPartition n H).part e.out.1 ∧
      e.out.2 ∈ (finRootlessPartition n H).part e.out.1 := by
  let P := finRootlessPartition n H
  let G := H.comap (Fin.succ : Fin n → Fin (n + 1))
  have hadj : G.Adj e.out.1 e.out.2 := by
    have he' : s(e.out.1, e.out.2) ∈ G.edgeFinset := by
      rw [Sym2.mk, e.out_eq]
      exact he
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he'
  have hsame := finRootless_adj_same_part H e.out.1 e.out.2 hadj
  constructor
  · exact P.mem_part_self.mpr (Finset.mem_univ _)
  · rw [hsame]
    exact P.mem_part_self.mpr (Finset.mem_univ _)

theorem finRootless_edge_block_iff_endpoints {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (B : Finset (Fin n))
    (hB : B ∈ (finRootlessPartition n H).parts)
    (e : Sym2 (Fin n))
    (he : e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset) :
    (finRootlessPartition n H).part e.out.1 = B ↔
      e.out.1 ∈ B ∧ e.out.2 ∈ B := by
  let P := finRootlessPartition n H
  constructor
  · intro h
    have hh := finRootless_edge_endpoints_same_part H e he
    simpa [h] using hh
  · intro h
    exact P.part_eq_of_mem hB h.1

private theorem sym2_mem_iff_out_endpoints {n : ℕ}
    (B : Finset (Fin n)) (e : Sym2 (Fin n)) :
    e ∈ B.sym2 ↔ e.out.1 ∈ B ∧ e.out.2 ∈ B := by
  have heq : s(e.out.1, e.out.2) = e := by
    simpa only [Sym2.mk] using e.out_eq
  constructor
  · intro h
    have h' : s(e.out.1, e.out.2) ∈ B.sym2 := by
      rw [heq]
      exact h
    exact Finset.mk_mem_sym2_iff.mp h'
  · intro h
    have h' : s(e.out.1, e.out.2) ∈ B.sym2 :=
      Finset.mk_mem_sym2_iff.mpr h
    rw [heq] at h'
    exact h'

theorem finRootless_block_edgeFinset_eq {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (s : Set (Fin n)) [DecidablePred (· ∈ s)] :
    ((H.comap (Fin.succ : Fin n → Fin (n + 1))).induce s).edgeFinset.map
      (Function.Embedding.subtype (· ∈ s)).sym2Map =
      ((H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset.filter
        (fun e => e.out.1 ∈ s ∧ e.out.2 ∈ s)) := by
  classical
  rw [SimpleGraph.map_edgeFinset_induce]
  ext e
  simp only [Finset.mem_inter, Finset.mem_filter]
  exact and_congr_right (fun _ => by
    simpa using sym2_mem_iff_out_endpoints s.toFinset e)

theorem CompactBJRModel.zeroTree_edge_factors_root_split
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (x : Fin (n + 1) → S) :
    (∏ e ∈ H.edgeFinset, M.edgeFactor 1 x e) =
      (∏ e ∈ H.incidenceFinset 0, M.edgeFactor 1 x e) *
        (∏ e ∈ (H.deleteIncidenceSet 0).edgeFinset,
          M.edgeFactor 1 x e) := by
  classical
  rw [H.edgeFinset_deleteIncidenceSet_eq_sdiff]
  calc
    _ = (∏ e ∈ H.edgeFinset \ H.incidenceFinset 0,
          M.edgeFactor 1 x e) *
          (∏ e ∈ H.incidenceFinset 0, M.edgeFactor 1 x e) :=
      (Finset.prod_sdiff (H.incidenceFinset_subset 0)).symm
    _ = _ := mul_comm _ _

theorem CompactBJRModel.zeroTree_rootless_edge_factors_partition
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (z : Fin n → S) :
    (∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset,
      M.edgeFactor 1 z e) =
      ∏ B ∈ (finRootlessPartition n H).parts,
        ∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset
          with e.out.1 ∈ B ∧ e.out.2 ∈ B,
          M.edgeFactor 1 z e := by
  classical
  rw [finRootless_edge_product_partition]
  apply Finset.prod_congr rfl
  intro B hB
  congr 1
  ext e
  simp only [Finset.mem_filter]
  exact and_congr_right (fun he => finRootless_edge_block_iff_endpoints H B hB e he)

theorem CompactBJRModel.zeroTree_surviving_edge_factors_relabel
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (x : Fin (n + 1) → S) :
    (∏ e ∈ (H.deleteIncidenceSet 0).edgeFinset,
      M.edgeFactor 1 x e) =
      ∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset,
        M.edgeFactor 1 (fun i => x i.succ) e := by
  classical
  have heq : (H.deleteIncidenceSet 0).edgeFinset =
      ((H.comap (0 : Fin (n + 1)).succAbove).map
        (0 : Fin (n + 1)).succAboveEmb).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [GraphCore.map_survivor_graph_eq_delete H 0]
  rw [heq]
  have hmap :
      ((H.comap (0 : Fin (n + 1)).succAbove).map
        (0 : Fin (n + 1)).succAboveEmb).edgeFinset =
        (H.comap (0 : Fin (n + 1)).succAbove).edgeFinset.map
          (0 : Fin (n + 1)).succAboveEmb.sym2Map := by
    ext e
    rw [← SimpleGraph.edgeFinset_map]
    simp only [SimpleGraph.mem_edgeFinset]
  rw [hmap, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ i j =>
      change M.edgeFactor 1 x
        (Sym2.map (0 : Fin (n + 1)).succAbove s(i, j)) =
          M.edgeFactor 1 (fun i => x i.succ) s(i, j)
      rw [Sym2.map_mk]
      simp only [CompactBJRModel.edgeFactor_mk,
        Fin.succAbove_zero_apply]

theorem CompactBJRModel.zeroTree_edge_factors_partition
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (x : Fin (n + 1) → S) :
    (∏ e ∈ H.edgeFinset, M.edgeFactor 1 x e) =
      (∏ e ∈ H.incidenceFinset 0, M.edgeFactor 1 x e) *
        ∏ B ∈ (finRootlessPartition n H).parts,
          ∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset
              with e.out.1 ∈ B ∧ e.out.2 ∈ B,
            M.edgeFactor 1 (fun i => x i.succ) e := by
  rw [M.zeroTree_edge_factors_root_split H x]
  rw [M.zeroTree_surviving_edge_factors_relabel H x]
  rw [M.zeroTree_rootless_edge_factors_partition H]


end PerronWright


