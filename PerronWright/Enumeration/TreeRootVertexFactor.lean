import PerronWright.Enumeration.TreeRootFinRelabel
import PerronWright.Enumeration.TreeCoefficientContinuous

/-!
# First weight factorisation across root-deleted blocks

Every edge avoiding the root stays within a unique root-deleted block. The
product of vertex factors splits into the root factor and one product per
block. Edge-factor and integral factorisation are separate later steps.
-/

open scoped Classical

namespace PerronWright

theorem finpartition_prod_univ {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n)))
    (f : Fin n → ℝ) :
    (∏ i : Fin n, f i) = ∏ B ∈ P.parts, ∏ i ∈ B, f i := by
  classical
  calc
    (∏ i : Fin n, f i) = ∏ i ∈ P.parts.biUnion id, f i := by
      rw [P.biUnion_parts]
    _ = ∏ B ∈ P.parts, ∏ i ∈ B, f i :=
      Finset.prod_biUnion P.supIndep.pairwiseDisjoint

theorem finRootless_adj_same_part {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (i j : Fin n)
    (hij : H.Adj i.succ j.succ) :
    (finRootlessPartition n H).part i =
      (finRootlessPartition n H).part j := by
  let P := finRootlessPartition n H
  have hrootless :
      (H.induce ({(0 : Fin (n + 1))}ᶜ : Set (Fin (n + 1)))).Adj
        ⟨i.succ, i.succ_ne_zero⟩ ⟨j.succ, j.succ_ne_zero⟩ := hij
  have hj : j ∈ P.part i :=
    (finRootlessPartition_mem_part_iff n H i j).mpr
      (SimpleGraph.ConnectedComponent.eq.mpr hrootless.reachable)
  exact (P.part_eq_of_mem (P.part_mem.mpr (Finset.mem_univ i)) hj).symm

theorem CompactBJRModel.zeroTree_vertex_factors_partition
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (x : Fin (n + 1) → S) :
    (∏ i : Fin (n + 1), M.zeroTreeVertexFactor (x i)) =
      M.zeroTreeVertexFactor (x 0) *
        ∏ B ∈ (finRootlessPartition n H).parts,
          ∏ i ∈ B, M.zeroTreeVertexFactor (x i.succ) := by
  rw [Fin.prod_univ_succ]
  congr 1
  exact finpartition_prod_univ (finRootlessPartition n H)
    (fun i => M.zeroTreeVertexFactor (x i.succ))

end PerronWright
