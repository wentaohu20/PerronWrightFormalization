import PerronWright.Enumeration.TreeRootEdgeFactor

/-!
# Root-neighbor kernel factors

The edges incident to the root contribute exactly one kernel factor per
neighbor. Combined with blockwise nonroot edges, this gives the full exact
edge-factor decomposition for the actual finite labelled graph.
-/

open scoped Classical

namespace PerronWright

theorem CompactBJRModel.zeroTree_incident_edges_eq_neighbor_kernels
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (x : Fin (n + 1) → S) :
    (∏ e ∈ H.incidenceFinset 0, M.edgeFactor 1 x e) =
      ∏ j ∈ H.neighborFinset 0, M.kernel (x 0) (x j) := by
  classical
  calc
    _ = ∏ e : H.incidenceSet 0, M.edgeFactor 1 x e.1 :=
      Finset.prod_subtype (H.incidenceFinset 0)
        (fun e => H.mem_incidenceFinset 0 e) _
    _ = ∏ j : H.neighborSet 0, M.kernel (x 0) (x j.1) := by
      symm
      apply Fintype.prod_equiv (H.incidenceSetEquivNeighborSet 0).symm
      intro j
      change M.kernel (x 0) (x j.1) =
        M.edgeFactor 1 x s(0, j.1)
      simp only [CompactBJRModel.edgeFactor_mk, one_mul]
    _ = _ := (Finset.prod_subtype (H.neighborFinset 0)
        (fun j => H.mem_neighborFinset 0 j)
        (fun j : Fin (n + 1) => M.kernel (x 0) (x j))).symm

theorem CompactBJRModel.zeroTree_edge_factors_root_kernel_partition
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (x : Fin (n + 1) → S) :
    (∏ e ∈ H.edgeFinset, M.edgeFactor 1 x e) =
      (∏ j ∈ H.neighborFinset 0, M.kernel (x 0) (x j)) *
        ∏ B ∈ (finRootlessPartition n H).parts,
          ∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset
              with e.out.1 ∈ B ∧ e.out.2 ∈ B,
            M.edgeFactor 1 (fun i => x i.succ) e := by
  rw [M.zeroTree_edge_factors_partition H x]
  rw [M.zeroTree_incident_edges_eq_neighbor_kernels H x]


end PerronWright


