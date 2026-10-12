import PerronWright.Enumeration.TreeRootKernelFactor

/-!
# Pointwise root-block factorisation of the actual zero-field graph weight

The exact finite-graph integrand factors into the root vertex factor, one
kernel factor for each root edge, and a local integrand for each component of
the root-deleted graph. No product-measure integral has been factored yet.
-/

open scoped Classical

namespace PerronWright

noncomputable def CompactBJRModel.rootlessBlockWeightIntegrand
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (B : Finset (Fin n)) (x : Fin (n + 1) → S) : ℝ :=
  (∏ i ∈ B, M.zeroTreeVertexFactor (x i.succ)) *
    ∏ e ∈ (H.comap (Fin.succ : Fin n → Fin (n + 1))).edgeFinset
        with e.out.1 ∈ B ∧ e.out.2 ∈ B,
      M.edgeFactor 1 (fun i => x i.succ) e

theorem CompactBJRModel.zeroTree_integrand_root_partition
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (x : Fin (n + 1) → S) :
    M.fieldGraphWeightIntegrand 0 H x =
      M.zeroTreeVertexFactor (x 0) *
        (∏ j ∈ H.neighborFinset 0, M.kernel (x 0) (x j)) *
          ∏ B ∈ (finRootlessPartition n H).parts,
            M.rootlessBlockWeightIntegrand H B x := by
  classical
  have hbase : M.fieldGraphWeightIntegrand 0 H x =
      (∏ i : Fin (n + 1), M.zeroTreeVertexFactor (x i)) *
        (∏ e ∈ H.edgeFinset, M.edgeFactor 1 x e) := by
    simp [CompactBJRModel.fieldGraphWeightIntegrand,
      CompactBJRModel.zeroTreeVertexFactor]
  rw [hbase, M.zeroTree_vertex_factors_partition H x,
    M.zeroTree_edge_factors_root_kernel_partition H x]
  unfold CompactBJRModel.rootlessBlockWeightIntegrand
  rw [Finset.prod_mul_distrib]
  ring


end PerronWright


