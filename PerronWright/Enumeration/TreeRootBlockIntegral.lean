import PerronWright.Enumeration.TreeRootIntegrandFactor
import PerronWright.Enumeration.TreePartitionIntegral

/-!
# Root-block product integral for actual finite graph weights

After the root is fixed, each factor of the zero-field weight belongs to a
unique block of the graph with the root deleted. This file includes the root
edge kernels in the block factors, proves their locality, and applies the
finite-partition product-measure theorem to factor the genuine graph integral.
The result holds for any finite graph; tree structure is needed only in the
later combinatorial sum over labelled rooted trees.
-/

open MeasureTheory
open scoped Classical

namespace PerronWright

theorem CompactBJRModel.rootlessBlockWeightIntegrand_congr_on
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (B : Finset (Fin n)) (x y : Fin (n + 1) → S)
    (hxy : ∀ i ∈ B, x i.succ = y i.succ) :
    M.rootlessBlockWeightIntegrand H B x =
      M.rootlessBlockWeightIntegrand H B y := by
  unfold CompactBJRModel.rootlessBlockWeightIntegrand
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hxy i hi]
  · apply Finset.prod_congr rfl
    intro e he
    have h1 : e.out.1 ∈ B := (Finset.mem_filter.mp he).2.1
    have h2 : e.out.2 ∈ B := (Finset.mem_filter.mp he).2.2
    rw [← e.out_eq]
    change M.edgeFactor 1 (fun i => x i.succ) s(e.out.1, e.out.2) =
      M.edgeFactor 1 (fun i => y i.succ) s(e.out.1, e.out.2)
    simp only [CompactBJRModel.edgeFactor_mk, one_mul]
    rw [hxy e.out.1 h1, hxy e.out.2 h2]

theorem CompactBJRModel.zeroTree_root_kernel_factors_partition
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (x : Fin (n + 1) → S) :
    (∏ j ∈ H.neighborFinset 0, M.kernel (x 0) (x j)) =
      ∏ B ∈ (finRootlessPartition n H).parts,
        ∏ i ∈ B, if H.Adj 0 i.succ then
          M.kernel (x 0) (x i.succ) else 1 := by
  classical
  calc
    _ = ∏ j : Fin (n + 1),
        if H.Adj 0 j then M.kernel (x 0) (x j) else 1 := by
      rw [H.neighborFinset_eq_filter, Finset.prod_filter]
    _ = ∏ i : Fin n,
        if H.Adj 0 i.succ then M.kernel (x 0) (x i.succ) else 1 := by
      rw [Fin.prod_univ_succ]
      simp only [H.irrefl, ↓reduceIte, one_mul]
    _ = _ := finpartition_prod_univ (finRootlessPartition n H) _

noncomputable def CompactBJRModel.rootBlockWeightIntegrand
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (B : Finset (Fin n)) (x : Fin (n + 1) → S) : ℝ :=
  (∏ i ∈ B, if H.Adj 0 i.succ then
    M.kernel (x 0) (x i.succ) else 1) *
    M.rootlessBlockWeightIntegrand H B x

theorem CompactBJRModel.zeroTree_integrand_root_block_partition
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (x : Fin (n + 1) → S) :
    M.fieldGraphWeightIntegrand 0 H x =
      M.zeroTreeVertexFactor (x 0) *
        ∏ B ∈ (finRootlessPartition n H).parts,
          M.rootBlockWeightIntegrand H B x := by
  rw [M.zeroTree_integrand_root_partition H x,
    M.zeroTree_root_kernel_factors_partition H x]
  simp only [CompactBJRModel.rootBlockWeightIntegrand]
  rw [Finset.prod_mul_distrib]
  ring

theorem CompactBJRModel.rootBlockWeightIntegrand_congr_on
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (B : Finset (Fin n)) (x y : Fin (n + 1) → S)
    (hroot : x 0 = y 0)
    (hxy : ∀ i ∈ B, x i.succ = y i.succ) :
    M.rootBlockWeightIntegrand H B x =
      M.rootBlockWeightIntegrand H B y := by
  unfold CompactBJRModel.rootBlockWeightIntegrand
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hroot, hxy i hi]
  · exact M.rootlessBlockWeightIntegrand_congr_on H B x y hxy

def extendBlock {ι S : Type*} [DecidableEq ι]
    (B : Finset ι) (root : S) (y : B → S) : ι → S :=
  fun i => if h : i ∈ B then y ⟨i, h⟩ else root

theorem CompactBJRModel.rootBlockWeightIntegrand_eq_local
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1)))
    (B : Finset (Fin n)) (root : S) (z : Fin n → S) :
    M.rootBlockWeightIntegrand H B (Fin.cons root z) =
      M.rootBlockWeightIntegrand H B
        (Fin.cons root (extendBlock B root (fun i => z i.1))) := by
  classical
  apply M.rootBlockWeightIntegrand_congr_on H B
  · simp only [Fin.cons_zero]
  · intro i hi
    simp only [Fin.cons_succ, extendBlock, dif_pos hi]

set_option linter.style.haveILetI false in
theorem CompactBJRModel.zeroTree_integral_root_block_partition
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (root : S) :
    (∫ z : Fin n → S,
      M.fieldGraphWeightIntegrand 0 H (Fin.cons root z)
        ∂Measure.pi (fun _ : Fin n => M.mu)) =
      M.zeroTreeVertexFactor root *
        ∏ B : (finRootlessPartition n H).parts,
          ∫ y : B.1 → S,
            M.rootBlockWeightIntegrand H B.1
              (Fin.cons root (extendBlock B.1 root y))
              ∂Measure.pi (fun _ : B.1 => M.mu) := by
  classical
  letI : DecidableEq (Fin n) := instDecidableEqFin n
  let P := finRootlessPartition n H
  let F : (B : P.parts) → (B.1 → S) → ℝ :=
    fun B y => M.rootBlockWeightIntegrand H B.1
      (Fin.cons root (extendBlock B.1 root y))
  have hpoint (z : Fin n → S) :
      M.fieldGraphWeightIntegrand 0 H (Fin.cons root z) =
        M.zeroTreeVertexFactor root *
          ∏ B : P.parts, F B (fun i => z i.1) := by
    rw [M.zeroTree_integrand_root_block_partition H (Fin.cons root z)]
    simp only [Fin.cons_zero]
    congr 1
    rw [Finset.prod_subtype P.parts (fun B => Iff.rfl)
      (fun B => M.rootBlockWeightIntegrand H B (Fin.cons root z))]
    apply Finset.prod_congr rfl
    intro B _
    exact M.rootBlockWeightIntegrand_eq_local H B.1 root z
  calc
    _ = ∫ z : Fin n → S,
        M.zeroTreeVertexFactor root * ∏ B : P.parts, F B (fun i => z i.1)
          ∂Measure.pi (fun _ : Fin n => M.mu) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = M.zeroTreeVertexFactor root *
        ∫ z : Fin n → S, ∏ B : P.parts, F B (fun i => z i.1)
          ∂Measure.pi (fun _ : Fin n => M.mu) := by
      rw [integral_const_mul]
    _ = _ := by
      congr 1
      exact integral_finpartition_prod_eq_prod (ι := Fin n) (S := S) P M.mu F

end PerronWright
