import PerronWright.Probability.AnnealedResidualCumulantExpansion
import PerronWright.Analysis.FinitePopulationLog

/-!
# Vanishing error for the actual critical-scale residual expansion

The edge bound is proved from the embedded component graphs.  The
finite-n cumulant envelope consequently vanishes on the critical size
scale; no residual expectation asymptotic is assumed here.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedResidualCriticalError

open AnnealedGraph ComponentBlocks ExactFactorialExpectation SelectedConfiguration
  AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
  AnnealedTupleResidualConnectedLawGraphTuple FreshTypeCumulantExpansion
  AnnealedResidualCumulantExpansion

def blockEmbedding {n q : ℕ} {k : Fin q → ℕ} (f : Placements n k)
    (i : Fin q) : Fin (k i) ↪ Fin n where
  toFun a := f ⟨i,a⟩
  inj' := by
    intro a b h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (f.injective h)).2

/-- No edge is created by embedding the prescribed component graphs. -/
theorem tupleGraph_edge_card_le_sum {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) :
    (tupleGraph f H).edgeFinset.card ≤ ∑ i, (H i).edgeFinset.card := by
  have hsub : (tupleGraph f H).edgeFinset ⊆
      Finset.univ.biUnion (fun i ↦ ((H i).map (blockEmbedding f i)).edgeFinset) := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨i,a,b,hab,ha,hb⟩ := (SimpleGraph.mem_edgeFinset).mp he
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,?_⟩
      apply SimpleGraph.mem_edgeFinset.mpr
      refine ⟨(tupleGraph f H).ne_of_adj ⟨i,a,b,hab,ha,hb⟩,a,b,hab,?_,?_⟩
      · exact ha
      · exact hb
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i, ((H i).map (blockEmbedding f i)).edgeFinset.card := Finset.card_biUnion_le
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      convert SimpleGraph.card_edgeFinset_map (blockEmbedding f i) (H i) using 1
      congr 1
      ext e
      simp [SimpleGraph.edgeSet_map]

/-- Fixed surplus gives the actual linear edge bound, including trees. -/
theorem tupleGraph_edge_card_le_size_surplus {n q : ℕ} {k r : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) {R : ℕ}
    (hH : ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)) (hr : ∀ i, r i ≤ R) :
    (tupleGraph f H).edgeFinset.card ≤ (∑ i, k i) + q * R := by
  calc
    _ ≤ ∑ i, (H i).edgeFinset.card := tupleGraph_edge_card_le_sum f H
    _ ≤ ∑ i, (k i + R) := Finset.sum_le_sum (fun i _ ↦ by
      rw [(hH i).2]
      have := hr i
      omega)
    _ = _ := by simp [Finset.sum_add_distrib]

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

/-- A deterministic majorant of the proved logarithmic residual error. -/
def envelope (n K q R : ℕ) (W : ℝ) : ℝ :=
  9 * W ^ 4 * (K : ℝ) ^ 4 / (n : ℝ) ^ 3 + W * ((K : ℝ) + q * R) / n

theorem selectedErrorBound_le_envelope {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (H : GraphTuple k) {R : ℕ}
    (hH : ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)) (hr : ∀ i, r i ≤ R) :
    selectedErrorBound M t hk f H ≤
      envelope n (∑ i,k i) q R (T * ‖M.kernel.toContinuousMap‖) := by
  have htN : t * ‖M.kernel.toContinuousMap‖ ≤ T * ‖M.kernel.toContinuousMap‖ :=
    mul_le_mul_of_nonneg_right htT (norm_nonneg _)
  have ht0 : 0 ≤ t * ‖M.kernel.toContinuousMap‖ := mul_nonneg ht (norm_nonneg _)
  have hT0 : 0 ≤ T * ‖M.kernel.toContinuousMap‖ := ht0.trans htN
  have hcard : Fintype.card ↥(selectedUnion (blocksOfPlacement hk f)) = ∑ i,k i := by
    rw [Fintype.card_coe,selectedUnion_blocksOfPlacement_card]
  have he : ((tupleGraph f H).edgeFinset.card : ℝ) ≤ (∑ i,k i : ℕ) + q * R := by
    exact_mod_cast tupleGraph_edge_card_le_size_surplus f H hH hr
  unfold selectedErrorBound exposureBound envelope
  rw [hcard]
  have h1 : 9 * ((n - ∑ i,k i : ℕ) : ℝ) *
      (t * ((∑ i,k i : ℕ) : ℝ) * ‖M.kernel.toContinuousMap‖ / (n : ℝ)) ^ 4 ≤
      9 * (n : ℝ) *
      (T * ((∑ i,k i : ℕ) : ℝ) * ‖M.kernel.toContinuousMap‖ / (n : ℝ)) ^ 4 := by
    gcongr
    · exact_mod_cast Nat.sub_le n (∑ i,k i)
  have h2 : t * ‖M.kernel.toContinuousMap‖ * ((tupleGraph f H).edgeFinset.card : ℝ) /
      (n : ℝ) ≤ T * ‖M.kernel.toContinuousMap‖ * (((∑ i,k i : ℕ) : ℝ) + q * R) / n := by
    gcongr
  have hid : 9 * (n : ℝ) *
      (T * ((∑ i,k i : ℕ) : ℝ) * ‖M.kernel.toContinuousMap‖ / (n : ℝ)) ^ 4 =
      9 * (T * ‖M.kernel.toContinuousMap‖) ^ 4 * ((∑ i,k i : ℕ) : ℝ) ^ 4 /
        (n : ℝ) ^ 3 := by
    by_cases hn : n = 0
    · simp [hn]
    · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      field_simp
  rw [hid] at h1
  simpa only [mul_assoc] using add_le_add h1 h2

/-- The envelope vanishes for arbitrary bounded critical-scale sizes. -/
theorem envelope_tendsto_zero (N K : ℕ → ℕ) (q R : ℕ) (W : ℝ) (_hW : 0 ≤ W)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop) {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ᶠ m in atTop, (K m : ℝ) ≤ C * (N m : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun m ↦ envelope (N m) (K m) q R W) atTop (𝓝 0) := by
  have hp : Tendsto (fun m ↦ (N m : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      (tendsto_natCast_atTop_atTop.comp hNt)
  have h4 : Tendsto (fun m ↦ 2 * (K m : ℝ) ^ 4 / (N m : ℝ) ^ 3) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun m ↦ by positivity))
      (hsize.mono (fun m hm ↦ FinitePopulationLog.fourth_remainder_bound (hN m) hC hm))
    simpa only [mul_zero] using hp.const_mul (2 * C ^ 4)
  have hr := FinitePopulationLog.critical_size_ratio_tendsto_zero N K hN hNt hC hsize
  have hinv : Tendsto (fun m ↦ (N m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hNt)
  have hh := ((h4.const_mul (9 * W ^ 4 / 2)).add
    ((hr.add (hinv.const_mul ((q : ℝ) * R))).const_mul W))
  norm_num only [mul_zero,zero_add] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun m ↦ by unfold envelope; ring)

/-- The deterministic error of the actual selected residual tends to zero
uniformly in its type configuration and eligible bounded-surplus graphs. -/
theorem selectedErrorBound_tendsto_zero (M : CompactBJRModel S) (N : ℕ → ℕ)
    (q R : ℕ) (k r : ℕ → Fin q → ℕ) (hk : ∀ m i, 0 < k m i)
    (f : ∀ m, Placements (N m) (k m)) (H : ∀ m, GraphTuple (k m))
    (t : ℕ → ℝ) (T : ℝ) (ht : ∀ m, 0 ≤ t m) (hT : 0 ≤ T)
    (htT : ∀ᶠ m in atTop, t m ≤ T) (hN : ∀ m, 0 < N m)
    (hNt : Tendsto N atTop atTop) {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ᶠ m in atTop, (∑ i,k m i : ℕ) ≤ C * (N m : ℝ) ^ (2 / 3 : ℝ))
    (hH : ∀ m i, ConnectedTypeLaw.Eligible (r m i) (H m i))
    (hr : ∀ᶠ m in atTop, ∀ i, r m i ≤ R) :
    Tendsto (fun m ↦ selectedErrorBound M (t m) (hk m) (f m) (H m)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun m ↦ by
    unfold selectedErrorBound
    have := ht m
    positivity))
    ((htT.and hr).mono (fun m hm ↦ selectedErrorBound_le_envelope M (t m) T
      (ht m) hm.1 (hk m) (f m) (H m) (hH m) hm.2))
  exact envelope_tendsto_zero N (fun m ↦ ∑ i,k m i) q R
    (T * ‖M.kernel.toContinuousMap‖) (mul_nonneg hT (norm_nonneg _)) hN hNt hC hsize

end PerronWright.AnnealedResidualCriticalError
