import PerronWright.Probability.CriticalFloorWindow
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Order.DenselyOrdered

/-! # Actual bounded cell tests and their almost-everywhere continuity -/

open MeasureTheory Set Filter Topology
open scoped BigOperators Classical Topology

noncomputable section

namespace PerronWright.SizeCellIndicators

def cellWeight {q : ℕ} (J : Fin q → Set ℝ) (x : Fin q → ℝ) : ℝ :=
  ∏ i, (J i).indicator (fun _ ↦ (1 : ℝ)) (x i)

theorem cellWeight_eq {q : ℕ} (J : Fin q → Set ℝ) (x : Fin q → ℝ) :
    cellWeight J x = if ∀ i, x i ∈ J i then 1 else 0 := by
  by_cases h : ∀ i, x i ∈ J i
  · simp [cellWeight,h]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i,hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

theorem cellWeight_nonneg {q : ℕ} (J : Fin q → Set ℝ) (x : Fin q → ℝ) :
    0 ≤ cellWeight J x := by
  rw [cellWeight_eq]
  split_ifs <;> norm_num

theorem cellWeight_norm_le {q : ℕ} (J : Fin q → Set ℝ) (x : Fin q → ℝ) :
    ‖cellWeight J x‖ ≤ 1 := by
  rw [cellWeight_eq]
  split_ifs <;> norm_num

theorem measurable_cellWeight {q : ℕ} (J : Fin q → Set ℝ)
    (hJ : ∀ i, MeasurableSet (J i)) : Measurable (cellWeight J) := by
  apply Finset.measurable_prod
  intro i _
  exact (measurable_const.indicator (hJ i)).comp (measurable_pi_apply i)

theorem continuousAt_cellWeight {q : ℕ} (J : Fin q → Set ℝ) {x : Fin q → ℝ}
    (hx : ∀ i, x i ∉ frontier (J i)) : ContinuousAt (cellWeight J) x := by
  apply tendsto_finsetProd
  intro i _
  have hi : ContinuousAt ((J i).indicator (fun _ ↦ (1 : ℝ))) (x i) :=
    continuousOn_const.continuousAt_indicator (hx i)
  have he : ContinuousAt (fun y : Fin q → ℝ ↦ y i) x := (continuous_apply i).continuousAt
  exact ContinuousAt.comp (f := fun y : Fin q → ℝ ↦ y i) (x := x) hi he

theorem ae_continuousAt_cellWeight {q : ℕ} (J : Fin q → Set ℝ)
    (hJ : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0) :
    ∀ᵐ x ∂(volume : Measure (Fin q → ℝ)), ContinuousAt (cellWeight J) x := by
  have hi (i : Fin q) : ∀ᵐ x ∂(volume : Measure (Fin q → ℝ)), x i ∉ frontier (J i) := by
    apply compl_mem_ae_iff.mpr
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null (fun _ : Fin q ↦ (volume : Measure ℝ)) (hJ i)
  filter_upwards [Filter.eventually_all.mpr hi] with x hx
  exact continuousAt_cellWeight J hx

theorem volume_frontier_Icc (a b : ℝ) : volume (frontier (Set.Icc a b)) = 0 := by
  by_cases h : a ≤ b
  · rw [frontier_Icc h]
    exact ((Set.finite_singleton b).insert a).measure_zero volume
  · rw [Set.Icc_eq_empty_of_lt (lt_of_not_ge h)]
    simp

theorem volume_frontier_Ico (a b : ℝ) : volume (frontier (Set.Ico a b)) = 0 := by
  by_cases h : a < b
  · rw [frontier_Ico h]
    exact ((Set.finite_singleton b).insert a).measure_zero volume
  · rw [Set.Ico_eq_empty_of_le (le_of_not_gt h)]
    simp

theorem volume_frontier_Ioc (a b : ℝ) : volume (frontier (Set.Ioc a b)) = 0 := by
  by_cases h : a < b
  · rw [frontier_Ioc h]
    exact ((Set.finite_singleton b).insert a).measure_zero volume
  · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt h)]
    simp

theorem volume_frontier_Ioo (a b : ℝ) : volume (frontier (Set.Ioo a b)) = 0 := by
  by_cases h : a < b
  · rw [frontier_Ioo h]
    exact ((Set.finite_singleton b).insert a).measure_zero volume
  · rw [Set.Ioo_eq_empty_of_le (le_of_not_gt h)]
    simp

end PerronWright.SizeCellIndicators
