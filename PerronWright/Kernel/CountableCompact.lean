import PerronWright.Kernel.CountableIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Compactness by finite output-coordinate truncation

The type space itself is not compact.  The constructed operator has a
uniform pointwise bound, so its omitted output coordinates have small
`L²(μ)` norm when the atomic measure of the omitted tail is small.
-/

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace PerronWright.CountableKernel

theorem coe_add_at (M : CountableKernel) (v w : M.L2) (a : ℕ) :
    (v + w) a = v a + w a :=
  M.forall_of_ae (Lp.coeFn_add v w) a

theorem coe_smul_at (M : CountableKernel) (c : ℝ) (v : M.L2) (a : ℕ) :
    (c • v) a = c * v a :=
  M.forall_of_ae (Lp.coeFn_smul c v) a

theorem coe_sum_at (M : CountableKernel) (f : ℕ → M.L2) (s : Finset ℕ) (a : ℕ) :
    (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, M.coe_add_at, ih]

def atomVector (M : CountableKernel) (a : ℕ) : M.L2 :=
  indicatorConstLp 2 (measurableSet_singleton a) (measure_ne_top M.mu {a}) (1 : ℝ)

theorem atomVector_apply (M : CountableKernel) (a b : ℕ) :
    M.atomVector a b = if b = a then 1 else 0 := by
  have h := M.forall_of_ae (indicatorConstLp_coeFn
    (p := 2) (hs := measurableSet_singleton a) (hμs := measure_ne_top M.mu {a}) (c := (1 : ℝ))) b
  simpa [atomVector, Set.indicator_apply] using h

def coordinateOutput (M : CountableKernel) (a : ℕ) : M.L2 →L[ℝ] M.L2 :=
  (innerSL ℝ (M.row a)).smulRight (M.atomVector a)

theorem isCompactOperator_coordinateOutput (M : CountableKernel) (a : ℕ) :
    IsCompactOperator (M.coordinateOutput a) := by
  have hi : IsCompactOperator (innerSL ℝ (M.row a)) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact hi.clm_comp (ContinuousLinearMap.toSpanSingleton ℝ (M.atomVector a))

def outputTruncation (M : CountableKernel) (N : ℕ) : M.L2 →L[ℝ] M.L2 :=
  ∑ a ∈ Finset.range N, M.coordinateOutput a

theorem isCompactOperator_outputTruncation (M : CountableKernel) (N : ℕ) :
    IsCompactOperator (M.outputTruncation N) := by
  unfold outputTruncation
  induction N with
  | zero => simpa using (isCompactOperator_zero : IsCompactOperator (0 : M.L2 →L[ℝ] M.L2))
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact ih.add (M.isCompactOperator_coordinateOutput N)

theorem outputTruncation_apply (M : CountableKernel) (N : ℕ) (v : M.L2) (a : ℕ) :
    M.outputTruncation N v a = if a < N then M.pointwiseAction v a else 0 := by
  classical
  rw [outputTruncation, sum_apply, M.coe_sum_at]
  simp only [coordinateOutput, ContinuousLinearMap.smulRight_apply,
    M.coe_smul_at, M.atomVector_apply]
  simp [Finset.mem_range, pointwiseAction]

def tailVector (M : CountableKernel) (N : ℕ) : M.L2 :=
  indicatorConstLp 2 (measurableSet_Ici : MeasurableSet (Set.Ici N))
    (measure_ne_top M.mu (Set.Ici N)) (1 : ℝ)

theorem tailVector_apply (M : CountableKernel) (N a : ℕ) :
    M.tailVector N a = if N ≤ a then 1 else 0 := by
  have h := M.forall_of_ae (indicatorConstLp_coeFn (p := 2)
    (hs := (measurableSet_Ici : MeasurableSet (Set.Ici N)))
    (hμs := measure_ne_top M.mu (Set.Ici N)) (c := (1 : ℝ))) a
  simpa [tailVector, Set.indicator_apply] using h

theorem norm_action_sub_outputTruncation_le (M : CountableKernel) (N : ℕ) (v : M.L2) :
    ‖(M.actionCLM - M.outputTruncation N) v‖ ≤
      (M.upper * ‖M.tailVector N‖) * ‖v‖ := by
  have hb : ∀ᵐ a ∂M.mu,
      ‖(M.actionCLM - M.outputTruncation N) v a‖ ≤
        (M.upper * ‖v‖) * ‖M.tailVector N a‖ := by
    filter_upwards [Lp.coeFn_sub (M.actionCLM v) (M.outputTruncation N v)] with a ha
    change ‖(M.actionCLM v - M.outputTruncation N v) a‖ ≤ _
    rw [ha, Pi.sub_apply, M.outputTruncation_apply, M.tailVector_apply]
    have hact : M.actionCLM v a = M.pointwiseAction v a := M.forall_of_ae (M.action_coe_ae v) a
    rw [hact]
    by_cases h : a < N
    · simp [h, Nat.not_le.mpr h]
    · simpa [h, Nat.le_of_not_gt h] using M.norm_pointwiseAction_le v a
  have hn := Lp.norm_le_mul_norm_of_ae_le_mul hb
  calc
    ‖(M.actionCLM - M.outputTruncation N) v‖ ≤
        (M.upper * ‖v‖) * ‖M.tailVector N‖ := hn
    _ = (M.upper * ‖M.tailVector N‖) * ‖v‖ := by ring

theorem norm_actionCLM_sub_outputTruncation_le (M : CountableKernel) (N : ℕ) :
    ‖M.actionCLM - M.outputTruncation N‖ ≤ M.upper * ‖M.tailVector N‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg M.upper_nonneg (norm_nonneg _))
    (M.norm_action_sub_outputTruncation_le N)

theorem norm_tailVector (M : CountableKernel) (N : ℕ) :
    ‖M.tailVector N‖ = (M.mu (Set.Ici N)).toReal ^ (1 / 2 : ℝ) := by
  simpa [tailVector, measureReal_def] using
    (norm_indicatorConstLp (p := (2 : ℝ≥0∞))
      (hs := (measurableSet_Ici : MeasurableSet (Set.Ici N)))
      (hμs := measure_ne_top M.mu (Set.Ici N)) (c := (1 : ℝ))
      (by norm_num) (by norm_num))

theorem tendsto_tail_measure (M : CountableKernel) :
    Filter.Tendsto (fun N : ℕ ↦ M.mu (Set.Ici N)) Filter.atTop (nhds 0) := by
  have hm : Antitone (fun N : ℕ ↦ Set.Ici N) := fun i j hij a ha ↦ hij.trans ha
  have h := tendsto_measure_iInter_atTop (μ := M.mu)
    (fun N : ℕ ↦ measurableSet_Ici.nullMeasurableSet) hm ⟨0, measure_ne_top M.mu _⟩
  have he : (⋂ N : ℕ, Set.Ici N) = ∅ := by
    ext a
    simp only [Set.mem_iInter, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
    exact fun h ↦ Nat.not_succ_le_self a (h (a + 1))
  simpa [Function.comp_def, he] using h

theorem tendsto_norm_tailVector (M : CountableKernel) :
    Filter.Tendsto (fun N : ℕ ↦ ‖M.tailVector N‖) Filter.atTop (nhds 0) := by
  have ht := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp
    M.tendsto_tail_measure
  have hp := (Real.continuous_rpow_const (by norm_num : 0 ≤ (1 / 2 : ℝ))).continuousAt.tendsto.comp ht
  simpa [M.norm_tailVector, Function.comp_def] using hp

theorem outputTruncation_tendsto (M : CountableKernel) :
    Filter.Tendsto (M.outputTruncation) Filter.atTop (nhds M.actionCLM) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hu := M.tendsto_norm_tailVector.const_mul M.upper
  apply squeeze_zero (fun N ↦ norm_nonneg _)
    (fun N ↦ ?_) (by simpa using hu)
  rw [norm_sub_rev]
  exact M.norm_actionCLM_sub_outputTruncation_le N

/-- Compactness is derived from the literal countable kernel data. -/
theorem isCompactOperator_actionCLM (M : CountableKernel) : IsCompactOperator M.actionCLM :=
  isCompactOperator_of_tendsto M.outputTruncation_tendsto
    (Filter.Eventually.of_forall M.isCompactOperator_outputTruncation)

end PerronWright.CountableKernel
