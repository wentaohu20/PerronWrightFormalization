import PerronWright.Probability.BrownianPathFiniteReversal
import PerronWright.Probability.BrownianPathDilationLaw

/-! # A genuine continuous-path source for the free entrance identification

The source is the whole future of an actual Brownian path after its
earliest minimum on [0,1], rescaled by the actual remaining duration.
It includes the entire post-unit future, not merely a finite tuple.
No entrance or meander distribution identity is assumed here.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianMinimumFutureEntranceSource

open BrownianPathLaw ContinuousPathLeastMinimum BrownianPathDilationLaw

def remainingDuration (f : Path) : ℝ≥0 := 1-leastMinimizer 1 f

theorem measurable_remainingDuration : Measurable remainingDuration :=
  measurable_const.sub (measurable_leastMinimizer 1)

def unitMinimumFuture (f : Path) : Path :=
  ⟨fun t ↦ (f (leastMinimizer 1 f+remainingDuration f*t)-f (leastMinimizer 1 f))/
      Real.sqrt (remainingDuration f : ℝ),
    (((continuous_path f).comp (continuous_const.add (continuous_const.mul continuous_id))).sub
      continuous_const).div_const _⟩

theorem unitMinimumFuture_eval (f : Path) (t : ℝ≥0) :
    unitMinimumFuture f t =
      (f (leastMinimizer 1 f+remainingDuration f*t)-minimumValue 1 f)/
        Real.sqrt (remainingDuration f : ℝ) := by
  change (f (leastMinimizer 1 f+remainingDuration f*t)-f (leastMinimizer 1 f))/
    Real.sqrt (remainingDuration f : ℝ) = _
  rw [← leastMinimizer_value]

theorem measurable_unitMinimumFuture : Measurable unitMinimumFuture := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  apply measurable_pi_lambda
  intro q
  have ht : Measurable (fun f : Path ↦ leastMinimizer 1 f+
      remainingDuration f*BrownianGaussianSkeleton.rationalTimeReal q) :=
    (measurable_leastMinimizer 1).add (measurable_remainingDuration.mul_const _)
  have he := continuous_joint_eval.measurable.comp (measurable_id.prodMk ht)
  have hm := (continuous_minimumValue 1).measurable
  have hs := Real.continuous_sqrt.measurable.comp
    (NNReal.continuous_coe.measurable.comp measurable_remainingDuration)
  change Measurable (fun f : Path ↦ unitMinimumFuture f
    (BrownianGaussianSkeleton.rationalTimeReal q))
  simp only [unitMinimumFuture_eval]
  convert (he.sub hm).div hs using 1
  funext f
  rfl

theorem unitMinimumFuture_initial_zero (f : Path) : unitMinimumFuture f 0 = 0 := by
  rw [unitMinimumFuture_eval]
  simp only [mul_zero,add_zero,leastMinimizer_value,sub_self,zero_div]

theorem unitMinimumFuture_nonnegative_prefix (f : Path) (t : ℝ≥0) (ht : t ≤ 1) :
    0 ≤ unitMinimumFuture f t := by
  rw [unitMinimumFuture_eval]
  apply div_nonneg _ (Real.sqrt_nonneg _)
  apply sub_nonneg.mpr
  apply minimumValue_le
  have htime : leastMinimizer 1 f+remainingDuration f*t ≤
      leastMinimizer 1 f+remainingDuration f := by
    apply add_le_add le_rfl
    calc
      _ ≤ remainingDuration f*1 :=
        mul_le_mul_of_nonneg_left ht (show (0 : ℝ≥0) ≤ remainingDuration f from bot_le)
      _ = _ := mul_one _
  rw [remainingDuration,add_tsub_cancel_of_le (leastMinimizer_le_time 1 f)] at htime
  exact htime

theorem ae_remainingDuration_pos : ∀ᵐ f : Path ∂pathLaw, 0 < remainingDuration f := by
  filter_upwards [BrownianPathFiniteReversal.ae_leastMinimizer_interior 1 zero_lt_one] with f hf
  exact tsub_pos_iff_lt.mpr hf.2

def unitSourceLaw : Measure Path := pathLaw.map unitMinimumFuture

instance unitSourceLaw_isProbability : IsProbabilityMeasure unitSourceLaw :=
  Measure.isProbabilityMeasure_map measurable_unitMinimumFuture.aemeasurable

theorem ae_unitSourceLaw_initial_zero : ∀ᵐ g : Path ∂unitSourceLaw, g 0 = 0 := by
  apply (ae_map_iff measurable_unitMinimumFuture.aemeasurable
    (measurableSet_eq_fun (continuous_eval 0).measurable measurable_const)).mpr
  exact Eventually.of_forall unitMinimumFuture_initial_zero

theorem ae_unitSourceLaw_nonnegative_prefix :
    ∀ᵐ g : Path ∂unitSourceLaw, ∀ t : ℝ≥0, t ≤ 1 → 0 ≤ g t := by
  have hm : MeasurableSet {g : Path | ∀ t : ℝ≥0, t ≤ 1 → 0 ≤ g t} := by
    have hc (t : ℝ≥0) : IsClosed {g : Path | t ≤ 1 → 0 ≤ g t} := by
      by_cases ht : t ≤ 1
      · simpa only [ht,true_implies] using isClosed_le continuous_const (continuous_eval t)
      · simp only [ht,false_implies,Set.ofPred_true]
        exact isClosed_univ
    simpa only [Set.ofPred_forall] using (isClosed_iInter hc).measurableSet
  apply (ae_map_iff measurable_unitMinimumFuture.aemeasurable hm).mpr
  exact Eventually.of_forall unitMinimumFuture_nonnegative_prefix

end PerronWright.BrownianMinimumFutureEntranceSource
