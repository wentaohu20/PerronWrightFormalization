import PerronWright.Probability.ContinuousPathLeastMinimum
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-! # Joint measurable earliest minimum on varying compact intervals

Scaling the actual interval by [0,1] makes the literal minimum jointly
continuous in both horizon and path. The prefix characterization then
proves joint measurability of the earliest minimizer, without uniqueness
or any measurable-selection assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.ContinuousPathMinimumScaling

open BrownianPathLaw ContinuousPathLeastMinimum

theorem minimumValue_eq_scaled_interval (T : ℝ≥0) (f : Path) :
    minimumValue T f = sInf ((fun u : ℝ≥0 ↦ f (T*u)) '' Icc 0 1) := by
  have he : (fun u : ℝ≥0 ↦ T*u) '' Icc 0 1 = Icc 0 T := by
    simpa only [mul_zero,mul_one] using image_mul_left_Icc (show 0 ≤ T from zero_le) (show (0 : ℝ≥0) ≤ 1 from zero_le)
  unfold minimumValue
  rw [← he,← image_comp]
  rfl

theorem continuous_joint_minimumValue :
    Continuous (fun p : ℝ≥0 × Path ↦ minimumValue p.1 p.2) := by
  have hc : Continuous (fun p : (ℝ≥0 × Path) × ℝ≥0 ↦ p.1.2 (p.1.1*p.2)) :=
    continuous_joint_eval.comp
      ((continuous_snd.comp continuous_fst).prodMk
        ((continuous_fst.comp continuous_fst).mul continuous_snd))
  have h := (isCompact_Icc (a := (0 : ℝ≥0)) (b := 1)).continuous_sInf
    (f := fun p : ℝ≥0 × Path ↦ fun u : ℝ≥0 ↦ p.2 (p.1*u)) hc
  exact h.congr (fun p ↦ (minimumValue_eq_scaled_interval p.1 p.2).symm)

theorem measurable_joint_leastMinimizer :
    Measurable (fun p : ℝ≥0 × Path ↦ leastMinimizer p.1 p.2) := by
  apply measurable_of_Iic
  intro a
  have he : (fun p : ℝ≥0 × Path ↦ leastMinimizer p.1 p.2) ⁻¹' Iic a =
      {p | minimumValue (min a p.1) p.2 = minimumValue p.1 p.2} := by
    ext p
    exact leastMinimizer_le_iff_prefix_minimum p.1 a p.2
  rw [he]
  have hp : Continuous (fun p : ℝ≥0 × Path ↦ minimumValue (min a p.1) p.2) :=
    continuous_joint_minimumValue.comp ((continuous_const.min continuous_fst).prodMk continuous_snd)
  exact (isClosed_eq hp continuous_joint_minimumValue).measurableSet

theorem measurable_joint_scaledLeastMinimizer :
    Measurable (fun p : ℝ≥0 × Path ↦ scaledLeastMinimizer p.1 p.2) :=
  measurable_joint_leastMinimizer.div measurable_fst

end PerronWright.ContinuousPathMinimumScaling
