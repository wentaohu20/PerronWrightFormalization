import PerronWright.Probability.BrownianKilledGreenBoundary

/-! # A uniform weighted bound for the actual killed Green kernel

The pointwise exponential-gap estimate bounds the inserted positive
state times the genuine zeroth resolvent. The constant is finite and
depends only on the Laplace parameter and initial state.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianKilledGreenWeightedBound

open BrownianKilledAreaMomentResolvent BrownianKilledGreenKernel BrownianKilledGreenBoundary

theorem mul_exp_neg_mul_le_inv (s : ℝ) (hs : 0 < s) (r : ℝ) :
    r*Real.exp (-r*s) ≤ 1/s := by
  apply (le_div_iff₀ hs).mpr
  have he : s*r ≤ Real.exp (s*r) := by linarith [Real.add_one_le_exp (s*r)]
  calc
    _ = (s*r)*Real.exp (-r*s) := by ring
    _ ≤ Real.exp (s*r)*Real.exp (-r*s) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = 1 := by
      rw [← Real.exp_add,show s*r+ -r*s = 0 by ring,Real.exp_zero]

theorem greenReal_mul_target_le (p : ℝ) (hp : 0 < p) (x z : ℝ) (hz : 0 ≤ z) :
    greenReal p x z*z ≤ (|x|+1/Real.sqrt (2*p))/Real.sqrt (2*p) := by
  have hs : 0 < Real.sqrt (2*p) := Real.sqrt_pos.mpr (by positivity)
  have hzbound : z ≤ |x|+|z-x| := by
    have h := abs_add_le (z-x) x
    rw [sub_add_cancel,abs_of_nonneg hz] at h
    simpa only [add_comm] using h
  have he : Real.exp (-|z-x| * Real.sqrt (2*p)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (abs_nonneg _)) (Real.sqrt_nonneg _))
  have hb : (|x|+|z-x|)*Real.exp (-|z-x| * Real.sqrt (2*p)) ≤
      |x|+1/Real.sqrt (2*p) := by
    rw [add_mul]
    have hfirst : |x| * Real.exp (-|z-x| * Real.sqrt (2*p)) ≤ |x| :=
      (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans_eq (mul_one _)
    exact add_le_add hfirst (mul_exp_neg_mul_le_inv (Real.sqrt (2*p)) hs |z-x|)
  calc
    _ ≤ Real.exp (-|z-x| * Real.sqrt (2*p))/Real.sqrt (2*p)*z :=
      mul_le_mul_of_nonneg_right (greenReal_le_exp_gap p x z) hz
    _ ≤ (|x|+|z-x|)*Real.exp (-|z-x| * Real.sqrt (2*p))/Real.sqrt (2*p) := by
      have hh := mul_le_mul_of_nonneg_left hzbound
        (div_nonneg (Real.exp_pos (-|z-x| * Real.sqrt (2*p))).le hs.le)
      exact hh.trans_eq (by ring)
    _ ≤ _ := div_le_div_of_nonneg_right hb hs.le

theorem actual_resolvent_mul_target_le (p : ℝ) (hp : 0 < p) (x z : ℝ) :
    resolvent 0 p x z*ENNReal.ofReal z ≤
      ENNReal.ofReal ((|x|+1/Real.sqrt (2*p))/Real.sqrt (2*p)) := by
  by_cases hz : 0 < z
  · by_cases hx : 0 < x
    · rw [resolvent_zero_eq_green p hp x z hx hz,
        ← ENNReal.ofReal_mul (greenReal_nonneg p x z hx hz)]
      exact ENNReal.ofReal_le_ofReal (greenReal_mul_target_le p hp x z hz.le)
    · rw [resolvent_zero_of_nonpos_initial 0 p x z (le_of_not_gt hx),zero_mul]
      exact zero_le
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hz),mul_zero]
    exact zero_le

end PerronWright.BrownianKilledGreenWeightedBound
