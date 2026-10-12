import PerronWright.Probability.BrownianSubquadraticGrowth

/-!
# Genuine Brownian parabolic drift tends to minus infinity

The almost-sure statement uses the proved full-horizon subquadratic
growth of the actual continuous Gaussian construction. One full-measure
set works for every drift parameter, without a tail-growth assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.BrownianFullHorizonDrift

open BrownianGaussianSkeleton BrownianContinuousModification BrownianSubquadraticGrowth

theorem tendsto_nnreal_coe_atTop :
    Tendsto (fun t : ℝ≥0 ↦ (t : ℝ)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (NNReal.mk (max b 0) (le_max_right _ _))] with t ht
  exact (le_max_left b 0).trans ht

theorem parabolic_div_sq_tendsto {f : ℝ≥0 → ℝ}
    (hf : Tendsto (fun t : ℝ≥0 ↦ f t / (t : ℝ)^2) atTop (𝓝 0)) (lambda : ℝ) :
    Tendsto (fun t : ℝ≥0 ↦
      (f t + lambda * (t : ℝ) - (t : ℝ)^2 / 2) / (t : ℝ)^2)
      atTop (𝓝 (-1/2 : ℝ)) := by
  have hi := tendsto_inv_atTop_zero.comp tendsto_nnreal_coe_atTop
  have h := (hf.add (hi.const_mul lambda)).sub_const (1/2 : ℝ)
  simp only [mul_zero, add_zero, zero_sub] at h
  rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by ring]
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with t ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht
  simp only [Function.comp_def]
  field_simp [htpos.ne']

theorem parabolic_tendsto_atBot {f : ℝ≥0 → ℝ}
    (hf : Tendsto (fun t : ℝ≥0 ↦ f t / (t : ℝ)^2) atTop (𝓝 0)) (lambda : ℝ) :
    Tendsto (fun t : ℝ≥0 ↦ f t + lambda * (t : ℝ) - (t : ℝ)^2 / 2)
      atTop atBot := by
  have hratio := (parabolic_div_sq_tendsto hf lambda).eventually
    (Iio_mem_nhds (by norm_num : (-1/2 : ℝ) < -1/4))
  have hsquare : Tendsto (fun t : ℝ≥0 ↦ (t : ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_nnreal_coe_atTop
  apply tendsto_atBot.mpr
  intro b
  filter_upwards [hratio, hsquare.eventually (eventually_ge_atTop (-4*b)),
    eventually_ge_atTop (1 : ℝ≥0)] with t hr hb ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht
  have h := (div_lt_iff₀ (sq_pos_of_pos htpos)).mp hr
  nlinarith

theorem ae_all_parameter_drift_div_sq :
    ∀ᵐ x ∂rationalLaw, ∀ lambda : ℝ,
      Tendsto (fun t : ℝ≥0 ↦ BrownianParabolicReflection.drift lambda t x / (t : ℝ)^2)
        atTop (𝓝 (-1/2 : ℝ)) := by
  filter_upwards [ae_subquadratic_process] with x hx
  intro lambda
  exact parabolic_div_sq_tendsto hx lambda

theorem ae_all_parameter_drift_tendsto_atBot :
    ∀ᵐ x ∂rationalLaw, ∀ lambda : ℝ,
      Tendsto (fun t : ℝ≥0 ↦ BrownianParabolicReflection.drift lambda t x) atTop atBot := by
  filter_upwards [ae_subquadratic_process] with x hx
  intro lambda
  exact parabolic_tendsto_atBot hx lambda

theorem ae_all_parameter_continuous_drift_atBot :
    ∀ᵐ x ∂rationalLaw, ∀ lambda : ℝ,
      Continuous (fun t : ℝ≥0 ↦ BrownianParabolicReflection.drift lambda t x) ∧
      Tendsto (fun t : ℝ≥0 ↦ BrownianParabolicReflection.drift lambda t x) atTop atBot := by
  filter_upwards [ae_all_parameter_drift_tendsto_atBot, ae_continuous_process] with x hx hc
  intro lambda
  exact ⟨ContinuousPathReflection.continuous_parabolicDrift hc lambda, hx lambda⟩

end PerronWright.BrownianFullHorizonDrift
