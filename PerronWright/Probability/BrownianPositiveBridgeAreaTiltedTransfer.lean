import PerronWright.Probability.BrownianPositiveBridgeAreaExponentialTails
import PerronWright.Probability.WeakContinuousSquareIntegralTransfer
import PerronWright.Probability.BrownianEntranceAreaWrightMoments
import Mathlib.MeasureTheory.Measure.Tilted

/-! # Actual exponential area tilts converge to the entrance-area tilt

The square bound is derived from the proved Brownian Gaussian-square
estimate. Thus continuous unbounded weighted tests, normalizers and actual
tilted measure integrals converge without an exponential-integrability
assumption. Literal all-order Wright moment limits are also recorded.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianPositiveBridgeAreaTiltedTransfer

open BrownianPathLaw BrownianBridgeCyclicArea BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeAreaExponentialSquare BrownianPositiveBridgeAreaFactorialGrowth
open BrownianPositiveBridgeAreaExponentialTails BrownianPositiveBridgePathConvergence
open BrownianPositiveBridgeWeakClusterSupport BrownianPositiveBridgeAreaLawIdentification
open WeakContinuousSquareIntegralTransfer ContinuousPathAreaContinuity
open BrownianPositiveBridgeAreaMomentLimits BrownianEntranceAreaWrightMoments
open PerronWrightFormulaMainTerm

private theorem weighted_test_square_pointwise (c u x : ℝ) (hc : 0 < c) (Φ : ℝ →ᵇ ℝ) :
    (Real.exp (u*x)*Φ x)^2 ≤
      (‖Φ‖^2*Real.exp (u^2/c))*Real.exp (c*x^2) := by
  have hs : (Φ x)^2 ≤ ‖Φ‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      pow_le_pow_left₀ (norm_nonneg (Φ x)) (Φ.norm_coe_le_norm x) 2
  have he : (Real.exp (u*x))^2 = Real.exp (2*u*x) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [mul_pow,he]
  calc
    _ ≤ Real.exp (2*u*x)*‖Φ‖^2 :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ ≤ (Real.exp (u^2/c)*Real.exp (c*x^2))*‖Φ‖^2 :=
      mul_le_mul_of_nonneg_right (exponential_linear_square_bound c u x hc) (sq_nonneg _)
    _ = _ := by ring

theorem eventually_uniform_weighted_area_square_bound (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (Φ : ℝ →ᵇ ℝ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ f : Path, ENNReal.ofReal ((Real.exp (u*pathArea T f)*Φ (pathArea T f))^2)
        ∂(bridgeProbability T hT a : Measure Path)) ≤
      ENNReal.ofReal ((‖Φ‖^2*Real.exp (u^2/areaSquareParameter T))*(4*areaGrowthConstant T)) := by
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_area_exp_square_bound T hT] with a ha hb
  rw [bridgeProbability_toMeasure T hT a ha]
  let K := ‖Φ‖^2*Real.exp (u^2/areaSquareParameter T)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    _ ≤ ∫⁻ f : Path, ENNReal.ofReal K*
        ENNReal.ofReal (Real.exp (areaSquareParameter T*pathArea T f^2)) ∂positiveBridgeLaw a T := by
      apply lintegral_mono
      intro f
      dsimp only
      rw [← ENNReal.ofReal_mul hK]
      exact ENNReal.ofReal_le_ofReal
        (weighted_test_square_pointwise _ u _ (areaSquareParameter_pos T) Φ)
    _ = ENNReal.ofReal K*(∫⁻ f : Path, ENNReal.ofReal
        (Real.exp (areaSquareParameter T*pathArea T f^2)) ∂positiveBridgeLaw a T) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K*ENNReal.ofReal (4*areaGrowthConstant T) := mul_le_mul' le_rfl hb
    _ = _ := (ENNReal.ofReal_mul hK).symm

theorem actual_weighted_area_test_tendsto (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (Φ : ℝ →ᵇ ℝ) :
    Tendsto (fun a : ℝ ↦ ∫ f : Path, Real.exp (u*pathArea T f)*Φ (pathArea T f)
      ∂positiveBridgeLaw a T) (𝓝[>] 0)
      (𝓝 (∫ f : Path, Real.exp (u*pathArea T f)*Φ (pathArea T f)
        ∂BrownianEntranceContinuousRealization.pathLaw T hT)) := by
  have h := tendsto_integral_of_uniform_square_bound
    (bridgeProbability T hT) (entranceProbability T hT) (tendsto_positiveBridgeProbability T hT)
    (fun f ↦ Real.exp (u*pathArea T f)*Φ (pathArea T f))
    ((Real.continuous_exp.comp ((continuous_pathArea T).const_mul u)).mul
      (Φ.continuous.comp (continuous_pathArea T)))
    ((‖Φ‖^2*Real.exp (u^2/areaSquareParameter T))*(4*areaGrowthConstant T))
    (by have := areaGrowthConstant_ge_one T; positivity)
    (eventually_uniform_weighted_area_square_bound T hT u Φ)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [bridgeProbability_toMeasure T hT a ha]

theorem actual_area_exp_normalizer_tendsto (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    Tendsto (fun a : ℝ ↦ ∫ f : Path, Real.exp (u*pathArea T f) ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (∫ f : Path, Real.exp (u*pathArea T f)
        ∂BrownianEntranceContinuousRealization.pathLaw T hT)) := by
  simpa only [BoundedContinuousFunction.const_apply',mul_one] using
    actual_weighted_area_test_tendsto T hT u (BoundedContinuousFunction.const ℝ 1)

theorem entrance_area_exp_normalizer_pos (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    0 < ∫ f : Path, Real.exp (u*pathArea T f)
      ∂BrownianEntranceContinuousRealization.pathLaw T hT := by
  let := BrownianEntranceContinuousRealization.pathLaw_isProbability T hT
  exact integral_exp_pos (entrance_area_exp_integrable T hT u)

theorem eventually_actual_area_tilt_isProbability (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      IsProbabilityMeasure ((positiveBridgeLaw a T).tilted (fun f ↦ u*pathArea T f)) := by
  filter_upwards [self_mem_nhdsWithin,eventually_area_exp_integrable T hT u] with a ha hb
  let := positiveBridgeLaw_isProbability a ha T hT
  exact isProbabilityMeasure_tilted hb

theorem entrance_area_tilt_isProbability (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    IsProbabilityMeasure ((BrownianEntranceContinuousRealization.pathLaw T hT).tilted
      (fun f ↦ u*pathArea T f)) := by
  let := BrownianEntranceContinuousRealization.pathLaw_isProbability T hT
  exact isProbabilityMeasure_tilted (entrance_area_exp_integrable T hT u)

private theorem integral_tilted_area_test (T : ℝ≥0) (u : ℝ) (Φ : ℝ →ᵇ ℝ) (μ : Measure Path) :
    (∫ f, Φ (pathArea T f) ∂μ.tilted (fun f ↦ u*pathArea T f)) =
      (∫ f, Real.exp (u*pathArea T f)*Φ (pathArea T f) ∂μ)/
        (∫ f, Real.exp (u*pathArea T f) ∂μ) := by
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div]
  exact integral_div _ _

theorem actual_tilted_area_test_integral_tendsto (T : ℝ≥0) (hT : 0 < T)
    (u : ℝ) (Φ : ℝ →ᵇ ℝ) :
    Tendsto (fun a : ℝ ↦ ∫ f : Path, Φ (pathArea T f)
      ∂(positiveBridgeLaw a T).tilted (fun f ↦ u*pathArea T f)) (𝓝[>] 0)
      (𝓝 (∫ f : Path, Φ (pathArea T f)
        ∂(BrownianEntranceContinuousRealization.pathLaw T hT).tilted
          (fun f ↦ u*pathArea T f))) := by
  simp_rw [integral_tilted_area_test]
  exact (actual_weighted_area_test_tendsto T hT u Φ).div
    (actual_area_exp_normalizer_tendsto T hT u) (entrance_area_exp_normalizer_pos T hT u).ne'

theorem actual_area_real_moment_tendsto_wrightConstant (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    Tendsto (fun a : ℝ ↦ ∫ f : Path, pathArea T f^n ∂positiveBridgeLaw a T) (𝓝[>] 0)
      (𝓝 (((T : ℝ)^(3/2 : ℝ))^n*(n.factorial : ℝ)*wrightConstant n)) := by
  rw [← entranceAreaMoment_duration_eq_wrightConstant T hT n]
  exact actual_area_real_moment_tendsto T hT n

theorem actual_entrance_area_real_moment_eq_wrightConstant (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ f : Path, pathArea T f^n ∂BrownianEntranceContinuousRealization.pathLaw T hT) =
      ((T : ℝ)^(3/2 : ℝ))^n*(n.factorial : ℝ)*wrightConstant n := by
  rw [entrance_area_real_moment_eq_time_kernel_integral,
    entranceAreaMoment_duration_eq_wrightConstant T hT n]

end PerronWright.BrownianPositiveBridgeAreaTiltedTransfer
