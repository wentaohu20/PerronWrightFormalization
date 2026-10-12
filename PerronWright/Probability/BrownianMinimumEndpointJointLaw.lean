import PerronWright.Probability.BrownianMinimumEndpointTimeLimit
import PerronWright.Probability.BrownianMinimumEndpointTests

/-! # The actual minimum-time, minimum-depth and endpoint joint law

The genuine first-passage window limit and the genuine killed entrance
limit converge to the same integral. Uniqueness of limits therefore
identifies the literal Brownian minimum triple with its numerical
first-passage-times-entrance density. No joint-law premise is introduced.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumEndpointJointLaw

open BrownianPathLaw ContinuousPathFirstPassage ContinuousPathLeastMinimum
open BrownianFirstPassageEndpointGeometry BrownianMinimumEndpointLevelLimit
open BrownianMinimumEndpointTimeLimit BrownianMinimumEndpointTests
open BrownianKilledBoundaryEntrance

theorem remainingTime_eq_nnreal_sub (T : ℝ≥0) (s : ℝ)
    (hs : 0 ≤ s) (hsT : s ≤ (T : ℝ)) :
    remainingTime T s = T-Real.toNNReal s := by
  apply NNReal.eq
  rw [remainingTime,Real.coe_toNNReal _ (sub_nonneg.mpr hsT),
    NNReal.coe_sub (Real.toNNReal_le_iff_le_coe.mpr hsT),Real.coe_toNNReal _ hs]

theorem actual_window_eq_endpointKernel (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ s in Iio (T : ℝ),
      BrownianFirstPassageDensityGeometry.density a s *
        ∫⁻ g in survival (-δ) (remainingTime T s),
          ENNReal.ofReal (Φ (Real.toNNReal s,-a,g (T-Real.toNNReal s))) ∂pathLaw)/
      ENNReal.ofReal δ =
      ∫⁻ s in Ioo 0 (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*endpointKernel T Φ δ s a := by
  have hc : (ENNReal.ofReal δ)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hδ)
  have he (a : ℝ) :
      (∫⁻ s in Iio (T : ℝ), BrownianFirstPassageDensityGeometry.density a s *
        ∫⁻ g in survival (-δ) (remainingTime T s),
          ENNReal.ofReal (Φ (Real.toNNReal s,-a,g (T-Real.toNNReal s))) ∂pathLaw)/
        ENNReal.ofReal δ =
      ∫⁻ s in Ioo 0 (T : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*endpointKernel T Φ δ s a := by
    rw [div_eq_mul_inv,← lintegral_mul_const' _ _ hc]
    rw [show Ioo 0 (T : ℝ) = Ioi 0 ∩ Iio (T : ℝ) by ext s; simp only [mem_Ioo,mem_inter_iff,mem_Ioi,mem_Iio]]
    rw [← setLIntegral_indicator measurableSet_Ioi]
    apply setLIntegral_congr_fun measurableSet_Iio
    intro s hsT
    by_cases hs : 0 < s
    · rw [indicator_of_mem (show s ∈ Ioi 0 from hs)]
      dsimp only
      rw [remainingTime_eq_nnreal_sub T s hs.le hsT.le]
      simp only [endpointKernel,remainingTime_eq_nnreal_sub T s hs.le hsT.le,
        div_eq_mul_inv,mul_assoc]
    · have hd : BrownianFirstPassageDensityGeometry.density a s = 0 := by
        rw [BrownianFirstPassageDensityGeometry.density,
          BrownianFirstPassageDensityGeometry.densityReal_eq_zero_of_nonpos a s
            (le_of_not_gt hs),ENNReal.ofReal_zero]
      simp only [indicator_of_notMem (show s ∉ Ioi 0 from hs),hd,zero_mul]
  calc
    _ = ∫⁻ a in Ioi (0 : ℝ),
        (∫⁻ s in Iio (T : ℝ), BrownianFirstPassageDensityGeometry.density a s *
          ∫⁻ g in survival (-δ) (remainingTime T s),
            ENNReal.ofReal (Φ (Real.toNNReal s,-a,g (T-Real.toNNReal s))) ∂pathLaw)/
          ENNReal.ofReal δ := by
      simp only [div_eq_mul_inv]
      exact (lintegral_mul_const' _ _ hc).symm
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ s in Ioo 0 (T : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*endpointKernel T Φ δ s a :=
      lintegral_congr he
    _ = _ := (lintegral_lintegral_swap
      ((BrownianHeatResolvent.measurable_joint_passageDensity.comp measurable_swap).mul
        (measurable_joint_endpointKernel T Φ δ)).aemeasurable).symm

theorem actual_minimum_endpoint_joint_density (T : ℝ≥0) (hT : 0 < T)
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p) :
    (∫⁻ f, ENNReal.ofReal
      (Φ (leastMinimizer T f,minimumValue T f,f T-minimumValue T f)) ∂pathLaw) =
      ∫⁻ s in Ioo 0 (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          ∫⁻ y, entrance (remainingTime T s) y*
            ENNReal.ofReal (Φ (Real.toNNReal s,-a,y)) := by
  have h := actual_minimum_endpoint_density_limit T hT Φ hΦ
  have he := time_endpointKernel_tendsto T hT Φ hΦ
  have hh := he.congr' (show ∀ᶠ δ : ℝ in 𝓝[>] 0,
      _ = _ from by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (actual_window_eq_endpointKernel T δ hδ Φ).symm)
  exact tendsto_nhds_unique h hh

end PerronWright.BrownianMinimumEndpointJointLaw
