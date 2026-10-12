import PerronWright.Probability.BrownianFirstPassageMinimumWindowLaw

/-! # Numerical endpoint kernels at a genuine first passage

These identities replace the future Gaussian or killed endpoint measure
by its already proved density. The outer measure remains the actual
negative-level first-passage time law, not a hypothesized hitting density.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageEndpointDensityKernel

open BrownianPathLaw ContinuousPathFirstPassage
open BrownianFirstPassageEndpointGeometry BrownianFirstPassageEndpointJointLaw
open BrownianFirstPassageMinimumWindowLaw

theorem remainingTime_pos (T : ℝ≥0) {s : ℝ} (hs : s < (T : ℝ)) :
    0 < remainingTime T s := by
  rw [remainingTime,Real.toNNReal_pos]
  linarith

theorem actual_endpoint_lintegral_density (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (Φ : ℝ × ℝ → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ f in {f : Path | realTime level f < (T : ℝ)}, Φ (realTime level f,f T) ∂pathLaw) =
      ∫⁻ s in Iio (T : ℝ), ∫⁻ z, gaussianPDF level (remainingTime T s) z * Φ (s,z)
        ∂volume ∂timeLaw level := by
  rw [actual_endpoint_lintegral level hlevel T Φ hΦ]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := timeLaw level) measurableSet_Iio] with s hs
  rw [gaussianReal_of_var_ne_zero level (ne_of_gt (remainingTime_pos T hs))]
  have hm : Measurable (fun z : ℝ ↦ Φ (s,z)) :=
    hΦ.comp (measurable_const.prodMk measurable_id)
  exact lintegral_withDensity_eq_lintegral_mul volume
    (measurable_gaussianPDF level _) hm

theorem actual_minimum_window_lintegral_density (level : ℝ) (hlevel : level < 0)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Φ : ℝ × ℝ → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ f in {f : Path | realTime level f < (T : ℝ)},
      (survival (level-δ) T).indicator (fun f ↦ Φ (realTime level f,f T)) f ∂pathLaw) =
      ∫⁻ s in Iio (T : ℝ), ∫⁻ y, BrownianPositiveKilledEndpoint.density δ
        (remainingTime T s) y * Φ (s,level-δ+y) ∂volume ∂timeLaw level := by
  rw [actual_minimum_window_lintegral level hlevel δ hδ T Φ hΦ]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (μ := timeLaw level) measurableSet_Iio] with s hs
  rw [BrownianPositiveKilledEndpoint.law_eq_withDensity δ hδ _ (remainingTime_pos T hs)]
  have hm : Measurable (fun y : ℝ ↦ Φ (s,level-δ+y)) :=
    hΦ.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  exact lintegral_withDensity_eq_lintegral_mul volume
    (BrownianPositiveKilledEndpoint.measurable_density δ _) hm

end PerronWright.BrownianFirstPassageEndpointDensityKernel
