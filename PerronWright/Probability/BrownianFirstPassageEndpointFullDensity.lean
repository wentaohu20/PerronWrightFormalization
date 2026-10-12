import PerronWright.Probability.BrownianFirstPassageEndpointDensityKernel
import PerronWright.Probability.BrownianFirstPassageMinimumWindowFutureLaw
import PerronWright.Probability.BrownianFirstPassageDensityLaw

/-! # Genuine joint first-passage and endpoint densities

Both factors below are proved densities of the actual Brownian laws:
the first-passage density comes from reflection and its exact CDF,
and the future endpoint kernel comes from the true whole-future product
law. The minimum-depth window formula uses the genuine killed kernel.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageEndpointFullDensity

open BrownianPathLaw ContinuousPathFirstPassage
open BrownianFirstPassageEndpointGeometry BrownianFirstPassageEndpointDensityKernel

theorem actual_endpoint_full_density (a : ℝ) (ha : 0 < a) (T : ℝ≥0)
    (Φ : ℝ × ℝ → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ f in {f : Path | realTime (-a) f < (T : ℝ)},
      Φ (realTime (-a) f,f T) ∂pathLaw) =
      ∫⁻ s in Iio (T : ℝ), BrownianFirstPassageDensityGeometry.density a s *
        ∫⁻ z, gaussianPDF (-a) (remainingTime T s) z * Φ (s,z) := by
  rw [actual_endpoint_lintegral_density (-a) (neg_neg_of_pos ha) T Φ hΦ]
  change (∫⁻ s in Iio (T : ℝ), ∫⁻ z, gaussianPDF (-a) (remainingTime T s) z * Φ (s,z)
    ∂volume ∂BrownianFirstPassageDistribution.timeLaw (-a)) = _
  rw [BrownianFirstPassageDensityLaw.timeLaw_neg_eq_withDensity a ha,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume
      (BrownianFirstPassageDensityGeometry.measurable_density a) _ measurableSet_Iio
      (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  rfl

theorem actual_minimum_window_full_density (a : ℝ) (ha : 0 < a)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Φ : ℝ × ℝ → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ f in {f : Path | realTime (-a) f < (T : ℝ)},
      (survival (-a-δ) T).indicator (fun f ↦ Φ (realTime (-a) f,f T)) f ∂pathLaw) =
      ∫⁻ s in Iio (T : ℝ), BrownianFirstPassageDensityGeometry.density a s *
        ∫⁻ y, BrownianPositiveKilledEndpoint.density δ (remainingTime T s) y *
          Φ (s,-a-δ+y) := by
  rw [actual_minimum_window_lintegral_density (-a) (neg_neg_of_pos ha) δ hδ T Φ hΦ]
  change (∫⁻ s in Iio (T : ℝ), ∫⁻ y, BrownianPositiveKilledEndpoint.density δ
    (remainingTime T s) y * Φ (s,-a-δ+y)
    ∂volume ∂BrownianFirstPassageDistribution.timeLaw (-a)) = _
  rw [BrownianFirstPassageDensityLaw.timeLaw_neg_eq_withDensity a ha,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume
      (BrownianFirstPassageDensityGeometry.measurable_density a) _ measurableSet_Iio
      (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  rfl

theorem actual_minimum_window_future_full_density (a : ℝ) (ha : 0 < a)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Ψ : ℝ × Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f in {f : Path | realTime (-a) f < (T : ℝ)},
      (survival (-a-δ) T).indicator
        (fun f ↦ Ψ (realTime (-a) f,BrownianFirstPassageUncappedLaw.passageFuture (-a) f))
          f ∂pathLaw) =
      ∫⁻ s in Iio (T : ℝ), BrownianFirstPassageDensityGeometry.density a s *
        ∫⁻ g in survival (-δ) (remainingTime T s), Ψ (s,g) ∂pathLaw := by
  rw [BrownianFirstPassageMinimumWindowFutureLaw.actual_minimum_window_future_lintegral
    (-a) (neg_neg_of_pos ha) δ hδ T Ψ hΨ]
  change (∫⁻ s in Iio (T : ℝ), ∫⁻ g in survival (-δ) (remainingTime T s), Ψ (s,g)
    ∂pathLaw ∂BrownianFirstPassageDistribution.timeLaw (-a)) = _
  rw [BrownianFirstPassageDensityLaw.timeLaw_neg_eq_withDensity a ha,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume
      (BrownianFirstPassageDensityGeometry.measurable_density a) _ measurableSet_Iio
      (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  rfl

end PerronWright.BrownianFirstPassageEndpointFullDensity
