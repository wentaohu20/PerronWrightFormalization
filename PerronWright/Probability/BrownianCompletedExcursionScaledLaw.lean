import PerronWright.Probability.BrownianCompletedExcursionStoppedLaw
import PerronWright.Probability.BrownianCompletedExcursionCandidateScaling

/-! # Actual completed-return lifetime and full stopped shape at every scale

The proved actual unit-source stopped-path law, not a conditional shape
premise, is transported by the literal return-time and path dilation maps.
The resulting lifetime density is sqrt(r)/(2*l*sqrt(l)) on l > r.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedExcursionScaledLaw

open BrownianPathLaw BrownianPathDilationLaw BrownianMinimumFutureEntranceSource
open BrownianMinimumFutureScaledStrongMarkov BrownianMinimumFutureReturnPathGeometry
open ContinuousPathPositiveReturnMeasurable BrownianCompletedExcursionStoppedLaw
open BrownianCompletedExcursionCandidateScaling

theorem actual_scaled_returnTaggedPast_law (r : ℝ≥0) (hr : 0 < r) :
    (sourceLaw r).map returnTaggedPast = scaledCandidateLaw r := by
  rw [sourceLaw,Measure.map_map measurable_returnTaggedPast (measurable_brownianDilation r),
    scaledCandidateLaw,← actual_returnTaggedPast_law,
    Measure.map_map (measurable_scaleTaggedPast r) measurable_returnTaggedPast]
  congr 1
  funext g
  exact returnTaggedPast_brownianDilation r hr g

theorem actual_scaled_returnTaggedPast_lintegral (r : ℝ≥0) (hr : 0 < r)
    (Ψ : ℝ≥0 × Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ g : Path, Ψ (returnTaggedPast g) ∂sourceLaw r) =
      ∫⁻ l : ℝ, lifetimeDensity r l*(∫⁻ e : Path,
        Ψ (Real.toNNReal l,brownianDilation (Real.toNNReal l) e)
          ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
  rw [← lintegral_map hΨ measurable_returnTaggedPast,actual_scaled_returnTaggedPast_law r hr]
  exact lintegral_scaledCandidateLaw r hr Ψ hΨ

end PerronWright.BrownianCompletedExcursionScaledLaw
