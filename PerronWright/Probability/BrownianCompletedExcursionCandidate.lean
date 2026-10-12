import PerronWright.Probability.BrownianMinimumFutureReturnDensity
import PerronWright.Probability.BrownianEntranceDurationScaling

/-! # A literal completed-excursion duration and shape mixture

The lifetime density is the proved actual source return density. The shape
is the constructed unit entrance excursion, dilated by that lifetime.
This defines and normalizes the candidate measure; it does not presume
that the actual source stopped at its return has this joint law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedExcursionCandidate

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathDilationLaw
open BrownianMinimumFutureEntranceSource BrownianMinimumFutureFirstReturn
open BrownianMinimumFuturePostUnit BrownianMinimumFutureReturnDensity

private def realization (q : ℝ × Path) : ℝ≥0 × Path :=
  (Real.toNNReal q.1,brownianDilation (Real.toNNReal q.1) q.2)

private theorem measurable_realization : Measurable realization :=
  measurable_fst.real_toNNReal.prodMk (measurable_joint_brownianDilation.comp
    (measurable_fst.real_toNNReal.prodMk measurable_snd))

private theorem returnLaw_isProbability : IsProbabilityMeasure (volume.withDensity returnDensity) := by
  rw [← actual_firstReturn_law]
  exact Measure.isProbabilityMeasure_map aemeasurable_firstReturnZero.ennreal_toReal

def candidateLaw : Measure (ℝ≥0 × Path) :=
  ((volume.withDensity returnDensity).prod
    (BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one)).map realization

theorem candidateLaw_isProbability : IsProbabilityMeasure candidateLaw := by
  let := returnLaw_isProbability
  let := BrownianEntranceContinuousRealization.pathLaw_isProbability 1 zero_lt_one
  exact Measure.isProbabilityMeasure_map measurable_realization.aemeasurable

theorem lintegral_candidateLaw (Ψ : ℝ≥0 × Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ p, Ψ p ∂candidateLaw) =
      ∫⁻ ζ : ℝ, returnDensity ζ*(∫⁻ e : Path,
        Ψ (Real.toNNReal ζ,brownianDilation (Real.toNNReal ζ) e)
          ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
  let := returnLaw_isProbability
  let := BrownianEntranceContinuousRealization.pathLaw_isProbability 1 zero_lt_one
  have hm : Measurable (fun q : ℝ × Path ↦ Ψ (realization q)) := hΨ.comp measurable_realization
  have hi := hm.lintegral_prod_right'
    (ν := BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one)
  rw [candidateLaw,lintegral_map hΨ measurable_realization,lintegral_prod _ hm.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul volume measurable_returnDensity hi]
  rfl

end PerronWright.BrownianCompletedExcursionCandidate
