import PerronWright.Probability.BrownianCompletedMinimumCampbellSource
import PerronWright.Probability.BrownianCompletedMinimumNoiseCoordinates
import PerronWright.Probability.BrownianExcursionTuplePoissonWeights

/-! # Actual full-area Poisson and deleted-noise tests in the Campbell source

The complete-state test retains the literal component duration, full area,
and compensated deleted Brownian path. Its Campbell identity is derived
from the actual nonrepeating excursion section, not a Palm assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianMarkedDeletedCampbellTest

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionComponents
open FullHorizonExcursionSection BrownianFullHorizonExcursionAreas
open FullHorizonExcursionEndpoints BrownianExcursionDeletionGeometry
open BrownianParabolicCompletedMinimumSource BrownianCompletedMinimumDeletionSource
open BrownianCompletedMinimumNoiseCoordinates BrownianCompletedMinimumCampbellSource
open BrownianExcursionTuplePoissonWeights BrownianMinimumPointReturnAnchor
open ContinuousPathMinimumSplitBandAverage

def markedDeletedTest (lambda : ℝ) (r : ℕ) (H : ℝ × Path → ℝ≥0∞)
    (q : CompletedState) : ℝ≥0∞ :=
  poissonWeight (Real.toNNReal (completeArea q)) r *
    H ((q.2.2.1.1 : ℝ),recoverNoise (lambda-(q.2.2.1.1 : ℝ)) (remainingDriver q))

theorem measurable_markedDeletedTest (lambda : ℝ) (r : ℕ)
    (H : ℝ × Path → ℝ≥0∞) (hH : Measurable H) :
    Measurable (markedDeletedTest lambda r H) :=
  ((measurable_poissonWeight r).comp measurable_completeArea.real_toNNReal).mul
    (hH.comp ((NNReal.continuous_coe.measurable.comp measurable_snd.snd.fst.fst).prodMk
      (measurable_completed_remaining_noise lambda)))

theorem markedDeletedTest_componentState (lambda : ℝ) (r : ℕ)
    (H : ℝ × Path → ℝ≥0∞) (q : ℝ) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hb : BddAbove (component (driftedReflectionPath lambda f) q)) :
    markedDeletedTest lambda r H (componentState lambda q f) =
      poissonWeight (excursionArea q lambda f) r *
        H (length q (driftedReflectionPath lambda f),deletedPath q lambda f) := by
  have hl : (componentState lambda q f).2.2.1.1 = cutLength q lambda f := by
    change Real.toNNReal (length q (driftedReflectionPath lambda f)) = _
    rw [← cutLength_eq_length q lambda f hq hb,Real.toNNReal_coe]
  unfold markedDeletedTest
  rw [completeArea_componentState lambda q f hq hb,Real.toNNReal_coe,
    remainingDriver_componentState lambda q f hq hb,hl]
  change poissonWeight (excursionArea q lambda f) r *
    H ((cutLength q lambda f : ℝ),
      recoverNoise (deletedParameter q lambda f)
        (BrownianPathReflectionLaw.driftPath (deletedParameter q lambda f)
          (deletedPath q lambda f))) = _
  rw [recoverNoise_driftPath,cutLength_eq_length q lambda f hq hb]

theorem actual_marked_deleted_campbell_lintegral (lambda : ℝ) (r : ℕ)
    (H : ℝ × Path → ℝ≥0∞) (hH : Measurable H) :
    (∑' q : ℚ, ∫⁻ f : Path,
      if Representative (driftedReflectionPath lambda f) q then
        poissonWeight (excursionArea (q : ℝ) lambda f) r *
          H (length (q : ℝ) (driftedReflectionPath lambda f),deletedPath (q : ℝ) lambda f)
      else 0 ∂pathLaw) =
      ∫⁻ t : ℝ in Ioi 0, ∫⁻ f : Path,
        markedDeletedTest lambda r H
          (completion (minimumPoint (Real.toNNReal t)
            (BrownianPathReflectionLaw.driftPath lambda f))) /
          ((completion (minimumPoint (Real.toNNReal t)
            (BrownianPathReflectionLaw.driftPath lambda f))).2.2.1.1 : ℝ≥0∞)
              ∂pathLaw := by
  calc
    _ = ∑' q : ℚ, ∫⁻ f : Path,
        if Representative (driftedReflectionPath lambda f) q then
          markedDeletedTest lambda r H (componentState lambda (q : ℝ) f)
        else 0 ∂pathLaw := by
      apply tsum_congr
      intro q
      apply lintegral_congr_ae
      filter_upwards [ae_actual_parabolic_component_bddAbove lambda (q : ℝ)] with f hf
      by_cases hq : Representative (driftedReflectionPath lambda f) q
      · rw [if_pos hq,if_pos hq,markedDeletedTest_componentState lambda r H (q : ℝ) f hq.1 hf]
      · rw [if_neg hq,if_neg hq]
    _ = _ := actual_completed_campbell_inverse_length lambda _
      (measurable_markedDeletedTest lambda r H hH)

end PerronWright.BrownianMarkedDeletedCampbellTest
