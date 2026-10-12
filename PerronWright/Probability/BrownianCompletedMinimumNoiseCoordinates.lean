import PerronWright.Probability.BrownianCompletedMinimumDeletionSource
import PerronWright.Probability.BrownianCompletedExcursionIntegratedPassageExchange

/-! # Recovering the actual deleted Brownian noise from completed driver data

Subtracting the literal parabolic drift is a jointly continuous inverse of
the driver transform. On the actual completed minimum source this recovers
the original compensated deleted Brownian path and its exact residual
parameter. Consequently the proved integrated passage exchange applies
to arbitrary Borel tests of raw remaining noise, not just driver tests.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianCompletedMinimumNoiseCoordinates

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open BrownianBridgeCyclicArea BrownianParabolicDriftTiltGeometry
open BrownianParabolicFirstPassageStoppedTiltFull BrownianExcursionDeletionGeometry
open BrownianParabolicCompletedMinimumSource BrownianCompletedMinimumDeletionSource
open ContinuousPathMinimumSplitBandAverage BrownianCompletedExcursionIntegratedPassageExchange

def recoverNoise (lambda : ℝ) (g : Path) : Path :=
  ⟨fun t ↦ g t-lambda*(t : ℝ)+(t : ℝ)^2/2,
    (g.continuous.sub (continuous_const.mul NNReal.continuous_coe)).add
      ((NNReal.continuous_coe.pow 2).div_const 2)⟩

theorem continuous_recoverNoise : Continuous (fun q : ℝ × Path ↦ recoverNoise q.1 q.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((continuous_fst.snd.eval continuous_snd).sub
    (continuous_fst.fst.mul (NNReal.continuous_coe.comp continuous_snd))).add
      (((NNReal.continuous_coe.comp continuous_snd).pow 2).div_const 2)

theorem measurable_recoverNoise : Measurable (fun q : ℝ × Path ↦ recoverNoise q.1 q.2) :=
  continuous_recoverNoise.measurable

theorem recoverNoise_driftPath (lambda : ℝ) (f : Path) : recoverNoise lambda (driftPath lambda f) = f := by
  apply ContinuousMap.ext
  intro t
  change (f t+lambda*(t : ℝ)-(t : ℝ)^2/2)-lambda*(t : ℝ)+(t : ℝ)^2/2 = f t
  ring

theorem driftPath_recoverNoise (lambda : ℝ) (g : Path) : driftPath lambda (recoverNoise lambda g) = g := by
  apply ContinuousMap.ext
  intro t
  change (g t-lambda*(t : ℝ)+(t : ℝ)^2/2)+lambda*(t : ℝ)-(t : ℝ)^2/2 = g t
  ring

theorem measurable_completed_remaining_noise (lambda : ℝ) :
    Measurable (fun q : CompletedState ↦ recoverNoise (lambda-(q.2.2.1.1 : ℝ)) (remainingDriver q)) :=
  measurable_recoverNoise.comp
    ((measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_snd.snd.fst.fst)).prodMk
      measurable_remainingDriver)

theorem ae_actual_recovered_deleted_noise (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f : Path ∂pathLaw,
      recoverNoise (lambda-((completion (minimumPoint T (driftPath lambda f))).2.2.1.1 : ℝ))
        (remainingDriver (completion (minimumPoint T (driftPath lambda f)))) =
          deletedPath (T : ℝ) lambda f := by
  filter_upwards [ae_actual_parabolic_completion lambda T hT,
    ae_actual_deleted_driver lambda T hT] with f hc hd
  rw [hc.1,hd]
  change recoverNoise (deletedParameter (T : ℝ) lambda f)
    (driftPath (deletedParameter (T : ℝ) lambda f) (deletedPath (T : ℝ) lambda f)) = _
  exact recoverNoise_driftPath _ _

theorem actual_complete_excursion_integrated_noise_exchange
    (lambda : ℝ) (l : ℝ≥0) (hl : 0 < l) (e : Path) (he : e l = 0)
    (F : Path → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ a : ℝ in Ioi 0, ∫⁻ p : ℝ≥0 × Path,
      density (lambda-(p.1 : ℝ)) l e*
        (∫⁻ h : Path, F (recoverNoise (lambda-(l : ℝ))
          (splicePath p.1 (p.2,driftPath (lambda-(l : ℝ)-(p.1 : ℝ)) h))) ∂pathLaw)
            ∂pathLaw.map (actualDriverPassagePast lambda (-a))) =
      ENNReal.ofReal (Real.exp (pathArea l e-energy lambda l/2))*
        ((l : ℝ≥0∞)⁻¹*(∫⁻ f, F f ∂pathLaw)) := by
  have hm : Measurable (fun g : Path ↦ F (recoverNoise (lambda-(l : ℝ)) g)) :=
    hF.comp (measurable_recoverNoise.comp (measurable_const.prodMk measurable_id))
  have h := actual_complete_excursion_integrated_passage_exchange lambda l hl e he
    (fun g ↦ F (recoverNoise (lambda-(l : ℝ)) g)) hm
  simpa only [recoverNoise_driftPath] using h

end PerronWright.BrownianCompletedMinimumNoiseCoordinates
