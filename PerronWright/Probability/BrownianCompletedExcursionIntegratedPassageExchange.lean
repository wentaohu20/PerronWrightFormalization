import PerronWright.Probability.BrownianCompletedExcursionPassageExchange
import PerronWright.Probability.BrownianParabolicPassageDriverFutureLaw
import PerronWright.Probability.BrownianPalmTimeDepthElimination

/-! # True complete-excursion passage exchange with the depth integrated out

For a fixed complete zero-endpoint excursion, the actual stopped density
changes the negative-level prefix parameter by its literal length. The
fresh whole future reconstructs the true remaining driver; integrating
the depth gives the inverse length. No stochastic Palm identity or
lifetime-conditioned excursion shape is supplied as a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianCompletedExcursionIntegratedPassageExchange

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open BrownianBridgeCyclicArea BrownianParabolicDriftTiltGeometry
open BrownianParabolicFirstPassageStoppedTiltFull
open BrownianCompletedExcursionPassageExchange BrownianParabolicPassageDriverFutureLaw
open BrownianPalmTimeDepthElimination

private theorem measurable_stitch :
    Measurable (fun z : (ℝ≥0 × Path) × Path ↦ splicePath z.1.1 (z.1.2,z.2)) := by
  apply Continuous.measurable
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_fst.fst.snd.eval (continuous_snd.min continuous_fst.fst.fst)).add
    (continuous_fst.snd.eval (continuous_snd.sub continuous_fst.fst.fst))

theorem actual_complete_excursion_integrated_passage_exchange
    (lambda : ℝ) (l : ℝ≥0) (hl : 0 < l) (e : Path) (he : e l = 0)
    (F : Path → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ a : ℝ in Ioi 0, ∫⁻ p : ℝ≥0 × Path,
      density (lambda-(p.1 : ℝ)) l e*
        (∫⁻ h : Path, F (splicePath p.1
          (p.2,driftPath (lambda-(l : ℝ)-(p.1 : ℝ)) h)) ∂pathLaw)
          ∂pathLaw.map (actualDriverPassagePast lambda (-a))) =
      ENNReal.ofReal (Real.exp (pathArea l e-energy lambda l/2))*
        ((l : ℝ≥0∞)⁻¹*(∫⁻ f, F (driftPath (lambda-(l : ℝ)) f) ∂pathLaw)) := by
  let Φ : ℝ≥0 × Path → ℝ≥0∞ := fun p ↦
    ∫⁻ h : Path, F (splicePath p.1
      (p.2,driftPath (lambda-(l : ℝ)-(p.1 : ℝ)) h)) ∂pathLaw
  have hshift : Measurable (fun z : (ℝ≥0 × Path) × Path ↦
      (z.1,driftPath (lambda-(l : ℝ)-(z.1.1 : ℝ)) z.2)) :=
    measurable_fst.prodMk (continuous_driftPath.measurable.comp
      ((measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk
        measurable_snd))
  have hΦ : Measurable Φ := (hF.comp (measurable_stitch.comp hshift)).lintegral_prod_right'
  let C := ENNReal.ofReal (Real.exp (pathArea l e-energy lambda l/2))
  let J := ∫⁻ f, F (driftPath (lambda-(l : ℝ)) f) ∂pathLaw
  calc
    _ = ∫⁻ a : ℝ in Ioi 0, C*(ENNReal.ofReal (Real.exp (-(l : ℝ)*a))*J) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      have hlevel : -a < 0 := neg_neg_of_pos ha
      change (∫⁻ p, density (lambda-(p.1 : ℝ)) l e*Φ p
        ∂pathLaw.map (actualDriverPassagePast lambda (-a))) = _
      rw [actual_parabolic_passage_completed_exchange_lintegral lambda (-a) hlevel l e he Φ hΦ]
      have hwhole := actual_driver_passage_whole_lintegral (lambda-(l : ℝ)) (-a) hF
      change J = ∫⁻ p, Φ p ∂pathLaw.map (actualDriverPassagePast (lambda-(l : ℝ)) (-a)) at hwhole
      rw [← hwhole]
      have hexp : ENNReal.ofReal (Real.exp (pathArea l e+(l : ℝ)*(-a)-energy lambda l/2)) =
          C*ENNReal.ofReal (Real.exp (-(l : ℝ)*a)) := by
        dsimp [C]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
        congr 2
        ring
      rw [hexp,mul_assoc]
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop),lintegral_mul_const _ (by fun_prop),
        negative_depth_lintegral l hl]

end PerronWright.BrownianCompletedExcursionIntegratedPassageExchange
