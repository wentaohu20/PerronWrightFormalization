import PerronWright.Probability.BrownianParabolicFirstPassageStoppedTiltFull

/-! # Actual passage parameter exchange when a complete excursion is removed

The literal endpoint/area score and polynomial energy commute the prefix
and the removed excursion. The proved actual stopped density then changes
the prefix parameter from lambda to lambda minus the complete length.
There is no stochastic deletion or conditional excursion law premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianCompletedExcursionPassageExchange

open BrownianPathLaw BrownianPathIndependentIncrements BrownianBridgeCyclicArea
open BrownianParabolicDriftTiltGeometry BrownianParabolicStoppedTiltGeometry
open BrownianParabolicFirstPassageStoppedTilt BrownianParabolicFirstPassageStoppedTiltFull
open BrownianFirstPassageUncappedLaw BrownianFirstPassageZeroDrift

theorem stopped_density_completed_exchange (lambda : ℝ) (l : ℝ≥0)
    (p : ℝ≥0 × Path) (e : Path) (he : e l = 0) :
    stoppedDensity lambda p*density (lambda-(p.1 : ℝ)) l e =
      stoppedDensity (lambda-(l : ℝ)) p*
        ENNReal.ofReal (Real.exp (pathArea l e+(l : ℝ)*p.2 p.1-energy lambda l/2)) := by
  unfold stoppedDensity density score
  rw [he,mul_zero,zero_add,← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  unfold energy
  ring

theorem stopped_density_negative_level_completed_exchange (lambda a : ℝ) (l : ℝ≥0)
    (p : ℝ≥0 × Path) (hp : p.2 p.1 = -a) (e : Path) (he : e l = 0) :
    stoppedDensity lambda p*density (lambda-(p.1 : ℝ)) l e =
      stoppedDensity (lambda-(l : ℝ)) p*
        ENNReal.ofReal (Real.exp (pathArea l e-(l : ℝ)*a-energy lambda l/2)) := by
  rw [stopped_density_completed_exchange lambda l p e he,hp]
  congr 3
  ring

theorem actual_parabolic_passage_completed_exchange_lintegral
    (lambda level : ℝ) (hlevel : level < 0) (l : ℝ≥0) (e : Path) (he : e l = 0)
    (Φ : ℝ≥0 × Path → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ p, density (lambda-(p.1 : ℝ)) l e*Φ p
      ∂pathLaw.map (actualDriverPassagePast lambda level)) =
      ENNReal.ofReal (Real.exp (pathArea l e+(l : ℝ)*level-energy lambda l/2))*
        ∫⁻ p, Φ p ∂pathLaw.map (actualDriverPassagePast (lambda-(l : ℝ)) level) := by
  have hd : Measurable (fun p : ℝ≥0 × Path ↦ density (lambda-(p.1 : ℝ)) l e) :=
    measurable_joint_density.comp
      ((measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst)).prodMk
        (measurable_const.prodMk measurable_const))
  have hprod : Measurable (fun p : ℝ≥0 × Path ↦ density (lambda-(p.1 : ℝ)) l e*Φ p) :=
    hd.mul hΦ
  have hp : ∀ᵐ p : ℝ≥0 × Path ∂pathLaw.map (passagePast level), p.2 p.1 = level := by
    have hm : Measurable (fun p : ℝ≥0 × Path ↦ p.2 p.1) :=
      continuous_joint_eval.measurable.comp (measurable_snd.prodMk measurable_fst)
    apply (ae_map_iff (measurable_passagePast level).aemeasurable
      (measurableSet_eq_fun hm measurable_const)).mpr
    filter_upwards [ae_firstPassage_exact_level level hlevel] with f hf
    change f (min (ContinuousPathFirstPassage.firstPassage level f).toNNReal
      (ContinuousPathFirstPassage.firstPassage level f).toNNReal) = level
    rwa [min_self]
  rw [actual_parabolic_passage_law lambda level hlevel,
    actual_parabolic_passage_law (lambda-(l : ℝ)) level hlevel,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_stoppedDensity lambda) hprod,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_stoppedDensity (lambda-(l : ℝ))) hΦ]
  calc
    _ = ∫⁻ p, ENNReal.ofReal (Real.exp (pathArea l e+(l : ℝ)*level-energy lambda l/2))*
        (stoppedDensity (lambda-(l : ℝ)) p*Φ p) ∂pathLaw.map (passagePast level) := by
      apply lintegral_congr_ae
      filter_upwards [hp] with p hpend
      simp only [Pi.mul_apply]
      rw [← mul_assoc,stopped_density_completed_exchange lambda l p e he,hpend]
      ac_rfl
    _ = _ := lintegral_const_mul _ ((measurable_stoppedDensity (lambda-(l : ℝ))).mul hΦ)

end PerronWright.BrownianCompletedExcursionPassageExchange
