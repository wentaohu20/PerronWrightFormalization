import PerronWright.Probability.BrownianFirstPassageMinimumWindowPastFutureLaw
import PerronWright.Probability.BrownianHeatResolvent
import PerronWright.Probability.BrownianMinimumWindowSurvivalBounds

/-! # The actual stopped-past time marginal and its depth integral

The time tagged on the genuine first-passage stopped past has the already
proved first-passage density. Tonelli retains arbitrary Borel depth/time
tests and proves the inverse-square-root future bound is integrable under
this actual family of stopped-past laws. No time-marginal or finite-moment
interface is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassagePastTimeMarginal

open BrownianPathLaw BrownianFirstPassageUncappedLaw BrownianFirstPassageDistribution
open BrownianFirstPassageMinimumWindowPastFutureLaw BrownianFirstPassageDensityGeometry
open BrownianFirstPassageDensityLaw BrownianMinimumWindowSurvivalBounds

theorem passagePastLaw_map_realTime (level : ℝ) :
    (passagePastLaw level).map (fun p : ℝ≥0 × Path ↦ (p.1 : ℝ)) = timeLaw level := by
  have hm : Measurable (fun p : ℝ≥0 × Path ↦ (p.1 : ℝ)) :=
    NNReal.continuous_coe.measurable.comp measurable_fst
  rw [passagePastLaw,Measure.map_map hm (measurable_passagePast level)]
  rfl

theorem passagePastLaw_neg_map_density (a : ℝ) (ha : 0 < a) :
    (passagePastLaw (-a)).map (fun p : ℝ≥0 × Path ↦ (p.1 : ℝ)) =
      volume.withDensity (density a) := by
  rw [passagePastLaw_map_realTime,timeLaw_neg_eq_withDensity a ha]

theorem lintegral_past_time_density (a : ℝ) (ha : 0 < a) (T : ℝ≥0)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p in {p : ℝ≥0 × Path | p.1 < T}, H (p.1 : ℝ) ∂passagePastLaw (-a)) =
      ∫⁻ s in Ioo 0 (T : ℝ), density a s*H s := by
  have hm : Measurable (fun p : ℝ≥0 × Path ↦ (p.1 : ℝ)) :=
    NNReal.continuous_coe.measurable.comp measurable_fst
  have hset : MeasurableSet {p : ℝ≥0 × Path | p.1 < T} :=
    measurable_fst measurableSet_Iio
  let F : ℝ → ℝ≥0∞ := (Iio (T : ℝ)).indicator H
  have hF : Measurable F := hH.indicator measurableSet_Iio
  calc
    _ = ∫⁻ p : ℝ≥0 × Path, F (p.1 : ℝ) ∂passagePastLaw (-a) := by
      rw [← lintegral_indicator hset]
      apply lintegral_congr
      intro p
      have he : p.1 < T ↔ (p.1 : ℝ) < (T : ℝ) := NNReal.coe_lt_coe
      simp only [F,Set.indicator,mem_ofPred_eq,mem_Iio,he]
    _ = ∫⁻ s : ℝ, F s ∂volume.withDensity (density a) := by
      rw [← lintegral_map hF hm,passagePastLaw_neg_map_density a ha]
    _ = ∫⁻ s : ℝ, density a s*F s :=
      lintegral_withDensity_eq_lintegral_mul volume (measurable_density a) hF
    _ = ∫⁻ s : ℝ, (Ioo 0 (T : ℝ)).indicator (fun s ↦ density a s*H s) s := by
      apply lintegral_congr
      intro s
      by_cases hs : 0 < s
      · simp only [F,Set.indicator,mem_Iio,mem_Ioo,hs,true_and]
        split_ifs <;> simp
      · have hd : density a s = 0 := by
          rw [density,densityReal_eq_zero_of_nonpos a s (le_of_not_gt hs),ENNReal.ofReal_zero]
        simp only [F,Set.indicator,mem_Ioo,hs,false_and,if_false,hd,zero_mul]
    _ = _ := lintegral_indicator measurableSet_Ioo _

theorem lintegral_level_past_time_density (T : ℝ≥0)
    (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
      H (a,(p.1 : ℝ)) ∂passagePastLaw (-a)) =
      ∫⁻ s in Ioo 0 (T : ℝ), ∫⁻ a in Ioi (0 : ℝ), density a s*H (a,s) := by
  have hM : Measurable (fun p : ℝ × ℝ ↦ density p.1 p.2*H p) :=
    BrownianHeatResolvent.measurable_joint_passageDensity.mul hH
  calc
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ s in Ioo 0 (T : ℝ), density a s*H (a,s) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      exact lintegral_past_time_density a ha T (fun s ↦ H (a,s))
        (hH.comp (measurable_const.prodMk measurable_id))
    _ = _ := lintegral_lintegral_swap hM.aemeasurable

theorem lintegral_level_past_time_inverse_sqrt (T : ℝ≥0) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
      ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))) ∂passagePastLaw (-a)) =
      ENNReal.ofReal (1/Real.sqrt (2*Real.pi))*
        ∫⁻ s in Ioo 0 (T : ℝ), ENNReal.ofReal (timeMajorant T s) := by
  rw [lintegral_level_past_time_density T
    (fun p : ℝ × ℝ ↦ ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-p.2))) (by fun_prop)]
  calc
    _ = ∫⁻ s in Ioo 0 (T : ℝ),
        ENNReal.ofReal (1/Real.sqrt (2*Real.pi))*ENNReal.ofReal (timeMajorant T s) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hd : Measurable (fun a : ℝ ↦ density a s) :=
        BrownianHeatResolvent.measurable_joint_passageDensity.comp
          (measurable_id.prodMk measurable_const)
      rw [lintegral_mul_const'' _ hd.aemeasurable,passage_level_mass s hs.1,
        ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold timeMajorant
      ring
    _ = _ := lintegral_const_mul _ (measurable_timeMajorant T).ennreal_ofReal

theorem lintegral_level_past_time_inverse_sqrt_ne_top (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
      ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))) ∂passagePastLaw (-a)) ≠ ⊤ := by
  rw [lintegral_level_past_time_inverse_sqrt]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_timeMajorant_ne_top T hT)

end PerronWright.BrownianFirstPassagePastTimeMarginal
