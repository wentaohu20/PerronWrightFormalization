import PerronWright.Probability.BrownianMinimumFutureReturnMixture
import PerronWright.Probability.BrownianRayleighPassageIntegral

/-! # Exact first-return density of the genuine minimum-future source

The literal positive-time return is mixed over the proved actual Rayleigh
endpoint. Tonelli, the actual Brownian hitting density, and the evaluated
Gaussian height integral give the return law without a distribution premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumFutureReturnDensity

open BrownianPathLaw BrownianMinimumFutureEntranceSource
open BrownianMinimumFutureEndpointLaw BrownianMinimumFutureFirstReturn
open BrownianMinimumFutureReturnMixture BrownianRayleighPassageIntegral

def returnDensity (z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Ioi (1 : ℝ)).indicator (fun t ↦ 1/(2*t*Real.sqrt t)) z)

theorem measurable_returnDensity : Measurable returnDensity := by
  have hm : Measurable (fun t : ℝ ↦ 1/(2*t*Real.sqrt t)) := by fun_prop
  exact (hm.indicator measurableSet_Ioi).ennreal_ofReal

theorem returnDensity_eq_rpow (z : ℝ) (hz : 1 < z) :
    returnDensity z = ENNReal.ofReal ((1/2 : ℝ)*z^(-3/2 : ℝ)) := by
  unfold returnDensity
  rw [indicator_of_mem (show z ∈ Ioi (1 : ℝ) from hz)]
  congr 1
  have hp : z^(-3/2 : ℝ) = (z*Real.sqrt z)⁻¹ := by
    rw [show (-3/2 : ℝ) = -(1+1/2) by norm_num,
      Real.rpow_neg (by linarith : 0 ≤ z),Real.rpow_add (by linarith : 0 < z),
      Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [hp]
  ring

theorem actual_firstReturn_lintegral {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ g : Path, H (firstReturnZero g).toReal ∂unitSourceLaw) =
      ∫⁻ z : ℝ, returnDensity z*H z := by
  have hm : Measurable (fun q : ℝ × ℝ ↦ H q.2) := hH.comp measurable_snd
  have he := actual_firstReturn_endpoint_lintegral hm
  change (∫⁻ g : Path, H (firstReturnZero g).toReal ∂unitSourceLaw) =
    ∫⁻ x : ℝ, endpointDensity x*(∫⁻ s : ℝ,
      BrownianFirstPassageDensityGeometry.density x s*H (1+s)) at he
  have hJ : Measurable (fun q : ℝ × ℝ ↦
      (endpointDensity q.1*BrownianFirstPassageDensityGeometry.density q.1 q.2)*H (1+q.2)) :=
    ((measurable_endpointDensity.comp measurable_fst).mul
      BrownianHeatResolvent.measurable_joint_passageDensity).mul
        (hH.comp (measurable_const.add measurable_snd))
  rw [he]
  calc
    _ = ∫⁻ x : ℝ, ∫⁻ s : ℝ,
        (endpointDensity x*BrownianFirstPassageDensityGeometry.density x s)*H (1+s) := by
      apply lintegral_congr
      intro x
      have hS : Measurable (fun s : ℝ ↦
          BrownianFirstPassageDensityGeometry.density x s*H (1+s)) :=
        (BrownianFirstPassageDensityGeometry.measurable_density x).mul
          (hH.comp (measurable_const.add measurable_id))
      rw [← lintegral_const_mul _ hS]
      simp only [mul_assoc]
    _ = ∫⁻ s : ℝ, ∫⁻ x : ℝ,
        (endpointDensity x*BrownianFirstPassageDensityGeometry.density x s)*H (1+s) :=
      lintegral_lintegral_swap hJ.aemeasurable
    _ = ∫⁻ s : ℝ, (∫⁻ x : ℝ,
        endpointDensity x*BrownianFirstPassageDensityGeometry.density x s)*H (1+s) := by
      apply lintegral_congr
      intro s
      exact lintegral_mul_const _ ((measurable_endpointDensity).mul
        (BrownianHeatResolvent.measurable_joint_passageDensity.comp
          (measurable_id.prodMk measurable_const)))
    _ = ∫⁻ s : ℝ, returnDensity (1+s)*H (1+s) := by
      apply lintegral_congr
      intro s
      by_cases hs : 0 < s
      · rw [lintegral_endpoint_passage s hs]
        simp only [returnDensity,indicator_of_mem (show 1+s ∈ Ioi (1 : ℝ) by exact lt_add_of_pos_right 1 hs)]
      · rw [lintegral_endpoint_passage_nonpositive s (le_of_not_gt hs)]
        simp [returnDensity,indicator_of_notMem (show 1+s ∉ Ioi (1 : ℝ) by simpa using hs)]
    _ = _ := by
      have ht : Measurable (fun z : ℝ ↦ returnDensity z*H z) := measurable_returnDensity.mul hH
      exact (measurePreserving_add_left (volume : Measure ℝ) 1).lintegral_comp ht

theorem actual_firstReturn_law :
    unitSourceLaw.map (fun g : Path ↦ (firstReturnZero g).toReal) =
      volume.withDensity returnDensity := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map' hH.aemeasurable aemeasurable_firstReturnZero.ennreal_toReal,
    lintegral_withDensity_eq_lintegral_mul volume measurable_returnDensity hH]
  exact actual_firstReturn_lintegral hH

end PerronWright.BrownianMinimumFutureReturnDensity
