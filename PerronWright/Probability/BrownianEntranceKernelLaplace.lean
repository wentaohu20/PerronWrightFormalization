import PerronWright.Probability.BrownianKilledBoundaryEntrance
import PerronWright.Probability.BrownianHeatResolvent

/-! # Actual entrance-kernel duration transform

The entrance kernel used by the constructed positive excursion is exactly
twice the proved negative-level first-passage density. Its genuine duration
transform therefore follows from the actual Brownian hitting Laplace law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianEntranceKernelLaplace

open BrownianKilledBoundaryEntrance BrownianFirstPassageDensityGeometry
open BrownianHeatPassageTail BrownianHeatResolvent PositiveTimeConvolutionLaplace

theorem entranceReal_eq_twice_passage_density (t z : ℝ) (hz : 0 < z) :
    entranceReal (Real.toNNReal t) z = 2*densityReal z t := by
  by_cases ht : 0 < t
  · rw [entranceReal,indicator_of_mem (show z ∈ Ioi (0 : ℝ) from hz),
      Real.coe_toNNReal _ ht.le,densityReal_eq_heat z t ht]
    unfold heatReal
    ring
  · rw [densityReal_eq_zero_of_nonpos z t (le_of_not_gt ht),
      Real.toNNReal_eq_zero.mpr (le_of_not_gt ht)]
    simp only [entranceReal,indicator_of_mem (show z ∈ Ioi (0 : ℝ) from hz),
      gaussianPDFReal_zero_var,Pi.zero_apply,mul_zero]

theorem entrance_eq_twice_passage_density (t z : ℝ) (hz : 0 < z) :
    entrance (Real.toNNReal t) z = ENNReal.ofReal 2*density z t := by
  rw [entrance,entranceReal_eq_twice_passage_density t z hz,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rfl

theorem measurable_joint_entrance :
    Measurable (fun q : ℝ × ℝ ↦ entrance (Real.toNNReal q.1) q.2) := by
  unfold entrance entranceReal
  change Measurable (fun q : ℝ × ℝ ↦ ENNReal.ofReal
    (if 0 < q.2 then 2*q.2/(Real.toNNReal q.1 : ℝ)*
      gaussianPDFReal 0 (Real.toNNReal q.1) q.2 else 0))
  apply Measurable.ennreal_ofReal
  apply Measurable.ite (measurableSet_lt measurable_const measurable_snd) _ measurable_const
  exact (measurable_const.mul measurable_snd |>.div measurable_fst.real_toNNReal.coe_nnreal_real).mul
    (measurable_uncurry_gaussianPDFReal.comp
      (measurable_const.prodMk (measurable_fst.real_toNNReal.prodMk measurable_snd)))

theorem lintegral_entrance_laplace (p : ℝ) (hp : 0 ≤ p) (z : ℝ) (hz : 0 < z) :
    (∫⁻ t : ℝ, laplaceWeight p t*entrance (Real.toNNReal t) z) =
      ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p))) := by
  calc
    _ = ENNReal.ofReal 2*(∫⁻ t : ℝ, laplaceWeight p t*density z t) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro t
      rw [entrance_eq_twice_passage_density t z hz]
      ac_rfl
    _ = _ := by
      rw [lintegral_passageDensity_laplace z hz p hp,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem lintegral_entrance_laplace_allStates (p : ℝ) (hp : 0 ≤ p) (z : ℝ) :
    (∫⁻ t : ℝ, laplaceWeight p t*entrance (Real.toNNReal t) z) =
      if 0 < z then ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p))) else 0 := by
  by_cases hz : 0 < z
  · rw [if_pos hz]
    exact lintegral_entrance_laplace p hp z hz
  · rw [if_neg hz]
    simp only [entrance,entranceReal,indicator_of_notMem (show z ∉ Ioi (0 : ℝ) from hz),
      ENNReal.ofReal_zero,mul_zero,lintegral_zero]

end PerronWright.BrownianEntranceKernelLaplace
