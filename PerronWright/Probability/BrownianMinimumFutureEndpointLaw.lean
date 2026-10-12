import PerronWright.Probability.BrownianMinimumFuturePrefixTests

/-! # Exact endpoint density of the genuine unit minimum-future source

The one-time case of the proved actual prefix law is converted from its
literal free entrance density to the normalized Rayleigh density. No
endpoint law is supplied as a distribution premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumFutureEndpointLaw

open BrownianPathLaw BrownianMinimumFutureEntranceSource
open BrownianMinimumFuturePrefixTests BrownianKilledBoundaryEntrance
open BrownianKilledFreeEntranceGeometry BrownianKilledFreeEntranceTests
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianPositiveBridgeMultiPointEntrance
open BrownianKilledFiniteDimensionalOrderedTimes

def endpointDensity (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Ioi (0 : ℝ)).indicator (fun y ↦ y*Real.exp (-y^2/2)) x)

theorem measurable_endpointDensity : Measurable endpointDensity := by
  have hm : Measurable (fun y : ℝ ↦ y*Real.exp (-y^2/2)) := by fun_prop
  exact (hm.indicator measurableSet_Ioi).ennreal_ofReal

theorem unit_entrance_eq_scaled_endpointDensity (x : ℝ) :
    entrance 1 x = ENNReal.ofReal (Real.sqrt (2/Real.pi))*endpointDensity x := by
  have hs : Real.sqrt (2/Real.pi)*Real.sqrt (2*Real.pi) = 2 := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ)/Real.pi)]
    have he : (2/Real.pi)*(2*Real.pi) = (4 : ℝ) := by field_simp; ring
    rw [he]
    norm_num
  have hc : 2*(Real.sqrt (2*Real.pi))⁻¹ = Real.sqrt (2/Real.pi) := by
    have hn : Real.sqrt (2*Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    apply (mul_right_cancel₀ hn)
    rw [mul_assoc,inv_mul_cancel₀ hn,mul_one,hs]
  unfold entrance entranceReal endpointDensity
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  by_cases hx : 0 < x
  · simp only [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx),gaussianPDFReal,
      NNReal.coe_one,mul_one,sub_zero,div_one]
    congr 1
    rw [← hc]
    ring
  · simp only [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
      ENNReal.ofReal_zero,mul_zero]

private theorem endpoint_free_entrance_integral {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ v : FreeVector 1, H (v 0) ∂freeEntranceLaw 0 (orderedGaps 1 ![0,1])) =
      ∫⁻ x : ℝ, entrance 1 x*H x := by
  have hG : Measurable (fun v : FreeVector 1 ↦ H (v 0)) := hH.comp (measurable_pi_apply 0)
  rw [freeEntranceLaw,lintegral_withDensity_eq_lintegral_mul volume
    (measurable_entranceJoint 0 _) hG]
  change (∫⁻ v : FreeVector 1, entranceJoint 0 (orderedGaps 1 ![0,1]) v*H (v 0)) = _
  have hJ : Measurable (fun v : FreeVector 1 ↦
      entranceJoint 0 (orderedGaps 1 ![0,1]) v*H (v 0)) :=
    (measurable_entranceJoint 0 _).mul hG
  rw [lintegral_volume_freeCons 0 hJ]
  simp only [entranceJoint,internalDensity,Fin.prod_univ_zero,mul_one,freeCons,Fin.cons_zero,
    lintegral_const,volume_pi,Measure.pi_empty_univ,mul_one]
  simp [orderedGaps,finiteTimeExtension]

theorem actual_endpoint_lintegral {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ g : Path, H (g 1) ∂unitSourceLaw) = ∫⁻ x : ℝ, endpointDensity x*H x := by
  have hstrict : StrictMono (![0,1] : Fin 2 → ℝ≥0) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at *
  have h := unitSource_prefix_borel_test 0 ![0,1] hstrict rfl rfl
    (fun v : FreeVector 1 ↦ H (v 0)) (hH.comp (measurable_pi_apply 0))
  change (∫⁻ g : Path, H (g 1) ∂unitSourceLaw) = _ at h
  rw [endpoint_free_entrance_integral hH] at h
  simp_rw [unit_entrance_eq_scaled_endpointDensity,mul_assoc] at h
  have hJ : Measurable (fun x : ℝ ↦ endpointDensity x*H x) := measurable_endpointDensity.mul hH
  rw [lintegral_const_mul _ hJ] at h
  have hc0 : ENNReal.ofReal (Real.sqrt (2/Real.pi)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity))
  rw [div_eq_mul_inv,mul_comm (ENNReal.ofReal (Real.sqrt (2/Real.pi))),mul_assoc,
    ENNReal.mul_inv_cancel hc0 ENNReal.ofReal_ne_top,mul_one] at h
  exact h

theorem actual_endpoint_law :
    unitSourceLaw.map (fun g : Path ↦ g 1) = volume.withDensity endpointDensity := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH (continuous_eval 1).measurable,
    lintegral_withDensity_eq_lintegral_mul volume measurable_endpointDensity hH]
  exact actual_endpoint_lintegral hH

end PerronWright.BrownianMinimumFutureEndpointLaw
