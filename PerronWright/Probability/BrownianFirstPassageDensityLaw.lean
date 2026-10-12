import PerronWright.Probability.BrownianFirstPassageDistribution
import PerronWright.Probability.BrownianFirstPassageDensityGeometry

/-! # The true Brownian first-passage law has its Gaussian density

Reflection gives the actual first-passage CDF. The proved one-dimensional
Jacobian gives the same CDF for the density, and finite-measure uniqueness
identifies the entire Borel law. There is no first-passage density premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageDensityLaw

open BrownianPathLaw BrownianFirstPassageDistribution BrownianFirstPassageDensityGeometry

theorem gaussian_lower_tail_standardization (level : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    gaussianReal 0 T (Iic level) = gaussianReal 0 1 (Iic (level / Real.sqrt T)) := by
  have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hT
  have hv : (⟨(Real.sqrt (T : ℝ))^2,sq_nonneg _⟩ : ℝ≥0)*1 = T := by
    apply NNReal.coe_injective
    change (Real.sqrt (T : ℝ))^2*1 = (T : ℝ)
    rw [mul_one,Real.sq_sqrt T.coe_nonneg]
  have hm : (gaussianReal 0 1).map (fun z : ℝ ↦ Real.sqrt T*z) = gaussianReal 0 T := by
    rw [gaussianReal_map_const_mul,mul_zero]
    congr 1
  have he : (fun z : ℝ ↦ Real.sqrt T*z) ⁻¹' Iic level = Iic (level/Real.sqrt T) := by
    ext z
    simp only [mem_preimage,mem_Iic]
    rw [le_div_iff₀ hs,mul_comm]
  rw [← hm,Measure.map_apply (by fun_prop) measurableSet_Iic,he]

theorem timeLaw_neg_eq_withDensity (a : ℝ) (ha : 0 < a) :
    timeLaw (-a) = volume.withDensity (density a) := by
  apply Measure.ext_of_Iic
  intro T
  rw [withDensity_apply _ measurableSet_Iic]
  by_cases hT : 0 < T
  · let TN : ℝ≥0 := ⟨T,hT.le⟩
    have hTN : 0 < TN := hT
    calc
      _ = 2 * gaussianReal 0 TN (Iic (-a)) := timeLaw_Iic (-a) (neg_neg_of_pos ha) TN hTN
      _ = 2 * gaussianReal 0 1 (Iic (argument a T)) := by
        rw [gaussian_lower_tail_standardization (-a) TN hTN]
        rfl
      _ = _ := (density_integral_Iic a ha T hT).symm
  · rw [timeLaw_Iic_of_nonpos (-a) (neg_neg_of_pos ha) T (le_of_not_gt hT)]
    symm
    apply setLIntegral_eq_zero measurableSet_Iic
    intro t ht
    have hp : t ∉ Ioi (0 : ℝ) := not_lt.mpr (ht.trans (le_of_not_gt hT))
    simp only [density,densityReal,indicator_of_notMem hp,ENNReal.ofReal_zero,Pi.zero_apply]

theorem timeLaw_neg_apply_density (a : ℝ) (ha : 0 < a) {A : Set ℝ}
    (hA : MeasurableSet A) :
    timeLaw (-a) A = ∫⁻ t in A, density a t := by
  rw [timeLaw_neg_eq_withDensity a ha,withDensity_apply _ hA]

theorem firstPassage_density_probability (a : ℝ) (ha : 0 < a) {A : Set ℝ}
    (hA : MeasurableSet A) :
    pathLaw {f : Path | realTime (-a) f ∈ A} = ∫⁻ t in A, density a t := by
  rw [← timeLaw_apply (-a) hA]
  exact timeLaw_neg_apply_density a ha hA

theorem density_total_mass (a : ℝ) (ha : 0 < a) : ∫⁻ t, density a t = 1 := by
  have h := timeLaw_neg_apply_density a ha MeasurableSet.univ
  simpa only [measure_univ,Measure.restrict_univ] using h.symm

theorem density_measure_isProbability (a : ℝ) (ha : 0 < a) :
    IsProbabilityMeasure (volume.withDensity (density a)) := by
  rw [← timeLaw_neg_eq_withDensity a ha]
  infer_instance

theorem lintegral_firstPassage_density (a : ℝ) (ha : 0 < a)
    (Ψ : ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ f : Path, Ψ (realTime (-a) f) ∂pathLaw = ∫⁻ t, density a t * Ψ t := by
  rw [← lintegral_map hΨ (measurable_realTime (-a)),← timeLaw,
    timeLaw_neg_eq_withDensity a ha,lintegral_withDensity_eq_lintegral_mul
      volume (measurable_density a) hΨ]
  rfl

end PerronWright.BrownianFirstPassageDensityLaw
