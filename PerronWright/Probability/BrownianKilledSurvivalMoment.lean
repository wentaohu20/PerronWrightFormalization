import PerronWright.Probability.BrownianKilledHarmonicMoment
import PerronWright.Probability.BrownianPositiveBridgeGaussianMomentBounds

/-! # Actual killed survival mass divided by its initial point

The bound is uniform over every positive start and positive time. For a
large start the literal killed law is a subprobability; for a small start
the proved Gaussian difference and true Gaussian first absolute moment
give the inverse-square-root time estimate. No survival estimate premise
is introduced.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledSurvivalMoment

open BrownianPathLaw BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance
open BrownianPositiveBridgeGaussianMomentBounds BrownianKilledHarmonicMoment

def survivalCoefficient : ℝ := 4*(1+standardMoment 1)

theorem survivalCoefficient_ge_one : 1 ≤ survivalCoefficient := by
  unfold survivalCoefficient
  have hm := standardMoment_nonneg 1
  linarith

theorem law_mass_le_one (a : ℝ) (t : ℝ≥0) : law a t univ ≤ 1 := by
  have hm : Measurable (fun f : Path ↦ f t+a) := (continuous_eval t).measurable.add_const a
  rw [law,Measure.map_apply hm MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ]
  exact (measure_mono (subset_univ _)).trans_eq (measure_univ : pathLaw univ = 1)

theorem normalized_density_le_first_gaussian (a : ℝ) (ha : 0 < a) (s : ℝ≥0)
    (hs : 0 < s) (y : ℝ) : density a s y/ENNReal.ofReal a ≤
      ENNReal.ofReal (2/(s : ℝ))*gaussianPDF a s y*ENNReal.ofReal |y| := by
  by_cases hy : 0 < y
  · rw [density,← ENNReal.ofReal_div_of_pos ha]
    have hb := BrownianPositiveBridgeGaussianBounds.densityReal_div_start_le_gaussian a ha s hs y hy
    have he : (2*y/(s : ℝ))*gaussianPDFReal a s y =
        (2/(s : ℝ))*gaussianPDFReal a s y*|y| := by rw [abs_of_pos hy]; ring
    rw [he] at hb
    have hn : 0 ≤ 2/(s : ℝ) := by positivity
    simpa only [ENNReal.ofReal_mul hn,ENNReal.ofReal_mul (mul_nonneg hn (gaussianPDFReal_nonneg a s y)),gaussianPDF]
      using ENNReal.ofReal_le_ofReal hb
  · simp only [density,densityReal,Set.indicator,mem_Ioi,if_neg hy,ENNReal.ofReal_zero,ENNReal.zero_div]
    exact zero_le

theorem normalized_density_integral_eq_mass (a : ℝ) (ha : 0 < a) (s : ℝ≥0) (hs : 0 < s) :
    (∫⁻ y : ℝ, density a s y/ENNReal.ofReal a) = law a s univ/ENNReal.ofReal a := by
  have he : (∫⁻ y : ℝ, density a s y) = law a s univ := by
    rw [law_eq_withDensity a ha s hs,withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
  simp only [div_eq_mul_inv]
  rw [lintegral_mul_const _ (measurable_density a s),he]

theorem normalized_survival_mass_bound (a : ℝ) (ha : 0 < a) (s : ℝ≥0) (hs : 0 < s) :
    law a s univ/ENNReal.ofReal a ≤ ENNReal.ofReal (survivalCoefficient/Real.sqrt (s : ℝ)) := by
  have hsR : (0 : ℝ) < s := hs
  have hsqrt : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hsR
  have hsq : (Real.sqrt (s : ℝ))^2 = (s : ℝ) := Real.sq_sqrt s.property
  by_cases haSmall : a ≤ Real.sqrt (s : ℝ)
  · rw [← normalized_density_integral_eq_mass a ha s hs]
    calc
      _ ≤ ∫⁻ y : ℝ, ENNReal.ofReal (2/(s : ℝ))*gaussianPDF a s y*ENNReal.ofReal |y| :=
        lintegral_mono (normalized_density_le_first_gaussian a ha s hs)
      _ = ENNReal.ofReal (2/(s : ℝ))*(∫⁻ y : ℝ, gaussianPDF a s y*ENNReal.ofReal |y|) := by
        have hm : Measurable (fun y : ℝ ↦ gaussianPDF a s y*ENNReal.ofReal |y|) := by fun_prop
        simpa only [mul_assoc] using lintegral_const_mul (μ := volume) (ENNReal.ofReal (2/(s : ℝ))) hm
      _ ≤ ENNReal.ofReal (2/(s : ℝ))*ENNReal.ofReal (2*(a+Real.sqrt (s : ℝ)*standardMoment 1)) := by
        apply mul_le_mul' le_rfl
        simpa only [pow_one] using gaussianPDF_abs_moment_bound a ha.le s hs 1
      _ = ENNReal.ofReal ((2/(s : ℝ))*(2*(a+Real.sqrt (s : ℝ)*standardMoment 1))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (survivalCoefficient/Real.sqrt (s : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ (2/(s : ℝ))*(2*(Real.sqrt (s : ℝ)+Real.sqrt (s : ℝ)*standardMoment 1)) := by
            gcongr
          _ = _ := by
            unfold survivalCoefficient
            field_simp [ne_of_gt hsR,ne_of_gt hsqrt]
            rw [hsq]
            ring
  · have haLarge : Real.sqrt (s : ℝ) ≤ a := (lt_of_not_ge haSmall).le
    calc
      _ ≤ 1/ENNReal.ofReal (Real.sqrt (s : ℝ)) :=
        ENNReal.div_le_div (law_mass_le_one a s) (ENNReal.ofReal_le_ofReal haLarge)
      _ = ENNReal.ofReal (1/Real.sqrt (s : ℝ)) := by rw [ENNReal.ofReal_div_of_pos hsqrt,ENNReal.ofReal_one]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right survivalCoefficient_ge_one hsqrt.le)

theorem normalized_density_mass_bound (a : ℝ) (ha : 0 < a) (s : ℝ≥0) (hs : 0 < s) :
    (∫⁻ y : ℝ, density a s y/ENNReal.ofReal a) ≤
      ENNReal.ofReal (survivalCoefficient/Real.sqrt (s : ℝ)) := by
  rw [normalized_density_integral_eq_mass a ha s hs]
  exact normalized_survival_mass_bound a ha s hs

theorem normalized_density_mass_mul_sqrt_bound (a : ℝ) (ha : 0 < a)
    (s : ℝ≥0) (hs : 0 < s) (h : ℝ≥0) (hhs : h ≤ s) :
    (∫⁻ y : ℝ, density a s y/ENNReal.ofReal a)*ENNReal.ofReal (Real.sqrt (h : ℝ)) ≤
      ENNReal.ofReal survivalCoefficient := by
  have hsR : (0 : ℝ) < s := hs
  have hsqrt := Real.sqrt_pos.mpr hsR
  have hc : 0 ≤ survivalCoefficient := (by norm_num : (0 : ℝ) ≤ 1).trans survivalCoefficient_ge_one
  calc
    _ ≤ ENNReal.ofReal (survivalCoefficient/Real.sqrt (s : ℝ))*ENNReal.ofReal (Real.sqrt (h : ℝ)) :=
      mul_le_mul' (normalized_density_mass_bound a ha s hs) le_rfl
    _ = ENNReal.ofReal ((survivalCoefficient/Real.sqrt (s : ℝ))*Real.sqrt (h : ℝ)) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (survivalCoefficient/Real.sqrt (s : ℝ))*Real.sqrt (s : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hhs) (div_nonneg hc hsqrt.le)
        _ = _ := div_mul_cancel₀ _ (ne_of_gt hsqrt)

end PerronWright.BrownianKilledSurvivalMoment
