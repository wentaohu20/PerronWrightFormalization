import PerronWright.Probability.BrownianPositiveBridgeGaussianMomentBounds
import PerronWright.Probability.BrownianPositiveBridgeTwoPointKernelBounds

/-! # Uniform polynomial entrance integrals, including short durations

The reflected killed density retains its actual small-start factor.
The two Gaussian estimates are split at the genuine standard deviation;
the resulting bound holds at every positive duration below a fixed T.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeEntranceMomentBounds

open BrownianPositiveKilledEndpoint BrownianPositiveBridgeGaussianBounds
open BrownianPositiveBridgeGaussianMomentBounds BrownianPositiveBridgeTwoPointKernelBounds

def entranceBound (T : ℝ≥0) (n : ℕ) : ℝ :=
  2^(2*n+1)*(1+standardMoment (2*n+1)) +
    2^(2*n+3)*(T : ℝ)^n*(1+standardMoment (2*n+2))

theorem entranceBound_nonneg (T : ℝ≥0) (n : ℕ) : 0 ≤ entranceBound T n := by
  unfold entranceBound
  have := standardMoment_nonneg (2*n+1)
  have := standardMoment_nonneg (2*n+2)
  positivity

theorem large_start_gaussian_bound (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (s : ℝ≥0) (hsa : Real.sqrt (s : ℝ) ≤ a) (n : ℕ) :
    (2^(2*n+1)*(a^(2*n+1)+(Real.sqrt (s : ℝ))^(2*n+1)*standardMoment (2*n+1)))/a ≤
      2^(2*n+1)*(1+standardMoment (2*n+1)) := by
  have hm := standardMoment_nonneg (2*n+1)
  have hp : (Real.sqrt (s : ℝ))^(2*n+1) ≤ a^(2*n+1) :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsa _
  have haPow : a^(2*n) ≤ 1 := pow_le_one₀ ha.le ha1
  apply (div_le_iff₀ ha).mpr
  calc
    _ ≤ 2^(2*n+1)*(a^(2*n+1)+a^(2*n+1)*standardMoment (2*n+1)) := by gcongr
    _ = (2^(2*n+1)*(1+standardMoment (2*n+1))*a^(2*n))*a := by
      rw [pow_succ]; ring
    _ ≤ _ := by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2^(2*n+1)*(1+standardMoment (2*n+1))) (sub_nonneg.mpr haPow)]

theorem small_start_gaussian_bound (a : ℝ) (ha : 0 < a)
    (s T : ℝ≥0) (hs : 0 < s) (hsT : s ≤ T) (has : a ≤ Real.sqrt (s : ℝ)) (n : ℕ) :
    (2/(s : ℝ))*(2^(2*n+2)*(a^(2*n+2)+(Real.sqrt (s : ℝ))^(2*n+2)*standardMoment (2*n+2))) ≤
      2^(2*n+3)*(T : ℝ)^n*(1+standardMoment (2*n+2)) := by
  have hm := standardMoment_nonneg (2*n+2)
  have hp : a^(2*n+2) ≤ (Real.sqrt (s : ℝ))^(2*n+2) := pow_le_pow_left₀ ha.le has _
  have hsqrt : (Real.sqrt (s : ℝ))^2 = (s : ℝ) := Real.sq_sqrt s.property
  have he : (Real.sqrt (s : ℝ))^(2*n+2) = (s : ℝ)^(n+1) := by
    calc
      _ = ((Real.sqrt (s : ℝ))^2)^(n+1) := by rw [← pow_mul]; congr 1
      _ = _ := by rw [hsqrt]
  calc
    _ ≤ (2/(s : ℝ))*(2^(2*n+2)*((Real.sqrt (s : ℝ))^(2*n+2)+
        (Real.sqrt (s : ℝ))^(2*n+2)*standardMoment (2*n+2))) := by gcongr
    _ = 2^(2*n+3)*(s : ℝ)^n*(1+standardMoment (2*n+2)) := by
      rw [he,pow_succ]
      have hsR : (s : ℝ) ≠ 0 := ne_of_gt hs
      field_simp
      ring
    _ ≤ _ := by gcongr

theorem normalized_density_abs_pow_le_gaussian (a : ℝ) (ha : 0 < a)
    (s : ℝ≥0) (hs : 0 < s) (n : ℕ) (y : ℝ) :
    (density a s y/ENNReal.ofReal a)*ENNReal.ofReal (|y|^(2*n+1)) ≤
      ENNReal.ofReal (2/(s : ℝ))*gaussianPDF a s y*ENNReal.ofReal (|y|^(2*n+2)) := by
  by_cases hy : 0 < y
  · have hd := densityReal_div_start_le_gaussian a ha s hs y hy
    have hp : densityReal a s y/a*|y|^(2*n+1) ≤
        (2/(s : ℝ))*gaussianPDFReal a s y*|y|^(2*n+2) := by
      calc
        _ ≤ ((2*y/(s : ℝ))*gaussianPDFReal a s y)*|y|^(2*n+1) :=
          mul_le_mul_of_nonneg_right hd (by positivity)
        _ = _ := by rw [abs_of_pos hy,show 2*n+2 = (2*n+1)+1 by omega,pow_succ]; ring
    convert ENNReal.ofReal_le_ofReal hp using 1
    · rw [ENNReal.ofReal_mul (div_nonneg (densityReal_nonneg a ha s hs y) ha.le),
        ENNReal.ofReal_div_of_pos ha]
      rfl
    · rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) (gaussianPDFReal_nonneg _ _ _)),
        ENNReal.ofReal_mul (by positivity)]
      rfl
  · simp only [density,densityReal,Set.indicator,mem_Ioi,if_neg hy,
      ENNReal.ofReal_zero,ENNReal.zero_div,zero_mul]
    exact zero_le

theorem uniform_entrance_moment_bound (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (s T : ℝ≥0) (hs : 0 < s) (hsT : s ≤ T) (n : ℕ) :
    (∫⁻ y : ℝ, (density a s y/ENNReal.ofReal a)*ENNReal.ofReal (|y|^(2*n+1))) ≤
      ENNReal.ofReal (entranceBound T n) := by
  have hmeas : Measurable (fun y : ℝ ↦ gaussianPDF a s y*ENNReal.ofReal (|y|^(2*n+1))) := by fun_prop
  by_cases hsa : Real.sqrt (s : ℝ) ≤ a
  · calc
      _ ≤ ∫⁻ y : ℝ, (gaussianPDF a s y/ENNReal.ofReal a)*ENNReal.ofReal (|y|^(2*n+1)) :=
        lintegral_mono (fun y ↦ mul_le_mul' (ENNReal.div_le_div_right (density_le_gaussian a y s) _) le_rfl)
      _ = (∫⁻ y : ℝ, gaussianPDF a s y*ENNReal.ofReal (|y|^(2*n+1)))/ENNReal.ofReal a := by
        simp only [div_eq_mul_inv]
        simp_rw [show ∀ y : ℝ, gaussianPDF a s y*(ENNReal.ofReal a)⁻¹*ENNReal.ofReal (|y|^(2*n+1)) =
          (gaussianPDF a s y*ENNReal.ofReal (|y|^(2*n+1)))*(ENNReal.ofReal a)⁻¹ by intro y; ac_rfl]
        rw [lintegral_mul_const _ hmeas]
      _ ≤ ENNReal.ofReal (2^(2*n+1)*(a^(2*n+1)+(Real.sqrt (s : ℝ))^(2*n+1)*standardMoment (2*n+1)))/ENNReal.ofReal a :=
        ENNReal.div_le_div_right (gaussianPDF_abs_moment_bound a ha.le s hs _) _
      _ = ENNReal.ofReal ((2^(2*n+1)*(a^(2*n+1)+(Real.sqrt (s : ℝ))^(2*n+1)*standardMoment (2*n+1)))/a) :=
        (ENNReal.ofReal_div_of_pos ha).symm
      _ ≤ ENNReal.ofReal (2^(2*n+1)*(1+standardMoment (2*n+1))) :=
        ENNReal.ofReal_le_ofReal (large_start_gaussian_bound a ha ha1 s hsa n)
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        unfold entranceBound
        have := standardMoment_nonneg (2*n+2)
        exact le_add_of_nonneg_right (by positivity)
  · have has : a ≤ Real.sqrt (s : ℝ) := (lt_of_not_ge hsa).le
    calc
      _ ≤ ∫⁻ y : ℝ, ENNReal.ofReal (2/(s : ℝ))*gaussianPDF a s y*ENNReal.ofReal (|y|^(2*n+2)) :=
        lintegral_mono (normalized_density_abs_pow_le_gaussian a ha s hs n)
      _ = ENNReal.ofReal (2/(s : ℝ))*(∫⁻ y : ℝ, gaussianPDF a s y*ENNReal.ofReal (|y|^(2*n+2))) := by
        simp_rw [mul_assoc]
        rw [lintegral_const_mul _ (by fun_prop)]
      _ ≤ ENNReal.ofReal (2/(s : ℝ))*ENNReal.ofReal (2^(2*n+2)*(a^(2*n+2)+(Real.sqrt (s : ℝ))^(2*n+2)*standardMoment (2*n+2))) :=
        mul_le_mul' le_rfl (gaussianPDF_abs_moment_bound a ha.le s hs _)
      _ = ENNReal.ofReal ((2/(s : ℝ))*(2^(2*n+2)*(a^(2*n+2)+(Real.sqrt (s : ℝ))^(2*n+2)*standardMoment (2*n+2)))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (2^(2*n+3)*(T : ℝ)^n*(1+standardMoment (2*n+2))) :=
        ENNReal.ofReal_le_ofReal (small_start_gaussian_bound a ha s T hs hsT has n)
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        unfold entranceBound
        have := standardMoment_nonneg (2*n+1)
        exact le_add_of_nonneg_left (by positivity)

end PerronWright.BrownianPositiveBridgeEntranceMomentBounds
