import PerronWright.Probability.BrownianPositiveBridgeGaussianMomentBounds

/-! # Centered and endpoint-weighted genuine Gaussian moments

The constants are finite integrals of the actual standard Gaussian.
Translation of its true law supplies bounds independent of the center.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianGaussianCenteredWeightedMoments

open BrownianPositiveBridgeGaussianMomentBounds

def centeredCoefficient (k : ℕ) : ℝ := 2^k*standardMoment k

def centeredBound (h : ℝ≥0) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (h : ℝ))^k*centeredCoefficient k)

theorem centeredCoefficient_nonneg (k : ℕ) : 0 ≤ centeredCoefficient k :=
  mul_nonneg (by positivity) (standardMoment_nonneg k)

theorem centeredBound_ne_top (h : ℝ≥0) (k : ℕ) : centeredBound h k ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem gaussian_centered_abs_moment_bound (x : ℝ) (h : ℝ≥0) (hh : 0 < h)
    (k : ℕ) (hk : 0 < k) :
    (∫⁻ y : ℝ, gaussianPDF x h y*ENNReal.ofReal (|y-x|^k)) ≤ centeredBound h k := by
  have hm : Measurable (fun z : ℝ ↦ ENNReal.ofReal (|z|^k)) := by fun_prop
  have hsub : Measurable (fun z : ℝ ↦ z-x) := by fun_prop
  have hl := lintegral_map hm hsub (μ := gaussianReal x h)
  rw [gaussianReal_map_sub_const,sub_self] at hl
  have hφ : Measurable (fun y : ℝ ↦ ENNReal.ofReal (|y-x|^k)) := by fun_prop
  have he : (∫⁻ y : ℝ, gaussianPDF x h y*ENNReal.ofReal (|y-x|^k)) =
      ∫⁻ y : ℝ, ENNReal.ofReal (|y-x|^k) ∂gaussianReal x h := by
    rw [gaussianReal_of_var_ne_zero x (ne_of_gt hh),
      lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF x h) hφ]
    rfl
  have hzero : (∫⁻ y : ℝ, gaussianPDF 0 h y*ENNReal.ofReal (|y|^k)) =
      ∫⁻ y : ℝ, ENNReal.ofReal (|y|^k) ∂gaussianReal 0 h := by
    rw [gaussianReal_of_var_ne_zero 0 (ne_of_gt hh),
      lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF 0 h) hm]
    rfl
  rw [he,← hl,← hzero]
  have hb := gaussianPDF_abs_moment_bound 0 (by norm_num) h hh k
  simpa only [zero_pow hk.ne',zero_add,centeredBound,centeredCoefficient,mul_assoc,mul_comm,mul_left_comm] using hb

theorem positive_weight_centered_fourth_bound (x : ℝ) (hx : 0 ≤ x)
    (h : ℝ≥0) (hh : 0 < h) :
    (∫⁻ y : ℝ, gaussianPDF x h y*ENNReal.ofReal y*ENNReal.ofReal (|y-x|^4)) ≤
      ENNReal.ofReal x*centeredBound h 4+centeredBound h 5 := by
  have hpoint (y : ℝ) : ENNReal.ofReal y*ENNReal.ofReal (|y-x|^4) ≤
      ENNReal.ofReal x*ENNReal.ofReal (|y-x|^4)+ENNReal.ofReal (|y-x|^5) := by
    have hy : y ≤ x+|y-x| := by have he := le_abs_self (y-x); linarith
    calc
      _ ≤ (ENNReal.ofReal x+ENNReal.ofReal |y-x|)*ENNReal.ofReal (|y-x|^4) := by
        apply mul_le_mul' _ le_rfl
        simpa only [ENNReal.ofReal_add hx (abs_nonneg _)] using ENNReal.ofReal_le_ofReal hy
      _ = _ := by
        rw [add_mul,← ENNReal.ofReal_mul (abs_nonneg _)]
        congr 2
        ring
  have hm4 : Measurable (fun y : ℝ ↦ gaussianPDF x h y*ENNReal.ofReal (|y-x|^4)) := by fun_prop
  have hm5 : Measurable (fun y : ℝ ↦ gaussianPDF x h y*ENNReal.ofReal (|y-x|^5)) := by fun_prop
  calc
    _ ≤ ∫⁻ y : ℝ, ENNReal.ofReal x*(gaussianPDF x h y*ENNReal.ofReal (|y-x|^4))+
        gaussianPDF x h y*ENNReal.ofReal (|y-x|^5) := by
      apply lintegral_mono
      intro y
      have he := mul_le_mul' (le_refl (gaussianPDF x h y)) (hpoint y)
      simp only [mul_add] at he
      simpa only [mul_assoc,mul_comm,mul_left_comm] using he
    _ = ENNReal.ofReal x*(∫⁻ y : ℝ, gaussianPDF x h y*ENNReal.ofReal (|y-x|^4))+
        (∫⁻ y : ℝ, gaussianPDF x h y*ENNReal.ofReal (|y-x|^5)) := by
      have hmleft : Measurable (fun y : ℝ ↦ ENNReal.ofReal x*(gaussianPDF x h y*ENNReal.ofReal (|y-x|^4))) := hm4.const_mul _
      rw [lintegral_add_left hmleft,lintegral_const_mul _ hm4]
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl (gaussian_centered_abs_moment_bound x h hh 4 (by norm_num)))
      (gaussian_centered_abs_moment_bound x h hh 5 (by norm_num))

theorem square_weight_centered_fourth_bound (x : ℝ) (h : ℝ≥0) (hh : 0 < h) :
    (∫⁻ y : ℝ, gaussianPDF x h y*ENNReal.ofReal (y^2)*ENNReal.ofReal (|y-x|^4)) ≤
      ENNReal.ofReal (2*x^2)*centeredBound h 4+2*centeredBound h 6 := by
  have hpoint (y : ℝ) : ENNReal.ofReal (y^2)*ENNReal.ofReal (|y-x|^4) ≤
      ENNReal.ofReal (2*x^2)*ENNReal.ofReal (|y-x|^4)+2*ENNReal.ofReal (|y-x|^6) := by
    have hy : y^2 ≤ 2*x^2+2*|y-x|^2 := by
      rw [sq_abs]
      nlinarith [sq_nonneg (y-2*x)]
    calc
      _ ≤ (ENNReal.ofReal (2*x^2)+ENNReal.ofReal (2*|y-x|^2))*ENNReal.ofReal (|y-x|^4) := by
        apply mul_le_mul' _ le_rfl
        simpa only [ENNReal.ofReal_add (by positivity : 0 ≤ 2*x^2) (by positivity : 0 ≤ 2*|y-x|^2)]
          using ENNReal.ofReal_le_ofReal hy
      _ = _ := by
        rw [add_mul,← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*|y-x|^2)]
        rw [show 2*|y-x|^2*|y-x|^4 = 2*|y-x|^6 by ring]
        have he : ENNReal.ofReal (2*|y-x|^6) = 2*ENNReal.ofReal (|y-x|^6) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),ENNReal.ofReal_ofNat]
        rw [he]
  have hm4 : Measurable (fun y : ℝ ↦ gaussianPDF x h y*ENNReal.ofReal (|y-x|^4)) := by fun_prop
  have hm6 : Measurable (fun y : ℝ ↦ gaussianPDF x h y*ENNReal.ofReal (|y-x|^6)) := by fun_prop
  calc
    _ ≤ ∫⁻ y : ℝ, ENNReal.ofReal (2*x^2)*(gaussianPDF x h y*ENNReal.ofReal (|y-x|^4))+
        2*(gaussianPDF x h y*ENNReal.ofReal (|y-x|^6)) := by
      apply lintegral_mono
      intro y
      have he := mul_le_mul' (le_refl (gaussianPDF x h y)) (hpoint y)
      simp only [mul_add] at he
      simpa only [mul_assoc,mul_comm,mul_left_comm] using he
    _ = ENNReal.ofReal (2*x^2)*(∫⁻ y : ℝ, gaussianPDF x h y*ENNReal.ofReal (|y-x|^4))+
        2*(∫⁻ y : ℝ, gaussianPDF x h y*ENNReal.ofReal (|y-x|^6)) := by
      have hmleft : Measurable (fun y : ℝ ↦ ENNReal.ofReal (2*x^2)*(gaussianPDF x h y*ENNReal.ofReal (|y-x|^4))) := hm4.const_mul _
      rw [lintegral_add_left hmleft,lintegral_const_mul _ hm4,lintegral_const_mul _ hm6]
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl (gaussian_centered_abs_moment_bound x h hh 4 (by norm_num)))
      (mul_le_mul' le_rfl (gaussian_centered_abs_moment_bound x h hh 6 (by norm_num)))

theorem centeredBound_fourth (h : ℝ≥0) :
    centeredBound h 4 = ENNReal.ofReal ((h : ℝ)^2)*ENNReal.ofReal (centeredCoefficient 4) := by
  have hs : (Real.sqrt (h : ℝ))^2 = (h : ℝ) := Real.sq_sqrt h.property
  have he : (Real.sqrt (h : ℝ))^4 = (h : ℝ)^2 := by
    calc
      _ = ((Real.sqrt (h : ℝ))^2)^2 := by ring
      _ = _ := by rw [hs]
  unfold centeredBound
  rw [he,ENNReal.ofReal_mul (sq_nonneg _)]

theorem centeredBound_fifth (h : ℝ≥0) :
    centeredBound h 5 = ENNReal.ofReal ((h : ℝ)^2)*ENNReal.ofReal (Real.sqrt (h : ℝ))*
      ENNReal.ofReal (centeredCoefficient 5) := by
  have hs : (Real.sqrt (h : ℝ))^2 = (h : ℝ) := Real.sq_sqrt h.property
  have he : (Real.sqrt (h : ℝ))^5 = (h : ℝ)^2*Real.sqrt (h : ℝ) := by
    calc
      _ = ((Real.sqrt (h : ℝ))^2)^2*Real.sqrt (h : ℝ) := by ring
      _ = _ := by rw [hs]
  unfold centeredBound
  rw [he,ENNReal.ofReal_mul (by positivity : 0 ≤ (h : ℝ)^2*Real.sqrt (h : ℝ)),
    ENNReal.ofReal_mul (sq_nonneg _)]

theorem centeredBound_sixth (h : ℝ≥0) :
    centeredBound h 6 = ENNReal.ofReal ((h : ℝ)^3)*ENNReal.ofReal (centeredCoefficient 6) := by
  have hs : (Real.sqrt (h : ℝ))^2 = (h : ℝ) := Real.sq_sqrt h.property
  have he : (Real.sqrt (h : ℝ))^6 = (h : ℝ)^3 := by
    calc
      _ = ((Real.sqrt (h : ℝ))^2)^3 := by ring
      _ = _ := by rw [hs]
  unfold centeredBound
  rw [he,ENNReal.ofReal_mul (by positivity : 0 ≤ (h : ℝ)^3)]

end PerronWright.BrownianGaussianCenteredWeightedMoments
