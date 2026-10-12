import PerronWright.Probability.BrownianPositiveBridgeGaussianMomentBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Actual Gaussian exponential-square integral and factorial moment growth

The constant is evaluated under the literal standard Gaussian measure.
The factorial estimates follow pointwise from the exponential series,
not from an exponential-integrability premise about bridge areas.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianGaussianSquareMomentGrowth

open BrownianPositiveBridgeGaussianMomentBounds

def gaussianSquareConstant : ℝ :=
  (Real.sqrt (2*Real.pi))⁻¹*Real.sqrt (4*Real.pi)

theorem gaussianSquareConstant_pos : 0 < gaussianSquareConstant := by
  unfold gaussianSquareConstant
  positivity

private theorem weighted_gaussian_exp_square (z : ℝ) :
    gaussianPDF 0 1 z*ENNReal.ofReal (Real.exp (z^2/4)) =
      ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(1/4:ℝ)*z^2)) := by
  rw [gaussianPDF,← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  unfold gaussianPDFReal
  simp only [NNReal.coe_one,mul_one,sub_zero,mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem lintegral_standard_gaussian_exp_square :
    (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (z^2/4)) ∂gaussianReal 0 1) =
      ENNReal.ofReal gaussianSquareConstant := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1:ℝ≥0) ≠ 0),
    lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF 0 1) (by fun_prop)]
  dsimp only [Pi.mul_apply]
  simp_rw [weighted_gaussian_exp_square]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).const_mul _)
    (ae_of_all _ (fun _ ↦ by positivity)),integral_const_mul,integral_gaussian]
  congr 1
  unfold gaussianSquareConstant
  congr 2
  ring

theorem integrable_standard_gaussian_exp_square :
    Integrable (fun z : ℝ ↦ Real.exp (z^2/4)) (gaussianReal 0 1) := by
  refine ⟨(by fun_prop),?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ ↦ (Real.exp_pos _).le))).mpr
  rw [lintegral_standard_gaussian_exp_square]
  exact ENNReal.ofReal_lt_top

theorem integral_standard_gaussian_exp_square :
    (∫ z : ℝ, Real.exp (z^2/4) ∂gaussianReal 0 1) = gaussianSquareConstant := by
  have h := lintegral_standard_gaussian_exp_square
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_standard_gaussian_exp_square
    (ae_of_all _ (fun _ ↦ (Real.exp_pos _).le))] at h
  exact ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (fun _ ↦ (Real.exp_pos _).le)) gaussianSquareConstant_pos.le |>.mp h

theorem gaussianSquareConstant_ge_one : 1 ≤ gaussianSquareConstant := by
  rw [← integral_standard_gaussian_exp_square]
  simpa only [integral_const,probReal_univ,one_smul] using
    integral_mono (integrable_const (1:ℝ)) integrable_standard_gaussian_exp_square
      (fun z : ℝ ↦ Real.one_le_exp (by positivity : 0 ≤ z^2/4))

theorem standardGaussian_even_pointwise_bound (n : ℕ) (z : ℝ) :
    |z|^(2*n) ≤ 4^n*(n.factorial:ℝ)*Real.exp (z^2/4) := by
  have hf : (0:ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have h := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (z^2/4) (by positivity : 0 ≤ z^2/4) n)
  calc
    _ = (4:ℝ)^n*(z^2/4)^n := by
      rw [pow_mul,← mul_pow,sq_abs]
      congr 1
      ring
    _ ≤ (4:ℝ)^n*(Real.exp (z^2/4)*(n.factorial:ℝ)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem standardMoment_even_factorial_bound (n : ℕ) :
    standardMoment (2*n) ≤ 4^n*(n.factorial:ℝ)*gaussianSquareConstant := by
  calc
    _ ≤ ∫ z : ℝ, 4^n*(n.factorial:ℝ)*Real.exp (z^2/4) ∂gaussianReal 0 1 :=
      integral_mono (gaussian_abs_pow_integrable 0 1 (2*n))
        (integrable_standard_gaussian_exp_square.const_mul _)
        (standardGaussian_even_pointwise_bound n)
    _ = _ := by rw [integral_const_mul,integral_standard_gaussian_exp_square]

theorem standardMoment_odd_factorial_bound (n : ℕ) :
    standardMoment (2*n+1) ≤ 1+4^(n+1)*((n+1).factorial:ℝ)*gaussianSquareConstant := by
  have hpoint (z : ℝ) : |z|^(2*n+1) ≤ 1+|z|^(2*(n+1)) := by
    by_cases hz : |z| ≤ 1
    · exact (pow_le_one₀ (abs_nonneg z) hz).trans (le_add_of_nonneg_right (by positivity))
    · exact (pow_le_pow_right₀ (lt_of_not_ge hz).le (by omega : 2*n+1 ≤ 2*(n+1))).trans
        (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1))
  calc
    _ ≤ ∫ z : ℝ, 1+|z|^(2*(n+1)) ∂gaussianReal 0 1 :=
      integral_mono (gaussian_abs_pow_integrable 0 1 (2*n+1))
        ((integrable_const _).add (gaussian_abs_pow_integrable 0 1 (2*(n+1)))) hpoint
    _ = 1+standardMoment (2*(n+1)) := by
      rw [integral_add (integrable_const _) (gaussian_abs_pow_integrable 0 1 _)]
      simp [standardMoment]
    _ ≤ _ := add_le_add le_rfl (standardMoment_even_factorial_bound (n+1))

end PerronWright.BrownianGaussianSquareMomentGrowth
