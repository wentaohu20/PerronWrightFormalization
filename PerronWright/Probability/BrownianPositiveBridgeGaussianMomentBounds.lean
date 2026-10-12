import PerronWright.Probability.BrownianPositiveBridgeGaussianBounds

/-! # Literal Gaussian moments used at both ends of a positive bridge

All constants below are integrals under the actual standard Gaussian
probability measure.  Shift and dilation of that measure give the bounds;
there is no moment or endpoint-limit premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeGaussianMomentBounds

def standardMoment (k : ℕ) : ℝ := ∫ z : ℝ, |z|^k ∂gaussianReal 0 1

theorem gaussian_abs_pow_integrable (a : ℝ) (s : ℝ≥0) (k : ℕ) :
    Integrable (fun z : ℝ ↦ |z|^k) (gaussianReal a s) := by
  simpa only [id_eq,Real.norm_eq_abs] using
    (memLp_id_gaussianReal' (μ := a) (v := s) k (by simp)).integrable_norm_pow' (p := k)

theorem standardMoment_nonneg (k : ℕ) : 0 ≤ standardMoment k :=
  integral_nonneg (fun _ ↦ by positivity)

theorem abs_shift_sqrt_pow_le (a : ℝ) (ha : 0 ≤ a) (s : ℝ≥0) (k : ℕ) (z : ℝ) :
    |a+Real.sqrt (s : ℝ)*z|^k ≤
      2^k*(a^k+(Real.sqrt (s : ℝ))^k*|z|^k) := by
  have htriangle : |a+Real.sqrt (s : ℝ)*z| ≤ a+Real.sqrt (s : ℝ)*|z| := by
    calc
      _ ≤ |a|+|Real.sqrt (s : ℝ)*z| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg ha,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (a+Real.sqrt (s : ℝ)*|z|)^k := pow_le_pow_left₀ (abs_nonneg _) htriangle _
    _ ≤ 2^(k-1)*(a^k+(Real.sqrt (s : ℝ)*|z|)^k) :=
      add_pow_le ha (by positivity) _
    _ ≤ _ := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le k 1)) (by positivity)

theorem gaussian_abs_moment_bound (a : ℝ) (ha : 0 ≤ a) (s : ℝ≥0) (k : ℕ) :
    (∫ y : ℝ, |y|^k ∂gaussianReal a s) ≤
      2^k*(a^k+(Real.sqrt (s : ℝ))^k*standardMoment k) := by
  have hsqrt : (Real.sqrt (s : ℝ))^2 = (s : ℝ) := Real.sq_sqrt s.property
  have hv : NNReal.mk ((Real.sqrt (s : ℝ))^2) (sq_nonneg _) * 1 = s := by
    apply NNReal.eq
    change (Real.sqrt (s : ℝ))^2*1 = (s : ℝ)
    simpa only [mul_one] using hsqrt
  have hs : HasLaw (fun z : ℝ ↦ Real.sqrt (s : ℝ)*z)
      (gaussianReal 0 s) (gaussianReal 0 1) := by
    simpa only [id_eq,mul_zero,hv] using
      gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt (s : ℝ))
  have hshift : HasLaw (fun z : ℝ ↦ a+Real.sqrt (s : ℝ)*z)
      (gaussianReal a s) (gaussianReal 0 1) := by
    simpa only [zero_add] using gaussianReal_const_add hs a
  have hint : Integrable (fun z : ℝ ↦ |a+Real.sqrt (s : ℝ)*z|^k) (gaussianReal 0 1) :=
    (hshift.hasGaussianLaw.memLp (by simp : (k : ℝ≥0∞) ≠ ∞)).integrable_norm_pow'
      (p := k) |>.congr (by filter_upwards [] with z; simp only [Real.norm_eq_abs])
  have hdom : Integrable
      (fun z : ℝ ↦ 2^k*(a^k+(Real.sqrt (s : ℝ))^k*|z|^k)) (gaussianReal 0 1) :=
    ((integrable_const _).add ((gaussian_abs_pow_integrable 0 1 k).const_mul _)).const_mul _
  calc
    _ = ∫ z : ℝ, |a+Real.sqrt (s : ℝ)*z|^k ∂gaussianReal 0 1 := by
      simpa only [Function.comp_def] using
        (hshift.integral_comp ((gaussian_abs_pow_integrable a s k).aestronglyMeasurable)).symm
    _ ≤ ∫ z : ℝ, 2^k*(a^k+(Real.sqrt (s : ℝ))^k*|z|^k) ∂gaussianReal 0 1 :=
      integral_mono hint hdom (abs_shift_sqrt_pow_le a ha s k)
    _ = _ := by
      rw [integral_const_mul,integral_add (integrable_const _)
        ((gaussian_abs_pow_integrable 0 1 k).const_mul _),integral_const_mul]
      simp [integral_const,standardMoment]

theorem gaussianPDF_abs_moment_bound (a : ℝ) (ha : 0 ≤ a)
    (s : ℝ≥0) (hs : 0 < s) (k : ℕ) :
    (∫⁻ y : ℝ, gaussianPDF a s y*ENNReal.ofReal (|y|^k)) ≤
      ENNReal.ofReal (2^k*(a^k+(Real.sqrt (s : ℝ))^k*standardMoment k)) := by
  have he : (∫⁻ y : ℝ, gaussianPDF a s y*ENNReal.ofReal (|y|^k)) =
      ENNReal.ofReal (∫ y : ℝ, |y|^k ∂gaussianReal a s) := by
    rw [ofReal_integral_eq_lintegral_ofReal (gaussian_abs_pow_integrable a s k)
      (ae_of_all _ (fun _ ↦ by positivity)),gaussianReal_of_var_ne_zero a hs.ne']
    exact (lintegral_withDensity_eq_lintegral_mul volume
      (measurable_gaussianPDF a s) (by fun_prop)).symm
  rw [he]
  exact ENNReal.ofReal_le_ofReal (gaussian_abs_moment_bound a ha s k)

end PerronWright.BrownianPositiveBridgeGaussianMomentBounds
