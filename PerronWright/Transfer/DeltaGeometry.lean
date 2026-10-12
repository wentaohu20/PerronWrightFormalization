import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import PerronWright.Transfer.DeltaDiscGeometry

/-!
Elementary geometry and exponential decay for the two rays of a keyhole
contour that leave the singularity at `1` in directions `(3 ± 4i)/5`.
The upper and lower rays lie in the right half-plane and are parametrized
by Euclidean arclength `t`.
-/

open Real
open scoped ComplexConjugate
noncomputable section

namespace PerronWright.Transfer

private def upperDir : ℂ := ⟨3 / 5, 4 / 5⟩
private def lowerDir : ℂ := ⟨3 / 5, -(4 / 5)⟩

private theorem norm_upperDir : ‖upperDir‖ = 1 := by
  rw [Complex.norm_def]
  norm_num [upperDir, Complex.normSq_apply]

private theorem norm_lowerDir : ‖lowerDir‖ = 1 := by
  rw [Complex.norm_def]
  norm_num [lowerDir, Complex.normSq_apply]

private theorem upperDir_re : upperDir.re = 3 / 5 := rfl
private theorem lowerDir_re : lowerDir.re = 3 / 5 := rfl
private theorem upperDir_abs_im : |upperDir.im| = 4 / 5 := by norm_num [upperDir]
private theorem lowerDir_abs_im : |lowerDir.im| = 4 / 5 := by norm_num [lowerDir]

private theorem lowerDir_eq_conj_upperDir : lowerDir = conj upperDir := by
  rfl

/-- Exact arclength and real-part bounds for either ray direction. -/
theorem ray_geometry (d : ℂ) (hd : ‖d‖ = 1) (hdre : d.re = 3 / 5)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖(1 : ℂ) - (1 + (t : ℂ) * d)‖ = t ∧
      1 + t / 2 ≤ ‖(1 : ℂ) + (t : ℂ) * d‖ := by
  constructor
  · have h : (1 : ℂ) - (1 + (t : ℂ) * d) = -(t : ℂ) * d := by ring
    rw [h, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht, hd]
    ring
  · calc
      1 + t / 2 ≤ ((1 : ℂ) + (t : ℂ) * d).re := by
        simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hdre]
        nlinarith
      _ ≤ ‖(1 : ℂ) + (t : ℂ) * d‖ := Complex.re_le_norm _

theorem upper_ray_geometry {t : ℝ} (ht : 0 ≤ t) :
    ‖(1 : ℂ) - (1 + (t : ℂ) * upperDir)‖ = t ∧
      1 + t / 2 ≤ ‖(1 : ℂ) + (t : ℂ) * upperDir‖ :=
  ray_geometry upperDir norm_upperDir upperDir_re ht

theorem lower_ray_geometry {t : ℝ} (ht : 0 ≤ t) :
    ‖(1 : ℂ) - (1 + (t : ℂ) * lowerDir)‖ = t ∧
      1 + t / 2 ≤ ‖(1 : ℂ) + (t : ℂ) * lowerDir‖ :=
  ray_geometry lowerDir norm_lowerDir lowerDir_re ht

/-- A keyhole ray with the paper's slope `4/3` lies outside every
Cartesian excluded cone of smaller slope, while remaining inside the
outer-radius margin for `t < η`. -/
theorem ray_mem_cartesianDelta (d : ℂ) (hd : ‖d‖ = 1)
    (hdre : d.re = 3 / 5) (hdim : |d.im| = 4 / 5)
    {t η m : ℝ} (ht : 0 < t) (htη : t < η)
    (hm : m < 4 / 3) :
    (1 : ℂ) + (t : ℂ) * d ∈ cartesianDelta η m := by
  constructor
  · have hnorm := norm_add_le (1 : ℂ) ((t : ℂ) * d)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, hd, mul_one, norm_one] at hnorm
    linarith
  · intro hcone
    have hre : (((1 : ℂ) + (t : ℂ) * d) - 1).re = t * (3 / 5) := by
      simp [hdre]
    have him : |(((1 : ℂ) + (t : ℂ) * d) - 1).im| = t * (4 / 5) := by
      simp [abs_mul, abs_of_pos ht, hdim]
    rw [hre, him] at hcone
    nlinarith [mul_pos ht (sub_pos.mpr hm)]

theorem upper_ray_mem_cartesianDelta {t η m : ℝ}
    (ht : 0 < t) (htη : t < η) (hm : m < 4 / 3) :
    (1 : ℂ) + (t : ℂ) * upperDir ∈ cartesianDelta η m :=
  ray_mem_cartesianDelta upperDir norm_upperDir upperDir_re
    upperDir_abs_im ht htη hm

theorem lower_ray_mem_cartesianDelta {t η m : ℝ}
    (ht : 0 < t) (htη : t < η) (hm : m < 4 / 3) :
    (1 : ℂ) + (t : ℂ) * lowerDir ∈ cartesianDelta η m :=
  ray_mem_cartesianDelta lowerDir norm_lowerDir lowerDir_re
    lowerDir_abs_im ht htη hm

/-- The two rays meet the same outer circle. If their endpoint arclength
`t₀` is smaller than the available radius margin `η`, that circle lies
inside `|z| < 1 + η`. -/
theorem ray_endpoint_radius {t₀ η : ℝ} (ht₀ : 0 < t₀) (hη : t₀ < η) :
    ‖(1 : ℂ) + (t₀ : ℂ) * upperDir‖ =
        ‖(1 : ℂ) + (t₀ : ℂ) * lowerDir‖ ∧
      1 < ‖(1 : ℂ) + (t₀ : ℂ) * upperDir‖ ∧
      ‖(1 : ℂ) + (t₀ : ℂ) * upperDir‖ < 1 + η := by
  have heq : conj ((1 : ℂ) + (t₀ : ℂ) * upperDir) =
      (1 : ℂ) + (t₀ : ℂ) * lowerDir := by
    rw [lowerDir_eq_conj_upperDir]
    simp
  constructor
  · rw [← heq, Complex.norm_conj]
  constructor
  · have h := (upper_ray_geometry ht₀.le).2
    linarith
  · have h := norm_add_le (1 : ℂ) ((t₀ : ℂ) * upperDir)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₀,
      norm_upperDir, mul_one, norm_one] at h
    linarith

/-- A fixed radial segment of either ray has uniform exponential decay
in the Cauchy coefficient denominator. -/
theorem ray_inverse_rpow_bound (d : ℂ) (hd : ‖d‖ = 1)
    (hdre : d.re = 3 / 5) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    ‖(1 : ℂ) + (t : ℂ) * d‖ ^ (-(n : ℝ) - 1) ≤
      exp (-((n : ℝ) * t / 4)) := by
  let z : ℂ := (1 : ℂ) + (t : ℂ) * d
  have hnorm : 1 + t / 2 ≤ ‖z‖ := (ray_geometry d hd hdre ht).2
  have hhalf : 0 ≤ t / 2 := by positivity
  have hden : 0 < t / 2 + 2 := by linarith
  have hpre : t / 4 ≤ 2 * (t / 2) / (t / 2 + 2) := by
    apply (le_div_iff₀ hden).2
    nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
  have hlog : t / 4 ≤ log ‖z‖ :=
    hpre.trans ((le_log_one_add_of_nonneg hhalf).trans
      (Real.log_le_log (by linarith) hnorm))
  have hzpos : 0 < ‖z‖ := by linarith
  rw [Real.rpow_def_of_pos hzpos]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (Nat.cast_nonneg n)]

theorem upper_ray_inverse_rpow_bound {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t ≤ 1) (n : ℕ) :
    ‖(1 : ℂ) + (t : ℂ) * upperDir‖ ^ (-(n : ℝ) - 1) ≤
      exp (-((n : ℝ) * t / 4)) :=
  ray_inverse_rpow_bound upperDir norm_upperDir upperDir_re ht ht1 n

theorem lower_ray_inverse_rpow_bound {t : ℝ} (ht : 0 ≤ t)
    (ht1 : t ≤ 1) (n : ℕ) :
    ‖(1 : ℂ) + (t : ℂ) * lowerDir‖ ^ (-(n : ℝ) - 1) ≤
      exp (-((n : ℝ) * t / 4)) :=
  ray_inverse_rpow_bound lowerDir norm_lowerDir lowerDir_re ht ht1 n

/-- Any fixed outer arc of modulus `R > 1` has exponentially decaying
Cauchy denominator; the decay rate `log R / 2` is positive. -/
theorem outer_circle_inverse_pow_bound {R : ℝ} (hR : 1 < R)
    {z : ℂ} (hz : ‖z‖ = R) (n : ℕ) :
    ‖z⁻¹ ^ (n + 1)‖ ≤ exp (-((n : ℝ) * (log R / 2))) := by
  have hlog : 0 < log R := Real.log_pos hR
  have hRpos : 0 < R := by linarith
  have hpow : ‖z⁻¹ ^ (n + 1)‖ = R ^ (-((n : ℝ) + 1)) := by
    calc
      ‖z⁻¹ ^ (n + 1)‖ = (R⁻¹) ^ (n + 1) := by simp [hz]
      _ = (R ^ (n + 1 : ℕ))⁻¹ := by rw [inv_pow]
      _ = R ^ (-((n : ℝ) + 1)) := by
        rw [Real.rpow_neg hRpos.le]
        norm_cast
  rw [hpow, Real.rpow_def_of_pos hRpos]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hlog.le (Nat.cast_nonneg n)]

/-- The real-power estimate above is exactly an estimate for the actual
complex Cauchy denominator on the radial sides. -/
theorem ray_inverse_pow_bound (d : ℂ) (hd : ‖d‖ = 1)
    (hdre : d.re = 3 / 5) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    ‖((1 : ℂ) + (t : ℂ) * d)⁻¹ ^ (n + 1)‖ ≤
      exp (-((n : ℝ) * t / 4)) := by
  let z : ℂ := (1 : ℂ) + (t : ℂ) * d
  have hzpos : 0 < ‖z‖ := by
    have h := (ray_geometry d hd hdre ht).2
    dsimp [z] at h ⊢
    linarith
  have hpow : ‖z⁻¹ ^ (n + 1)‖ = ‖z‖ ^ (-((n : ℝ) + 1)) := by
    calc
      ‖z⁻¹ ^ (n + 1)‖ = (‖z‖⁻¹) ^ (n + 1) := by simp
      _ = (‖z‖ ^ (n + 1 : ℕ))⁻¹ := by rw [inv_pow]
      _ = ‖z‖ ^ (-((n : ℝ) + 1)) := by
        rw [Real.rpow_neg hzpos.le]
        norm_cast
  rw [hpow]
  dsimp [z]
  convert ray_inverse_rpow_bound d hd hdre ht ht1 n using 1; ring_nf

/-- Multiplying the local singular-power bound by the exact Cauchy
denominator yields the Laplace majorant of `ScratchDeltaTransfer`. -/
theorem ray_cauchy_integrand_bound (d : ℂ) (hd : ‖d‖ = 1)
    (hdre : d.re = 3 / 5) {t a C : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hC : 0 ≤ C) (n : ℕ) {F : ℂ → ℂ}
    (hF : ‖F ((1 : ℂ) + (t : ℂ) * d)‖ ≤ C * t ^ a) :
    ‖F ((1 : ℂ) + (t : ℂ) * d) *
      (((1 : ℂ) + (t : ℂ) * d)⁻¹ ^ (n + 1))‖ ≤
      C * (t ^ a * exp (-((n : ℝ) * t / 4))) := by
  rw [norm_mul]
  calc
    ‖F (1 + (t : ℂ) * d)‖ * ‖(1 + (t : ℂ) * d)⁻¹ ^ (n + 1)‖ ≤
        (C * t ^ a) * exp (-((n : ℝ) * t / 4)) := by
      exact mul_le_mul hF (ray_inverse_pow_bound d hd hdre ht ht1 n)
        (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg ht _))
    _ = _ := by ring

/-- The corresponding pointwise bound on any fixed outer circular arc. -/
theorem outer_cauchy_integrand_bound {R M : ℝ} (hR : 1 < R)
    (hM : 0 ≤ M) {z : ℂ} (hz : ‖z‖ = R) (n : ℕ) {F : ℂ → ℂ}
    (hF : ‖F z‖ ≤ M) :
    ‖F z * (z⁻¹ ^ (n + 1))‖ ≤ M * exp (-((n : ℝ) * (log R / 2))) := by
  rw [norm_mul]
  exact mul_le_mul hF (outer_circle_inverse_pow_bound hR hz n)
    (norm_nonneg _) hM


end PerronWright.Transfer
