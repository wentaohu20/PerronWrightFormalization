import PerronWright.Transfer.DeltaGeometry
import PerronWright.Transfer.KeyholeBounds
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
Actual contour-piece estimates for a keyhole coefficient argument.  This file
does not assert the still-unproved contour deformation that identifies their
sum with a Taylor coefficient.
-/

open Real MeasureTheory Set
open scoped ComplexConjugate
noncomputable section

namespace PerronWright.Transfer

/-- Integrate the genuine Cauchy integrand along one radial side, including
its constant unit tangent. The local `|1-z|^a` bound is the only hypothesis. -/
theorem radial_piece_bound {F : ℂ → ℂ} {d : ℂ} {M a : ℝ} {n : ℕ}
    (hd : ‖d‖ = 1) (hdre : d.re = 3 / 5)
    (hM : 0 ≤ M) (hM1 : M ≤ 1) (ha : -1 < a) (hn : 0 < n)
    (hF : ∀ t ∈ Ioc (0 : ℝ) M,
      ‖F ((1 : ℂ) + (t : ℂ) * d)‖ ≤ t ^ a) :
    ‖∫ t in (0 : ℝ)..M,
        d * F ((1 : ℂ) + (t : ℂ) * d) *
          (((1 : ℂ) + (t : ℂ) * d)⁻¹ ^ (n + 1))‖ ≤
      (1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1) := by
  apply PerronWright.Transfer.norm_radial_integral_le ha hM (by norm_num) hn
  intro t ht
  have ht0 : 0 ≤ t := ht.1.le
  have ht1 : t ≤ 1 := ht.2.trans hM1
  have hF' : ‖F ((1 : ℂ) + (t : ℂ) * d)‖ ≤ (1 : ℝ) * t ^ a := by
    simpa only [one_mul] using hF t ht
  have h := PerronWright.Transfer.ray_cauchy_integrand_bound d hd hdre
    ht0 ht1 (by norm_num : (0 : ℝ) ≤ 1) n hF'
  simp only [norm_mul, hd, one_mul] at *
  convert h using 1; ring_nf

/-- The radial bound follows directly from a power estimate on the
actual Cartesian dented domain: the ray's inclusion is proved rather
than supplied as a separate contour hypothesis. -/
theorem radial_piece_bound_on_cartesianDelta
    {F : ℂ → ℂ} {d : ℂ} {M a η m : ℝ} {n : ℕ}
    (hd : ‖d‖ = 1) (hdre : d.re = 3 / 5)
    (hdim : |d.im| = 4 / 5)
    (hM : 0 ≤ M) (hM1 : M ≤ 1) (hMη : M < η)
    (hm : m < 4 / 3) (ha : -1 < a) (hn : 0 < n)
    (hF : ∀ z ∈ cartesianDelta η m,
      ‖F z‖ ≤ ‖z - 1‖ ^ a) :
    ‖∫ t in (0 : ℝ)..M,
        d * F ((1 : ℂ) + (t : ℂ) * d) *
          (((1 : ℂ) + (t : ℂ) * d)⁻¹ ^ (n + 1))‖ ≤
      (1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1) := by
  apply radial_piece_bound hd hdre hM hM1 ha hn
  intro t ht
  have hmem : (1 : ℂ) + (t : ℂ) * d ∈ cartesianDelta η m :=
    ray_mem_cartesianDelta d hd hdre hdim ht.1 (ht.2.trans_lt hMη) hm
  have hdist : ‖((1 : ℂ) + (t : ℂ) * d) - 1‖ = t := by
    rw [norm_sub_rev]
    exact (ray_geometry d hd hdre ht.1.le).1
  simpa only [hdist] using hF _ hmem

/-- Actual outer-arc integral, parametrized by the usual circle map.  This
works for an arbitrary subarc `[θ₀,θ₁]` and does not require `F` to be
defined analytically on the deleted wedge. -/
theorem outer_arc_bound {F : ℂ → ℂ} {R M θ₀ θ₁ : ℝ} {n : ℕ}
    (hR : 1 < R) (hM : 0 ≤ M) (hθ : θ₀ ≤ θ₁)
    (hF : ∀ θ ∈ Icc θ₀ θ₁, ‖F (circleMap 0 R θ)‖ ≤ M) :
    ‖∫ θ in θ₀..θ₁,
        deriv (circleMap 0 R) θ *
          (F (circleMap 0 R θ) * ((circleMap 0 R θ)⁻¹ ^ (n + 1)))‖ ≤
      (θ₁ - θ₀) * (R * M * exp (-((n : ℝ) * (log R / 2)))) := by
  have hconst : ∀ θ ∈ Set.uIoc θ₀ θ₁,
      ‖deriv (circleMap 0 R) θ *
          (F (circleMap 0 R θ) * ((circleMap 0 R θ)⁻¹ ^ (n + 1)))‖ ≤
        R * M * exp (-((n : ℝ) * (log R / 2))) := by
    intro θ hθmem
    have hθmem' : θ ∈ Icc θ₀ θ₁ := Ioc_subset_Icc_self (by simpa [uIoc_of_le hθ] using hθmem)
    have hz : ‖circleMap 0 R θ‖ = R := by
      simp [norm_circleMap_zero, abs_of_pos (lt_trans zero_lt_one hR)]
    rw [norm_mul, deriv_circleMap, norm_mul, Complex.norm_I,
      norm_circleMap_zero, abs_of_pos (lt_trans zero_lt_one hR), mul_one]
    simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
      (PerronWright.Transfer.outer_cauchy_integrand_bound hR hM hz n (hF θ hθmem'))
      (le_of_lt (lt_trans zero_lt_one hR)))
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hconst
  rw [abs_of_nonneg (sub_nonneg.mpr hθ)] at hb
  convert hb using 1; ring_nf

/-- The Cauchy denominator stays uniformly bounded on the small circle
`|z-1|=1/(2n)`. This is the missing geometric input for its true
`n^(-a-1)` contribution. -/
theorem inner_circle_inverse_bound {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : ‖z - 1‖ = 1 / (2 * (n : ℝ))) :
    ‖z⁻¹ ^ (n + 1)‖ ≤ exp 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let r : ℝ := 1 / (2 * (n : ℝ))
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrhalf : r ≤ 1 / 2 := by
    dsimp [r]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hnorm : 1 - r ≤ ‖z‖ := by
    have htri := norm_sub_le z (1 : ℂ)
    have h := norm_add_le z (1 - z)
    have heq : z + (1 - z) = (1 : ℂ) := by ring
    rw [heq, norm_one, norm_sub_rev, hz] at h
    dsimp [r]
    linarith
  have hbase : 0 < 1 - r := by linarith
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hbase hnorm
  have hloginv : -log (1 - r) ≤ r / (1 - r) := by
    rw [← Real.log_inv]
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hbase)
    convert h using 1; field_simp; ring
  have hloglower : -(2 * r) ≤ log ‖z‖ := by
    have hden : 0 < 1 - r := hbase
    have hdiv : r / (1 - r) ≤ 2 * r := by
      apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg hrpos.le (sub_nonneg.mpr hrhalf)]
    have hlog := Real.log_le_log hbase hnorm
    linarith
  have hpow : ‖z⁻¹ ^ (n + 1)‖ = ‖z‖ ^ (-((n : ℝ) + 1)) := by
    calc
      ‖z⁻¹ ^ (n + 1)‖ = (‖z‖⁻¹) ^ (n + 1) := by simp
      _ = (‖z‖ ^ (n + 1 : ℕ))⁻¹ := by rw [inv_pow]
      _ = ‖z‖ ^ (-((n : ℝ) + 1)) := by
        rw [Real.rpow_neg hzpos.le]
        norm_cast
  rw [hpow, Real.rpow_def_of_pos hzpos]
  apply Real.exp_le_exp.mpr
  have hscale : r * ((n : ℝ) + 1) ≤ 1 := by
    dsimp [r]
    calc
      1 / (2 * (n : ℝ)) * ((n : ℝ) + 1) =
          ((n : ℝ) + 1) / (2 * (n : ℝ)) := by ring
      _ ≤ 1 := by
        apply (div_le_iff₀ (mul_pos (by norm_num) hn')).2
        nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  nlinarith [mul_nonneg (add_nonneg (Nat.cast_nonneg n) zero_le_one)
    (sub_nonneg.mpr hloglower)]

/-- The actual inner-circle Cauchy integral is `O(n^(-a-1))`, with an
explicit constant and no integrability restriction on `a`. -/
theorem inner_circle_piece_bound {F : ℂ → ℂ} {a : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hF : ∀ z ∈ Metric.sphere (1 : ℂ) (1 / (2 * (n : ℝ))),
      ‖F z‖ ≤ ‖z - 1‖ ^ a) :
    ‖∮ z in C((1 : ℂ), 1 / (2 * (n : ℝ))), F z * z⁻¹ ^ (n + 1)‖ ≤
      (2 * π * exp 2) * (1 / (2 * (n : ℝ))) ^ (a + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hbound : ∀ z ∈ Metric.sphere (1 : ℂ) (1 / (2 * (n : ℝ))),
      ‖F z * z⁻¹ ^ (n + 1)‖ ≤
        (1 / (2 * (n : ℝ))) ^ a * exp 2 := by
    intro z hz
    have hz' : ‖z - 1‖ = 1 / (2 * (n : ℝ)) := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    rw [norm_mul]
    exact (mul_le_mul (by simpa only [hz'] using hF z hz)
      (inner_circle_inverse_bound hn hz') (norm_nonneg _)
      (Real.rpow_nonneg hr.le _))
  have hb := circleIntegral.norm_integral_le_of_norm_le_const hr.le hbound
  calc
    ‖∮ z in C((1 : ℂ), 1 / (2 * (n : ℝ))), F z * z⁻¹ ^ (n + 1)‖ ≤
      2 * π * (1 / (2 * (n : ℝ))) *
        ((1 / (2 * (n : ℝ))) ^ a * exp 2) := hb
    _ = (2 * π * exp 2) * (1 / (2 * (n : ℝ))) ^ (a + 1) := by
      rw [Real.rpow_add hr]
      simp only [Real.rpow_one]
      ring

/-- Assembly of the four **actual integrals** in the keyhole estimate.
There is intentionally no claim here that their oriented sum equals a
Taylor coefficient; that is the separate Cauchy deformation step. -/
theorem contour_piece_sum_bound {F : ℂ → ℂ} {dUp dDown : ℂ}
    {M R B θ₀ θ₁ a : ℝ} {n : ℕ}
    (hdUp : ‖dUp‖ = 1) (hreUp : dUp.re = 3 / 5)
    (hdDown : ‖dDown‖ = 1) (hreDown : dDown.re = 3 / 5)
    (hM : 0 ≤ M) (hM1 : M ≤ 1) (hR : 1 < R) (hB : 0 ≤ B)
    (hθ : θ₀ ≤ θ₁) (ha : -1 < a) (hn : 0 < n)
    (hFUp : ∀ t ∈ Ioc (0 : ℝ) M,
      ‖F ((1 : ℂ) + (t : ℂ) * dUp)‖ ≤ t ^ a)
    (hFDown : ∀ t ∈ Ioc (0 : ℝ) M,
      ‖F ((1 : ℂ) + (t : ℂ) * dDown)‖ ≤ t ^ a)
    (hFi : ∀ z ∈ Metric.sphere (1 : ℂ) (1 / (2 * (n : ℝ))),
      ‖F z‖ ≤ ‖z - 1‖ ^ a)
    (hFo : ∀ θ ∈ Icc θ₀ θ₁, ‖F (circleMap 0 R θ)‖ ≤ B) :
    ‖(∫ t in (0 : ℝ)..M,
          dUp * F ((1 : ℂ) + (t : ℂ) * dUp) *
            (((1 : ℂ) + (t : ℂ) * dUp)⁻¹ ^ (n + 1))) +
      (∫ t in (0 : ℝ)..M,
          dDown * F ((1 : ℂ) + (t : ℂ) * dDown) *
            (((1 : ℂ) + (t : ℂ) * dDown)⁻¹ ^ (n + 1))) +
      (∮ z in C((1 : ℂ), 1 / (2 * (n : ℝ))), F z * z⁻¹ ^ (n + 1)) +
      (∫ θ in θ₀..θ₁,
          deriv (circleMap 0 R) θ *
            (F (circleMap 0 R θ) *
              ((circleMap 0 R θ)⁻¹ ^ (n + 1))))‖ ≤
      2 * ((1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1)) +
      (2 * π * exp 2) * (1 / (2 * (n : ℝ))) ^ (a + 1) +
      (θ₁ - θ₀) * (R * B * exp (-((n : ℝ) * (log R / 2)))) := by
  let U : ℂ := ∫ t in (0 : ℝ)..M,
    dUp * F ((1 : ℂ) + (t : ℂ) * dUp) *
      (((1 : ℂ) + (t : ℂ) * dUp)⁻¹ ^ (n + 1))
  let L : ℂ := ∫ t in (0 : ℝ)..M,
    dDown * F ((1 : ℂ) + (t : ℂ) * dDown) *
      (((1 : ℂ) + (t : ℂ) * dDown)⁻¹ ^ (n + 1))
  let I : ℂ := ∮ z in C((1 : ℂ), 1 / (2 * (n : ℝ))), F z * z⁻¹ ^ (n + 1)
  let O : ℂ := ∫ θ in θ₀..θ₁,
    deriv (circleMap 0 R) θ *
      (F (circleMap 0 R θ) * ((circleMap 0 R θ)⁻¹ ^ (n + 1)))
  have hU : ‖U‖ ≤ (1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1) :=
    radial_piece_bound hdUp hreUp hM hM1 ha hn hFUp
  have hL : ‖L‖ ≤ (1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1) :=
    radial_piece_bound hdDown hreDown hM hM1 ha hn hFDown
  have hI : ‖I‖ ≤ (2 * π * exp 2) * (1 / (2 * (n : ℝ))) ^ (a + 1) :=
    inner_circle_piece_bound hn hFi
  have hO : ‖O‖ ≤ (θ₁ - θ₀) * (R * B * exp (-((n : ℝ) * (log R / 2)))) :=
    outer_arc_bound hR hB hθ hFo
  change ‖U + L + I + O‖ ≤ _
  have h1 := norm_add_le U L
  have h2 := norm_add_le (U + L) I
  have h3 := norm_add_le (U + L + I) O
  linarith


end PerronWright.Transfer
