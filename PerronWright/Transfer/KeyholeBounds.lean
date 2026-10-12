import PerronWright.Transfer.Base
import Mathlib.Analysis.SumIntegralExpDecay
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
An explicit Laplace bound for the radial sides of a keyhole contour.
This is the analytic estimate needed in the remainder transfer from a
`|1-z|^a` singularity to an `n^(-a-1)` coefficient bound.
-/

open Real MeasureTheory Set
open scoped Topology

noncomputable section

namespace PerronWright.Transfer

/-- The radial Laplace contribution has the precise power of its exponential
rate, for every real exponent above the integrability threshold `-1`. -/
theorem laplace_interval_rpow_le {a M c : ℝ}
    (ha : -1 < a) (hM : 0 ≤ M) (hc : 0 < c) :
    (∫ t in (0 : ℝ)..M, t ^ a * exp (-(c * t))) ≤
      (1 / c) ^ (a + 1) * Gamma (a + 1) := by
  have ha' : 0 < a + 1 := by linarith
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi ha' hc
  have hint : IntegrableOn (fun t : ℝ => t ^ ((a + 1) - 1) * exp (-(c * t))) (Ioi 0) :=
    .of_integral_ne_zero (by rw [key]; positivity)
  rw [intervalIntegral.integral_of_le hM]
  calc
    (∫ t in Ioc (0 : ℝ) M, t ^ a * exp (-(c * t))) =
        ∫ t in Ioc (0 : ℝ) M, t ^ ((a + 1) - 1) * exp (-(c * t)) := by
          simp only [add_sub_cancel_right]
    _ ≤ ∫ t in Ioi (0 : ℝ), t ^ ((a + 1) - 1) * exp (-(c * t)) := by
      apply setIntegral_mono_set hint _ Ioc_subset_Ioi_self.eventuallyLE
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (rpow_nonneg ht.le _) (exp_nonneg _)
    _ = _ := key

/-- Scaling by a coefficient index `n` gives exactly the required
`(n : ℝ)^(-a-1)` decay along a radial keyhole side. -/
theorem laplace_ray_bound {a M c : ℝ} {n : ℕ}
    (ha : -1 < a) (hM : 0 ≤ M) (hc : 0 < c) (hn : 0 < n) :
    (∫ t in (0 : ℝ)..M, t ^ a * exp (-(c * (n : ℝ) * t))) ≤
      (1 / (c * n)) ^ (a + 1) * Gamma (a + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact laplace_interval_rpow_le ha hM (mul_pos hc hn')

/-- A complex-valued radial contour contribution obeys the same bound,
provided its pointwise norm has the standard singular-power/exponential
majorant. This is the norm estimate actually consumed by keyhole transfer. -/
theorem norm_radial_integral_le {a M c : ℝ} {n : ℕ} {f : ℝ → ℂ}
    (ha : -1 < a) (hM : 0 ≤ M) (hc : 0 < c) (hn : 0 < n)
    (hbound : ∀ t ∈ Set.Ioc (0 : ℝ) M,
      ‖f t‖ ≤ t ^ a * exp (-(c * (n : ℝ) * t))) :
    ‖∫ t in (0 : ℝ)..M, f t‖ ≤
      (1 / (c * n)) ^ (a + 1) * Gamma (a + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hrate : 0 < c * (n : ℝ) := mul_pos hc hn'
  have ha' : 0 < a + 1 := by linarith
  have hkey := Real.integral_rpow_mul_exp_neg_mul_Ioi ha' hrate
  have hint : IntegrableOn (fun t : ℝ => t ^ ((a + 1) - 1) * exp (-((c * n) * t)))
      (Ioi 0) := .of_integral_ne_zero (by
        rw [hkey]
        exact (mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hrate) _)
          (Real.Gamma_pos_of_pos ha')).ne')
  have hmajor : IntervalIntegrable
      (fun t : ℝ => t ^ a * exp (-(c * (n : ℝ) * t))) MeasureTheory.volume 0 M := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hM]
    simpa only [add_sub_cancel_right] using hint.mono_set Ioc_subset_Ioi_self
  exact (intervalIntegral.norm_integral_le_of_norm_le hM
    (Filter.Eventually.of_forall (fun t ht => hbound t ht)) hmajor).trans
      (laplace_ray_bound ha hM hc hn)

/-- On a circle of radius `1/n` around the singularity, a `|1-z|^a`
majorant gives an `n^(-a-1)` contour contribution. -/
theorem norm_inner_circle_le {a C : ℝ} {n : ℕ} {f : ℂ → ℂ}
    (hn : 0 < n)
    (hf : ∀ z ∈ Metric.sphere (1 : ℂ) (1 / (n : ℝ)),
      ‖f z‖ ≤ C * (1 / (n : ℝ)) ^ a) :
    ‖∮ z in C((1 : ℂ), 1 / (n : ℝ)), f z‖ ≤
      (2 * π * C) * (1 / (n : ℝ)) ^ (a + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < (1 / (n : ℝ)) := one_div_pos.mpr hn'
  have hb := circleIntegral.norm_integral_le_of_norm_le_const hr.le hf
  calc
    ‖∮ z in C((1 : ℂ), 1 / (n : ℝ)), f z‖ ≤
      2 * π * (1 / (n : ℝ)) * (C * (1 / (n : ℝ)) ^ a) := hb
    _ = (2 * π * C) * (1 / (n : ℝ)) ^ (a + 1) := by
      rw [Real.rpow_add hr]
      simp only [Real.rpow_one]
      ring






end PerronWright.Transfer
