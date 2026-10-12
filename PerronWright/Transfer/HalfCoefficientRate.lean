import PerronWright.Transfer.NegativeHalfPolynomial
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Quantitative half-power coefficient estimate

Log-convexity of the Gamma function gives a sharp elementary bracket for
`Gamma(n + 1/2) / Gamma(n)`. It yields an explicit `1/n` bound on the
relative error of the coefficients of `(1-z)^(-1/2)`.
-/

open Filter Asymptotics
open scoped Topology
noncomputable section

namespace PerronWright.Transfer

private theorem logGamma_recurrence {y : ℝ} (hy : 0 < y) :
    (Real.log ∘ Real.Gamma) (y + 1) =
      (Real.log ∘ Real.Gamma) y + Real.log y := by
  simp only [Function.comp_apply, Real.Gamma_add_one hy.ne']
  rw [Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne']
  ring

theorem half_gamma_log_bounds (n : ℕ) (hn : 2 ≤ n) :
    Real.log (Real.Gamma (n : ℝ)) +
        (1 / 2 : ℝ) * Real.log ((n : ℝ) - 1) ≤
      Real.log (Real.Gamma ((n : ℝ) + 1 / 2)) ∧
      Real.log (Real.Gamma ((n : ℝ) + 1 / 2)) ≤
        Real.log (Real.Gamma (n : ℝ)) +
          (1 / 2 : ℝ) * Real.log (n : ℝ) := by
  have hl := Real.BohrMollerup.f_add_nat_ge Real.convexOn_log_Gamma
    (fun {y} hy => logGamma_recurrence hy) hn
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hu := Real.BohrMollerup.f_add_nat_le Real.convexOn_log_Gamma
    (fun {y} hy => logGamma_recurrence hy)
    (by omega : n ≠ 0) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1)
  exact ⟨hl, hu⟩

theorem half_gamma_bounds (n : ℕ) (hn : 2 ≤ n) :
    Real.Gamma (n : ℝ) * Real.sqrt ((n : ℝ) - 1) ≤
      Real.Gamma ((n : ℝ) + 1 / 2) ∧
      Real.Gamma ((n : ℝ) + 1 / 2) ≤
        Real.Gamma (n : ℝ) * Real.sqrt (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnm1pos : 0 < (n : ℝ) - 1 := by
    have h : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hgamma : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnpos
  have hgamma' : 0 < Real.Gamma ((n : ℝ) + 1 / 2) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hlog_sqrt (x : ℝ) (hx : 0 < x) :
      (1 / 2 : ℝ) * Real.log x = Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]
    ring
  constructor
  · have h := (half_gamma_log_bounds n hn).1
    rw [hlog_sqrt _ hnm1pos,
      ← Real.log_mul hgamma.ne' (Real.sqrt_pos.2 hnm1pos).ne'] at h
    exact (Real.log_le_log_iff
      (mul_pos hgamma (Real.sqrt_pos.2 hnm1pos)) hgamma').mp h
  · have h := (half_gamma_log_bounds n hn).2
    rw [hlog_sqrt _ hnpos,
      ← Real.log_mul hgamma.ne' (Real.sqrt_pos.2 hnpos).ne'] at h
    exact (Real.log_le_log_iff hgamma'
      (mul_pos hgamma (Real.sqrt_pos.2 hnpos))).mp h

theorem coefficient_half_gamma_form (n : ℕ) (hn : 0 < n) :
    coefficient (1 / 2) n =
      Real.Gamma ((n : ℝ) + 1 / 2) /
        (Real.sqrt Real.pi * ((n : ℝ) * Real.Gamma (n : ℝ))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [coefficient_eq_gamma (1 / 2) (by norm_num), Real.Gamma_one_half_eq]
  have ha : (1 / 2 : ℝ) + n = (n : ℝ) + 1 / 2 := by ring
  rw [ha]
  rw [Real.Gamma_add_one hnpos.ne']

theorem coefficient_half_bounds (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt ((n : ℝ) - 1) / (Real.sqrt Real.pi * n) ≤
      coefficient (1 / 2) n ∧
      coefficient (1 / 2) n ≤
        Real.sqrt (n : ℝ) / (Real.sqrt Real.pi * n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hgamma : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnpos
  have hden : 0 < Real.sqrt Real.pi * ((n : ℝ) * Real.Gamma (n : ℝ)) := by
    positivity
  have hc := coefficient_half_gamma_form n (by omega : 0 < n)
  constructor
  · calc
      _ = (Real.Gamma (n : ℝ) * Real.sqrt ((n : ℝ) - 1)) /
          (Real.sqrt Real.pi * ((n : ℝ) * Real.Gamma (n : ℝ))) := by
            field_simp [hgamma.ne', hnpos.ne']
      _ ≤ _ := div_le_div_of_nonneg_right (half_gamma_bounds n hn).1 hden.le
      _ = _ := hc.symm
  · calc
      _ = Real.Gamma ((n : ℝ) + 1 / 2) /
          (Real.sqrt Real.pi * ((n : ℝ) * Real.Gamma (n : ℝ))) := hc
      _ ≤ (Real.Gamma (n : ℝ) * Real.sqrt (n : ℝ)) /
          (Real.sqrt Real.pi * ((n : ℝ) * Real.Gamma (n : ℝ))) :=
            div_le_div_of_nonneg_right (half_gamma_bounds n hn).2 hden.le
      _ = _ := by field_simp [hgamma.ne', hnpos.ne']

theorem sqrt_lag_ratio_ge_one_sub_inv (n : ℕ) (hn : 2 ≤ n) :
    1 - (n : ℝ)⁻¹ ≤
      Real.sqrt ((n : ℝ) - 1) / Real.sqrt (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnm1 : 0 ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    linarith
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsqrtle : Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by linarith)
  have hmul : (n : ℝ) - 1 ≤
      Real.sqrt ((n : ℝ) - 1) * Real.sqrt (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsqrtle
      (Real.sqrt_nonneg ((n : ℝ) - 1))
    nlinarith [Real.sq_sqrt hnm1]
  have hdiv : ((n : ℝ) - 1) / Real.sqrt (n : ℝ) ≤
      Real.sqrt ((n : ℝ) - 1) := (div_le_iff₀ hsqrtpos).2 hmul
  calc
    1 - (n : ℝ)⁻¹ = ((n : ℝ) - 1) / n := by
      field_simp [hnpos.ne']
    _ = (((n : ℝ) - 1) / Real.sqrt (n : ℝ)) /
        Real.sqrt (n : ℝ) := by
          field_simp [hnpos.ne', hsqrtpos.ne']
          nlinarith [Real.sq_sqrt hnpos.le]
    _ ≤ _ := div_le_div_of_nonneg_right hdiv hsqrtpos.le

theorem coefficient_half_normalized_bounds (n : ℕ) (hn : 2 ≤ n) :
    1 - (n : ℝ)⁻¹ ≤
      coefficient (1 / 2) n * Real.sqrt Real.pi * Real.sqrt (n : ℝ) ∧
      coefficient (1 / 2) n * Real.sqrt Real.pi * Real.sqrt (n : ℝ) ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hgamma : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hnpos
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hden : 0 ≤ Real.Gamma (n : ℝ) * Real.sqrt (n : ℝ) := by positivity
  have heq : coefficient (1 / 2) n * Real.sqrt Real.pi * Real.sqrt (n : ℝ) =
      Real.Gamma ((n : ℝ) + 1 / 2) /
        (Real.Gamma (n : ℝ) * Real.sqrt (n : ℝ)) := by
    rw [coefficient_half_gamma_form n (by omega : 0 < n)]
    field_simp [hpi.ne', hgamma.ne', hnpos.ne', hsqrtpos.ne']
    nlinarith [Real.sq_sqrt hnpos.le]
  rw [heq]
  constructor
  · calc
      _ ≤ Real.sqrt ((n : ℝ) - 1) / Real.sqrt (n : ℝ) :=
        sqrt_lag_ratio_ge_one_sub_inv n hn
      _ = (Real.Gamma (n : ℝ) * Real.sqrt ((n : ℝ) - 1)) /
          (Real.Gamma (n : ℝ) * Real.sqrt (n : ℝ)) := by
            field_simp [hgamma.ne', hsqrtpos.ne']
      _ ≤ _ := div_le_div_of_nonneg_right (half_gamma_bounds n hn).1 hden
  · calc
      _ ≤ (Real.Gamma (n : ℝ) * Real.sqrt (n : ℝ)) /
          (Real.Gamma (n : ℝ) * Real.sqrt (n : ℝ)) :=
        div_le_div_of_nonneg_right (half_gamma_bounds n hn).2 hden
      _ = _ := div_self (mul_ne_zero hgamma.ne' hsqrtpos.ne')

theorem coefficient_half_relative_error_bound (n : ℕ) (hn : 2 ≤ n) :
    |coefficient (1 / 2) n * Real.sqrt Real.pi * Real.sqrt (n : ℝ) - 1| ≤
      (n : ℝ)⁻¹ := by
  obtain ⟨hl, hu⟩ := coefficient_half_normalized_bounds n hn
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith

theorem coefficient_half_relative_error_isBigO :
    (fun n : ℕ =>
      coefficient (1 / 2) n * Real.sqrt Real.pi * Real.sqrt (n : ℝ) - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply isBigO_iff.mpr
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  simpa only [Real.norm_eq_abs, one_mul,
    abs_of_nonneg (show 0 ≤ ((n : ℝ)⁻¹) by positivity)] using
      coefficient_half_relative_error_bound n hn

end PerronWright.Transfer
