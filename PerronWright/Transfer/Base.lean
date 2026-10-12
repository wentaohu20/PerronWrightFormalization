import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exact coefficients and leading asymptotics for pure power singularities

For each real exponent `s`, the complex analytic expansion of `(1-z)^(-s)`
is identified on the unit disc. For `s > 0`, its exact coefficients are
expressed by a Gamma ratio and their leading asymptotic is proved from
Euler's convergent Gamma sequence.

This module does not assert a transfer theorem for general dented-domain
remainders, parameter-uniform errors, or a quantitative relative error rate.
-/

open Filter Asymptotics
open scoped Topology
noncomputable section

namespace PerronWright.Transfer

/-- The exact coefficient of the elementary singularity `(1-z)^(-s)`. -/
def coefficient (s : ℝ) (n : ℕ) : ℝ :=
  (∏ j ∈ Finset.range n, (s + j)) / (n.factorial : ℝ)

theorem ascPochhammer_eval_eq_prod (s : ℝ) (n : ℕ) :
    (ascPochhammer ℝ n).eval s = ∏ j ∈ Finset.range n, (s + j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, Finset.prod_range_succ, ih]

theorem coefficient_eq_choose (s : ℝ) (n : ℕ) :
    coefficient s n = Ring.choose (s + n - 1) n := by
  rw [← Ring.multichoose_eq]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer s n
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval,
    ascPochhammer_eval_eq_prod] at h
  unfold coefficient
  apply (div_eq_iff (by exact_mod_cast Nat.factorial_ne_zero n)).mpr
  simpa only [mul_comm] using h.symm

theorem gamma_add_nat_eq_prod (s : ℝ) (hs : 0 < s) (n : ℕ) :
    Real.Gamma (s + n) = Real.Gamma s * ∏ j ∈ Finset.range n, (s + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 0 < s + (n : ℝ) := add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg n)
      rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos.ne', ih, Finset.prod_range_succ]
      ring

theorem coefficient_eq_gamma (s : ℝ) (hs : 0 < s) (n : ℕ) :
    coefficient s n =
      Real.Gamma (s + n) / (Real.Gamma s * Real.Gamma (n + 1)) := by
  rw [gamma_add_nat_eq_prod s hs, Real.Gamma_nat_eq_factorial]
  unfold coefficient
  exact (mul_div_mul_left _ _ (Real.Gamma_pos_of_pos hs).ne').symm

def powerSeries (s : ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (fun n => (coefficient s n : ℂ))

theorem powerSeries_hasFPowerSeriesOnBall (s : ℝ) :
    HasFPowerSeriesOnBall (fun z : ℂ => 1 / (1 - z) ^ (s : ℂ))
      (powerSeries s) 0 1 := by
  have hc (n : ℕ) : (coefficient s n : ℂ) =
      Ring.choose ((s : ℂ) + n - 1) n := by
    rw [coefficient_eq_choose, Complex.ofReal_choose]
    push_cast
    rfl
  simpa only [powerSeries, hc] using Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (s : ℂ)

theorem powerSeries_coeff (s : ℝ) (n : ℕ) :
    (powerSeries s).coeff n = (coefficient s n : ℂ) := by
  exact FormalMultilinearSeries.coeff_ofScalars

theorem powerSeries_coeff_gamma (s : ℝ) (hs : 0 < s) (n : ℕ) :
    (powerSeries s).coeff n =
      (Real.Gamma (s + n) / (Real.Gamma s * Real.Gamma (n + 1)) : ℝ) := by
  rw [powerSeries_coeff, coefficient_eq_gamma s hs]

theorem coefficient_normalized_eq_GammaSeq (s : ℝ) (hs : 0 < s)
    (n : ℕ) (hn : n ≠ 0) :
    coefficient s n / (n : ℝ) ^ (s - 1) =
      ((n : ℝ) / (n + s)) / Real.GammaSeq s n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hprod : (∏ j ∈ Finset.range n, (s + (j : ℝ))) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro j _
    exact add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg j)
  have hfact : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hrpow : (n : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos hnpos s).ne'
  have hns : (n : ℝ) + s ≠ 0 := (add_pos hnpos hs).ne'
  unfold coefficient Real.GammaSeq
  rw [Finset.prod_range_succ, Real.rpow_sub hnpos, Real.rpow_one]
  field_simp
  ring

theorem coefficient_tendsto (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => coefficient s n / (n : ℝ) ^ (s - 1))
      atTop (𝓝 (1 / Real.Gamma s)) := by
  have h := (tendsto_natCast_div_add_atTop s).div (Real.GammaSeq_tendsto_Gamma s)
    (Real.Gamma_pos_of_pos hs).ne'
  apply h.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (coefficient_normalized_eq_GammaSeq s hs n hn).symm

theorem coefficient_isEquivalent (s : ℝ) (hs : 0 < s) :
    coefficient s ~[atTop] (fun n : ℕ => (n : ℝ) ^ (s - 1) / Real.Gamma s) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hg : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos hs).ne'
  have h := (coefficient_tendsto s hs).mul_const (Real.Gamma s)
  have hlimit : Tendsto (fun n : ℕ =>
      (coefficient s n / (n : ℝ) ^ (s - 1)) * Real.Gamma s) atTop (𝓝 1) := by
    simpa only [div_mul_cancel₀ (1 : ℝ) hg] using h
  convert hlimit using 1
  ext n
  simp only [Pi.div_apply, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem powerSeries_neg_cpow (s : ℝ) :
    HasFPowerSeriesOnBall (fun z : ℂ => (1 - z) ^ (-(s : ℂ)))
      (powerSeries s) 0 1 := by
  simpa only [Complex.cpow_neg, one_div] using powerSeries_hasFPowerSeriesOnBall s

theorem coefficient_half_isEquivalent :
    coefficient (1 / 2) ~[atTop]
      (fun n : ℕ => 1 / Real.sqrt (Real.pi * n)) := by
  have h := coefficient_isEquivalent (1 / 2) (by norm_num)
  convert h using 1
  ext n
  rw [Real.Gamma_one_half_eq, show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num,
    Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow,
    Real.sqrt_mul Real.pi_pos.le]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]


end PerronWright.Transfer


