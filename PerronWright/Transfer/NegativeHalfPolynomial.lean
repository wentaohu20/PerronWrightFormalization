import PerronWright.Transfer.NegativeHalf
import PerronWright.Transfer.Polynomial

/-!
# Polynomial prefactors for positive half-integer powers

The fixed-shift coefficient limit and finite-convolution argument of
`Polynomial` require only a nonzero normalized coefficient limit, not a
positive exponent. This module proves that general form and applies it
to `(1-z)^(1/2)` and `(1-z)^(3/2)`.
-/

open Filter Asymptotics
open scoped Topology
noncomputable section

namespace PerronWright.Transfer

theorem shifted_coefficient_tendsto_of_normalized_limit
    (s c : ℝ)
    (hc : Tendsto (fun n : ℕ => coefficient s n / (n : ℝ) ^ (s - 1))
      atTop (𝓝 c)) (j : ℕ) :
    Tendsto (fun n : ℕ => coefficient s (n - j) / (n : ℝ) ^ (s - 1))
      atTop (𝓝 c) := by
  have hc' := hc.comp (tendsto_sub_atTop_nat j)
  have hr := (nat_sub_div_tendsto_one j).rpow_const (p := s - 1) (Or.inl one_ne_zero)
  have h := hc'.mul hr
  simp only [Real.one_rpow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop j] with n hn
  have hmpos : (0 : ℝ) < (n - j : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hn
  have hm : ((n - j : ℕ) : ℝ) ^ (s - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hmpos _).ne'
  change coefficient s (n - j) / ((n - j : ℕ) : ℝ) ^ (s - 1) *
      (((n - j : ℕ) : ℝ) / n) ^ (s - 1) = _
  rw [Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  field_simp

theorem prefactorCoefficient_tendsto_of_normalized_limit
    (P : Polynomial ℝ) (s c : ℝ)
    (hc : Tendsto (fun n : ℕ => coefficient s n / (n : ℝ) ^ (s - 1))
      atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => prefactorCoefficient P s n / (n : ℝ) ^ (s - 1))
      atTop (𝓝 (P.eval 1 * c)) := by
  have h := tendsto_finsetSum P.support
    (fun j _ => (shifted_coefficient_tendsto_of_normalized_limit s c hc j).const_mul
      (P.coeff j))
  have heval : (∑ j ∈ P.support, P.coeff j * c) = P.eval 1 * c := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
    simp only [one_pow, mul_one]
  rw [heval] at h
  apply h.congr'
  filter_upwards [prefactorCoefficient_eventually_eq P s] with n hn
  rw [hn, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem prefactorCoefficient_isEquivalent_of_normalized_limit
    (P : Polynomial ℝ) (s c : ℝ) (hP : P.eval 1 ≠ 0) (hc0 : c ≠ 0)
    (hc : Tendsto (fun n : ℕ => coefficient s n / (n : ℝ) ^ (s - 1))
      atTop (𝓝 c)) :
    prefactorCoefficient P s ~[atTop]
      (fun n : ℕ => P.eval 1 * c * (n : ℝ) ^ (s - 1)) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have h := (prefactorCoefficient_tendsto_of_normalized_limit P s c hc).div_const
    (P.eval 1 * c)
  have hq : P.eval 1 * c ≠ 0 := mul_ne_zero hP hc0
  rw [div_self hq] at h
  convert h using 1
  ext n
  simp only [Pi.div_apply, div_eq_mul_inv, mul_inv_rev]
  ring

theorem prefactorCoefficient_neg_half_isEquivalent
    (P : Polynomial ℝ) (hP : P.eval 1 ≠ 0) :
    prefactorCoefficient P (-(1 / 2)) ~[atTop]
      (fun n : ℕ => -(P.eval 1) * (n : ℝ) ^ (-(3 / 2) : ℝ) /
        (2 * Real.sqrt Real.pi)) := by
  have hc : Tendsto (fun n : ℕ =>
      coefficient (-(1 / 2)) n / (n : ℝ) ^ ((-(1 / 2 : ℝ)) - 1))
      atTop (𝓝 (-(1 / (2 * Real.Gamma (1 / 2))))) := by
    simpa only [show (-(1 / 2 : ℝ)) - 1 = -(3 / 2 : ℝ) by norm_num] using
      coefficient_neg_half_normalized_tendsto
  have hg : Real.Gamma (1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  have h := prefactorCoefficient_isEquivalent_of_normalized_limit P
    (-(1 / 2)) (-(1 / (2 * Real.Gamma (1 / 2)))) hP
    (by exact neg_ne_zero.mpr (one_div_ne_zero (mul_ne_zero (by norm_num) hg))) hc
  convert h using 1
  ext n
  rw [Real.Gamma_one_half_eq]
  norm_num
  ring

theorem prefactorCoefficient_neg_three_halves_isEquivalent
    (P : Polynomial ℝ) (hP : P.eval 1 ≠ 0) :
    prefactorCoefficient P (-(3 / 2)) ~[atTop]
      (fun n : ℕ => 3 * P.eval 1 * (n : ℝ) ^ (-(5 / 2) : ℝ) /
        (4 * Real.sqrt Real.pi)) := by
  have hc : Tendsto (fun n : ℕ =>
      coefficient (-(3 / 2)) n / (n : ℝ) ^ ((-(3 / 2 : ℝ)) - 1))
      atTop (𝓝 (3 / (4 * Real.Gamma (1 / 2)))) := by
    simpa only [show (-(3 / 2 : ℝ)) - 1 = -(5 / 2 : ℝ) by norm_num] using
      coefficient_neg_three_halves_normalized_tendsto
  have hg : Real.Gamma (1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  have h := prefactorCoefficient_isEquivalent_of_normalized_limit P
    (-(3 / 2)) (3 / (4 * Real.Gamma (1 / 2))) hP
    (by exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hg)) hc
  convert h using 1
  ext n
  rw [Real.Gamma_one_half_eq]
  norm_num
  ring

end PerronWright.Transfer
