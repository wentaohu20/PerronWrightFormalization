import PerronWright.Transfer.ShiftGeneral
import PerronWright.Transfer.Polynomial

/-!
# Quantitative finite polynomial prefactor shift

For an exponent without zeros in its generalized binomial coefficients,
the finite-convolution coefficient divided by its pure-power coefficient
differs from the polynomial's value at 1 by `O(1/n)`. The positive
half-integer cases are explicit corollaries.
-/

open Filter Asymptotics
open scoped Topology
noncomputable section

namespace PerronWright.Transfer

theorem prefactorCoefficient_relative_shift_error_isBigO
    (P : Polynomial ℝ) (s : ℝ) (hs : ∀ j : ℕ, s + j ≠ 0) :
    (fun n : ℕ => prefactorCoefficient P s n / coefficient s n - P.eval 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  have hsum :
      (fun n : ℕ => ∑ j ∈ P.support,
        P.coeff j * (coefficient s (n - j) / coefficient s n - 1))
        =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
    have h : (∑ j ∈ P.support,
        fun n : ℕ => P.coeff j * (coefficient s (n - j) / coefficient s n - 1))
        =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
      apply IsBigO.sum
      intro j hj
      exact (shifted_coefficient_error_isBigO_of_no_nat_root s hs j).const_mul_left
        (P.coeff j)
    simpa only [Finset.sum_fn] using h
  apply hsum.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [prefactorCoefficient_eventually_eq P s] with n hn
  rw [hn, Finset.sum_div]
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  simp only [one_pow, mul_one]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem prefactorCoefficient_neg_half_relative_shift_error_isBigO
    (P : Polynomial ℝ) :
    (fun n : ℕ => prefactorCoefficient P (-(1 / 2)) n /
      coefficient (-(1 / 2)) n - P.eval 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) :=
  prefactorCoefficient_relative_shift_error_isBigO P (-(1 / 2))
    coefficient_neg_half_no_nat_root

theorem prefactorCoefficient_neg_three_halves_relative_shift_error_isBigO
    (P : Polynomial ℝ) :
    (fun n : ℕ => prefactorCoefficient P (-(3 / 2)) n /
      coefficient (-(3 / 2)) n - P.eval 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) :=
  prefactorCoefficient_relative_shift_error_isBigO P (-(3 / 2))
    coefficient_neg_three_halves_no_nat_root

end PerronWright.Transfer
