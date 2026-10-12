import PerronWright.Probability.PolynomialCoefficientSeriesDerivation
import PerronWright.Probability.PolynomialLinearODEUniqueness

/-! # Polynomial coefficient uniqueness for a formal first-order equation

The proof uses finite convolution and polynomial degree reduction,
not analytic uniqueness or an imposed boundary-response identity.
-/

open Polynomial
open scoped Polynomial PowerSeries
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.PolynomialSeriesFirstOrderUniqueness

open PolynomialCoefficientSeriesDerivation PolynomialLinearODEUniqueness

theorem coeff_mul_of_lower_zero (B H : PowerSeries ℝ[X]) (n : ℕ)
    (hH : ∀ k < n, PowerSeries.coeff k H = 0) :
    PowerSeries.coeff n (B*H) = PowerSeries.coeff 0 B*PowerSeries.coeff n H := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_single (0,n)
  · intro a ha hne
    have hsum := Finset.mem_antidiagonal.mp ha
    have hlt : a.2 < n := by
      by_contra hlt
      have heq : a = (0,n) := by
        apply Prod.ext <;> dsimp <;> omega
      exact hne heq
    rw [hH a.2 hlt,mul_zero]
  · intro hn
    exact (hn (Finset.mem_antidiagonal.mpr (by simp))).elim

theorem homogeneous_first_order_zero (B H : PowerSeries ℝ[X])
    (hB : PowerSeries.coeff 0 B = -1)
    (h : spatialDerivative H+PowerSeries.C (C (2 : ℝ))*B*H = 0) : H = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc := congrArg (PowerSeries.coeff n) h
    rw [map_add,coeff_spatialDerivative] at hc
    have hprod : PowerSeries.C (C (2 : ℝ))*B*H =
        PowerSeries.C (C (2 : ℝ))*(B*H) := by ring
    rw [hprod,PowerSeries.coeff_C_mul,coeff_mul_of_lower_zero B H n ih,hB,map_zero] at hc
    apply derivative_eigenvalue_zero _ 2 (by norm_num)
    linear_combination hc

end PerronWright.PolynomialSeriesFirstOrderUniqueness
