import PerronWright.Probability.BrownianKilledBoundaryPolynomial
import PerronWright.Probability.PolynomialCoefficientSeriesDerivation
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # The normalized actual boundary polynomial series

The coefficient differential equation is obtained from the already
identified Brownian boundary polynomials. The power-series equation
is its literal coefficientwise normalization; it is not an additional
analytic interface.
-/

open Polynomial
open scoped Polynomial PowerSeries
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBoundaryNormalizedSeries

open BrownianKilledBoundaryPolynomial PolynomialCoefficientSeriesDerivation

def normalization (n : ℕ) : ℝ := (2*(n.factorial : ℝ))⁻¹

theorem normalization_succ (n : ℕ) :
    normalization (n+1)*((n+1 : ℕ) : ℝ) = normalization n := by
  unfold normalization
  rw [Nat.factorial_succ,Nat.cast_mul]
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

def normalizedBoundaryPolynomial (n : ℕ) : ℝ[X] :=
  C (normalization n)*boundaryPolynomial n 1

theorem normalizedBoundaryPolynomial_zero : normalizedBoundaryPolynomial 0 = 1 := by
  norm_num [normalizedBoundaryPolynomial,normalization,boundaryPolynomial,← C_mul]

theorem normalizedBoundaryPolynomial_succ_zero (n : ℕ) :
    (normalizedBoundaryPolynomial (n+1)).eval 0 = 0 := by
  simp only [normalizedBoundaryPolynomial,eval_mul,eval_C,boundaryPolynomial_succ_zero,mul_zero]

theorem normalizedBoundaryPolynomial_equation (n : ℕ) :
    (normalizedBoundaryPolynomial (n+1)).derivative.derivative-
      C (2 : ℝ)*(normalizedBoundaryPolynomial (n+1)).derivative =
        -C (2 : ℝ)*X*normalizedBoundaryPolynomial n := by
  have h := boundaryPolynomial_differential_equation n 1 (by norm_num)
  have hODE : (boundaryPolynomial (n+1) 1).derivative.derivative-
      C (2 : ℝ)*(boundaryPolynomial (n+1) 1).derivative =
        -C (2 : ℝ)*C ((n+1 : ℕ) : ℝ)*X*boundaryPolynomial n 1 := by
    simp only [C_1,one_mul] at h
    have hc : C (2 : ℝ)*C (1/2 : ℝ) = (1 : ℝ[X]) := by
      rw [← C_mul]
      norm_num
    calc
      _ = C (2 : ℝ)*(C (1/2 : ℝ)*(boundaryPolynomial (n+1) 1).derivative.derivative)-
          C (2 : ℝ)*(boundaryPolynomial (n+1) 1).derivative := by
            rw [← mul_assoc,hc,one_mul]
      _ = -C (2 : ℝ)*((boundaryPolynomial (n+1) 1).derivative-
          C (1/2 : ℝ)*(boundaryPolynomial (n+1) 1).derivative.derivative) := by ring
      _ = _ := by rw [h]; ring
  simp only [normalizedBoundaryPolynomial,derivative_C_mul]
  calc
    _ = C (normalization (n+1))*
        ((boundaryPolynomial (n+1) 1).derivative.derivative-
          C (2 : ℝ)*(boundaryPolynomial (n+1) 1).derivative) := by ring
    _ = C (normalization (n+1))*
        (-C (2 : ℝ)*C ((n+1 : ℕ) : ℝ)*X*boundaryPolynomial n 1) := by rw [hODE]
    _ = -C (2 : ℝ)*(C (normalization (n+1))*C ((n+1 : ℕ) : ℝ))*
        X*boundaryPolynomial n 1 := by ring
    _ = _ := by rw [← C_mul,normalization_succ]; ring

def boundarySeries : PowerSeries ℝ[X] := PowerSeries.mk normalizedBoundaryPolynomial

theorem coeff_boundarySeries (n : ℕ) :
    PowerSeries.coeff n boundarySeries = normalizedBoundaryPolynomial n := by
  simp only [boundarySeries,PowerSeries.coeff_mk]

theorem constantCoeff_boundarySeries : PowerSeries.constantCoeff boundarySeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,coeff_boundarySeries,
    normalizedBoundaryPolynomial_zero]

theorem boundarySeries_equation :
    spatialDerivative (spatialDerivative boundarySeries)-
      PowerSeries.C (C (2 : ℝ))*spatialDerivative boundarySeries =
        -PowerSeries.C (C (2 : ℝ))*PowerSeries.X*PowerSeries.C X*boundarySeries := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    rw [map_sub,coeff_spatialDerivative,coeff_spatialDerivative,coeff_boundarySeries,
      normalizedBoundaryPolynomial_zero]
    simp only [derivative_one]
    rw [PowerSeries.coeff_C_mul,coeff_spatialDerivative,coeff_boundarySeries,
      normalizedBoundaryPolynomial_zero]
    simp
  | succ n =>
    simp only [map_sub,coeff_spatialDerivative,PowerSeries.coeff_C_mul,coeff_boundarySeries]
    have hshift : -PowerSeries.C (C (2 : ℝ))*PowerSeries.X*PowerSeries.C X*boundarySeries =
        PowerSeries.X*(PowerSeries.C (-C (2 : ℝ)*X)*boundarySeries) := by
      simp only [map_mul,map_neg]
      ring
    rw [hshift,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_C_mul,coeff_boundarySeries]
    exact normalizedBoundaryPolynomial_equation n

def boundarySeriesInverse : PowerSeries ℝ[X] := PowerSeries.invOfUnit boundarySeries 1

theorem boundarySeries_mul_inverse : boundarySeries*boundarySeriesInverse = 1 := by
  exact PowerSeries.mul_invOfUnit _ _ (by simpa using constantCoeff_boundarySeries)

theorem boundarySeries_inverse_mul : boundarySeriesInverse*boundarySeries = 1 := by
  rw [mul_comm]
  exact boundarySeries_mul_inverse

theorem constantCoeff_boundarySeriesInverse :
    PowerSeries.constantCoeff boundarySeriesInverse = 1 := by
  simp only [boundarySeriesInverse,PowerSeries.constantCoeff_invOfUnit,inv_one,Units.val_one]

end PerronWright.BrownianBoundaryNormalizedSeries
