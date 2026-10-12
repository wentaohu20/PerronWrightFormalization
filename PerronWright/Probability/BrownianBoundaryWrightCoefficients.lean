import PerronWright.Probability.BrownianBoundaryRiccatiTransport
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! # Wright recurrence for the actual Brownian boundary coefficients

These coefficients are evaluations of the literal logarithmic boundary
series. The recurrence is obtained from the proved Riccati and transport
identities, including the exceptional initial coefficient.
-/

open Polynomial
open scoped Polynomial PowerSeries
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBoundaryWrightCoefficients

open BrownianBoundarySeriesRiccati BrownianBoundaryRiccatiTransport
open PolynomialCoefficientSeriesDerivation

def logPolynomial (n : ℕ) : ℝ[X] := PowerSeries.coeff n logarithmicBoundarySeries

def logCoefficient (n : ℕ) : ℝ := (logPolynomial n).eval 0

theorem logPolynomial_zero : logPolynomial 0 = -1 := coeff_zero_logarithmicBoundarySeries

theorem logCoefficient_zero : logCoefficient 0 = -1 := by
  simp [logCoefficient,logPolynomial_zero]

theorem logPolynomial_succ_derivative (n : ℕ) :
    (logPolynomial (n+1)).derivative =
      C (3*(n : ℝ)-1)*logPolynomial n-X*(logPolynomial n).derivative := by
  have h := congrArg (PowerSeries.coeff (n+1)) logarithmicBoundarySeries_transport
  have h3 : (3 : PowerSeries ℝ[X]) = PowerSeries.C (C (3 : ℝ)) := by simp only [map_ofNat]
  rw [coeff_spatialDerivative,PowerSeries.coeff_succ_X_mul] at h
  simp only [h3,map_sub,PowerSeries.coeff_C_mul,coeff_parameterEuler,coeff_spatialDerivative] at h
  change (logPolynomial (n+1)).derivative =
    C (3 : ℝ)*((n : ℝ[X])*logPolynomial n)-logPolynomial n-
      X*(logPolynomial n).derivative at h
  calc
    _ = _ := h
    _ = _ := by
      rw [map_sub,map_mul,C_1,map_natCast]
      ring

theorem logCoefficient_succ_derivative (n : ℕ) :
    (logPolynomial (n+1)).derivative.eval 0 = (3*(n : ℝ)-1)*logCoefficient n := by
  rw [logPolynomial_succ_derivative]
  simp [logCoefficient]

theorem logCoefficient_riccati (n : ℕ) :
    (3*(n : ℝ)-1)*logCoefficient n+
      ∑ a ∈ Finset.antidiagonal (n+1), logCoefficient a.1*logCoefficient a.2 = 0 := by
  have h := congrArg (fun f : PowerSeries ℝ[X] ↦ (PowerSeries.coeff (n+1) f).eval 0)
    logarithmicBoundarySeries_riccati
  have hshift : (2 : PowerSeries ℝ[X])*PowerSeries.X*PowerSeries.C X =
      PowerSeries.X*PowerSeries.C (C (2 : ℝ)*X) := by
    simp only [map_mul,map_ofNat]
    ring
  rw [pow_two,map_add,coeff_spatialDerivative,PowerSeries.coeff_mul,eval_add] at h
  rw [hshift,map_sub,eval_sub,PowerSeries.coeff_succ_X_mul] at h
  simp only [PowerSeries.coeff_one,Nat.add_one_ne_zero,if_false,eval_zero,
    PowerSeries.coeff_C] at h
  have heval : (if n = 0 then C (2 : ℝ)*X else 0).eval 0 = 0 := by
    split_ifs <;> simp
  rw [heval,sub_self] at h
  rw [show ∑ a ∈ Finset.antidiagonal (n+1),
      PowerSeries.coeff a.1 logarithmicBoundarySeries*PowerSeries.coeff a.2 logarithmicBoundarySeries =
      ∑ a ∈ Finset.antidiagonal (n+1), logPolynomial a.1*logPolynomial a.2 from rfl,
    ← Polynomial.coe_evalRingHom,map_sum] at h
  simp only [Polynomial.coe_evalRingHom,eval_mul] at h
  change (logPolynomial (n+1)).derivative.eval 0+
    ∑ a ∈ Finset.antidiagonal (n+1), logCoefficient a.1*logCoefficient a.2 = 0 at h
  rwa [logCoefficient_succ_derivative] at h

theorem logCoefficient_one : logCoefficient 1 = 1/2 := by
  have h := logCoefficient_riccati 0
  norm_num [Finset.antidiagonal,logCoefficient_zero] at h
  linarith

theorem logCoefficient_recurrence (n : ℕ) :
    2*logCoefficient (n+2) =
      (3*(n : ℝ)+2)*logCoefficient (n+1)+
        ∑ a ∈ Finset.antidiagonal n, logCoefficient (a.1+1)*logCoefficient (a.2+1) := by
  have h := logCoefficient_riccati (n+1)
  rw [Finset.Nat.sum_antidiagonal_succ,Finset.Nat.sum_antidiagonal_succ'] at h
  simp only [logCoefficient_zero] at h
  push_cast at h
  norm_num only [show n+1+1 = n+2 by omega] at h
  linear_combination -h

theorem logCoefficient_two : logCoefficient 2 = 5/8 := by
  have h := logCoefficient_recurrence 0
  norm_num [Finset.antidiagonal,logCoefficient_one] at h
  linarith

end PerronWright.BrownianBoundaryWrightCoefficients
