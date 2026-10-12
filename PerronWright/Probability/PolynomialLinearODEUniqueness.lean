import PerronWright.Probability.BrownianGreenPolynomialAction

/-! # Polynomial uniqueness for the linear boundary equations

A nonzero polynomial cannot be an eigenfunction of differentiation with
a nonzero eigenvalue. Degree reduction therefore proves uniqueness of
the polynomial Green response with zero boundary value.
-/

open Polynomial
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.PolynomialLinearODEUniqueness

theorem derivative_eigenvalue_zero (P : ℝ[X]) (c : ℝ) (hc : c ≠ 0)
    (h : P.derivative = C c*P) : P = 0 := by
  by_contra hP
  have hd := degree_derivative_lt hP
  rw [h,degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hc)] at hd
  exact (lt_irrefl _ hd)

theorem shifted_derivative_injective (P Q : ℝ[X]) (c : ℝ) (hc : c ≠ 0)
    (h : P.derivative-C c*P = Q.derivative-C c*Q) : P = Q := by
  apply sub_eq_zero.mp
  apply derivative_eigenvalue_zero (P-Q) c hc
  rw [derivative_sub]
  calc
    _ = (P.derivative-C c*P)-(Q.derivative-C c*Q)+C c*(P-Q) := by ring
    _ = _ := by rw [h]; ring

theorem green_boundary_equation_injective (P Q : ℝ[X]) (s : ℝ) (hs : s ≠ 0)
    (h : C s*P.derivative-C (1/2 : ℝ)*P.derivative.derivative =
      C s*Q.derivative-C (1/2 : ℝ)*Q.derivative.derivative)
    (h0 : P.eval 0 = Q.eval 0) : P = Q := by
  let R := P-Q
  have hR : C s*R.derivative-C (1/2 : ℝ)*R.derivative.derivative = 0 := by
    dsimp only [R]
    rw [derivative_sub,derivative_sub]
    calc
      _ = (C s*P.derivative-C (1/2 : ℝ)*P.derivative.derivative)-
          (C s*Q.derivative-C (1/2 : ℝ)*Q.derivative.derivative) := by ring
      _ = 0 := by rw [h]; ring
  have hd : R.derivative.derivative = C (2*s)*R.derivative := by
    have he : C (1/2 : ℝ)*R.derivative.derivative = C s*R.derivative :=
      (sub_eq_zero.mp hR).symm
    calc
      _ = C (2 : ℝ)*(C (1/2 : ℝ)*R.derivative.derivative) := by
        rw [← mul_assoc,← C_mul,show (2 : ℝ)*(1/2) = 1 by norm_num,C_1,one_mul]
      _ = C (2 : ℝ)*(C s*R.derivative) := by rw [he]
      _ = _ := by rw [← mul_assoc,← C_mul]
  have hz : R.derivative = 0 := derivative_eigenvalue_zero R.derivative (2*s) (mul_ne_zero (by norm_num) hs) hd
  have hconst := eq_C_of_derivative_eq_zero hz
  have hR0 : R.eval 0 = 0 := by dsimp [R]; rw [eval_sub,h0,sub_self]
  rw [hconst,eval_C] at hR0
  have hzero : R = 0 := by rw [hconst,hR0,C_0]
  exact sub_eq_zero.mp hzero

end PerronWright.PolynomialLinearODEUniqueness
