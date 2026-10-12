import PerronWright.Probability.BrownianGreenMonomialResponse
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Literal polynomial and differential equation of the Green response

The polynomial below evaluates to the already computed actual Green
integral. Its differential equation follows from its finite recursion.
-/

open Polynomial
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianGreenResponsePolynomial

open BrownianGreenMonomialResponse ExponentialMonomialTail

theorem responsePolynomial_zero (s y : ℝ) : responsePolynomial 0 s y = y/s := by
  unfold responsePolynomial
  simp only [tailPolynomial,zero_add,pow_one,Nat.cast_one,div_one]
  ring

theorem responsePolynomial_succ (n : ℕ) (s : ℝ) (hs : s ≠ 0) (y : ℝ) :
    responsePolynomial (n+1) s y = y^(n+2)/(s*((n+2 : ℕ) : ℝ))+
      ((n+1 : ℕ) : ℝ)/(2*s)*responsePolynomial n s y := by
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold responsePolynomial
  simp only [tailPolynomial,zero_pow (Nat.succ_ne_zero _),zero_div,zero_add]
  field_simp
  ring

theorem responsePolynomial_nonneg (n : ℕ) (s : ℝ) (hs : 0 < s) (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ responsePolynomial n s y := by
  induction n with
  | zero => rw [responsePolynomial_zero]; exact div_nonneg hy hs.le
  | succ n ih =>
    rw [responsePolynomial_succ n s hs.ne' y]
    exact add_nonneg (div_nonneg (pow_nonneg hy _) (by positivity))
      (mul_nonneg (by positivity) ih)

def responsePoly : ℕ → ℝ → ℝ[X]
  | 0, s => C (1/s)*X
  | n+1, s => C (1/(s*((n+2 : ℕ) : ℝ)))*X^(n+2)+
      C (((n+1 : ℕ) : ℝ)/(2*s))*responsePoly n s

theorem eval_responsePoly (n : ℕ) (s : ℝ) (hs : s ≠ 0) (y : ℝ) :
    (responsePoly n s).eval y = responsePolynomial n s y := by
  induction n with
  | zero => simp only [responsePoly,eval_mul,eval_C,eval_X,responsePolynomial_zero]; ring
  | succ n ih =>
    simp only [responsePoly,eval_add,eval_mul,eval_C,eval_pow,eval_X,ih,
      responsePolynomial_succ n s hs y]
    ring

theorem eval_zero_responsePoly (n : ℕ) (s : ℝ) : (responsePoly n s).eval 0 = 0 := by
  induction n with
  | zero => simp [responsePoly]
  | succ n ih => simp [responsePoly,ih]

private def responseOperator (s : ℝ) (P : ℝ[X]) : ℝ[X] :=
  C s*P.derivative-C (1/2 : ℝ)*P.derivative.derivative

private theorem responseOperator_add (s : ℝ) (P Q : ℝ[X]) :
    responseOperator s (P+Q) = responseOperator s P+responseOperator s Q := by
  unfold responseOperator
  rw [derivative_add,derivative_add]
  ring

private theorem responseOperator_const_mul (s c : ℝ) (P : ℝ[X]) :
    responseOperator s (C c*P) = C c*responseOperator s P := by
  unfold responseOperator
  rw [derivative_C_mul,derivative_C_mul]
  ring

private theorem responseOperator_leading (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    responseOperator s (C (1/(s*((n+2 : ℕ) : ℝ)))*X^(n+2)) =
      X^(n+1)-C (((n+1 : ℕ) : ℝ)/(2*s))*X^n := by
  have hn : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have h1 : (1/(s*((n+2 : ℕ) : ℝ)))*((n+2 : ℕ) : ℝ) = 1/s := by field_simp
  have h2 : s*(1/s) = 1 := by field_simp
  have h3 : (1/2 : ℝ)*((1/s)*((n+1 : ℕ) : ℝ)) = ((n+1 : ℕ) : ℝ)/(2*s) := by ring
  unfold responseOperator
  rw [derivative_C_mul_X_pow,show n+2-1 = n+1 by omega,h1,
    derivative_C_mul_X_pow,show n+1-1 = n by omega]
  rw [← mul_assoc,← C_mul,h2,C_1,one_mul,← mul_assoc,← C_mul,h3]

theorem responsePoly_differential_equation (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    C s*(responsePoly n s).derivative-
      C (1/2 : ℝ)*(responsePoly n s).derivative.derivative = X^n := by
  change responseOperator s (responsePoly n s) = X^n
  induction n with
  | zero =>
    unfold responseOperator
    simp only [responsePoly,derivative_C_mul_X,derivative_C,mul_zero,sub_zero,pow_zero,
      ← C_mul]
    rw [show s*(1/s) = 1 by field_simp,C_1]
  | succ n ih =>
    rw [responsePoly,responseOperator_add,responseOperator_leading n s hs,
      responseOperator_const_mul,ih]
    ring

end PerronWright.BrownianGreenResponsePolynomial
