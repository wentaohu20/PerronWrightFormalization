import PerronWright.Probability.BrownianKilledBoundaryInsertionRecurrence
import PerronWright.Probability.BrownianGreenPolynomialAction
import PerronWright.Probability.BrownianKilledAreaResolventBoundary

/-! # Genuine all-order polynomial representation of the boundary response

The literal polynomial recursion is identified with the actual Kac
boundary insertion. Thus the actual Brownian resolvent boundary slope
has this representation, with its differential equation proved rather
than imposed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Polynomial
open scoped Classical NNReal ENNReal Polynomial
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianKilledBoundaryPolynomial

open BrownianKilledAreaMomentResolvent BrownianKilledGreenKernel
open BrownianKilledAreaResolventBoundary BrownianKilledBoundaryInsertionRecurrence
open BrownianGreenPolynomialAction

def boundaryPolynomial : ℕ → ℝ → ℝ[X]
  | 0, _ => C 2
  | n+1, s => C ((n+1 : ℕ) : ℝ)*greenResponse s (X*boundaryPolynomial n s)

theorem boundaryPolynomial_succ_zero (n : ℕ) (s : ℝ) :
    (boundaryPolynomial (n+1) s).eval 0 = 0 := by
  simp only [boundaryPolynomial,eval_mul,eval_C,eval_zero_greenResponse,mul_zero]

theorem boundaryPolynomial_differential_equation (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    C s*(boundaryPolynomial (n+1) s).derivative-
      C (1/2 : ℝ)*(boundaryPolynomial (n+1) s).derivative.derivative =
        C ((n+1 : ℕ) : ℝ)*X*boundaryPolynomial n s := by
  rw [boundaryPolynomial,derivative_C_mul,derivative_C_mul]
  calc
    _ = C ((n+1 : ℕ) : ℝ)*(C s*(greenResponse s (X*boundaryPolynomial n s)).derivative-
        C (1/2 : ℝ)*(greenResponse s (X*boundaryPolynomial n s)).derivative.derivative) := by ring
    _ = _ := by rw [greenResponse_differential_equation s hs]; ring

theorem boundaryPolynomial_nonneg (n : ℕ) (p : ℝ) (hp : 0 < p)
    (y : ℝ) (hy : 0 < y) : 0 ≤ (boundaryPolynomial n (Real.sqrt (2*p))).eval y := by
  induction n generalizing y with
  | zero => norm_num [boundaryPolynomial]
  | succ n ih =>
    rw [boundaryPolynomial,eval_mul,eval_C]
    apply mul_nonneg (by positivity)
    have hI : 0 ≤ ∫ z : ℝ in Ioi 0, greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*
        (X*boundaryPolynomial n (Real.sqrt (2*p))).eval z := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      rw [eval_mul,eval_X]
      exact mul_nonneg (mul_nonneg (greenReal_nonneg p y z hy hz) (Real.exp_pos _).le)
        (mul_nonneg hz.le (ih z hz))
    rw [integral_green_polynomial _ p hp y hy.le] at hI
    exact nonneg_of_mul_nonneg_right hI (Real.exp_pos _)

theorem boundarySlopeNN_eq_polynomial (n : ℕ) (p : ℝ) (hp : 0 < p)
    (y : ℝ) (hy : 0 < y) :
    boundarySlopeNN n p y = ENNReal.ofReal
      (Real.exp (-Real.sqrt (2*p)*y)*(boundaryPolynomial n (Real.sqrt (2*p))).eval y) := by
  induction n generalizing y with
  | zero =>
    simp only [boundarySlopeNN,boundaryPolynomial,eval_C]
    congr 1
    rw [show -y*Real.sqrt (2*p) = -Real.sqrt (2*p)*y by ring]
    ring
  | succ n ih =>
    rw [boundarySlopeNN_recurrence n p hp y]
    have hfull : (∫⁻ z : ℝ, resolvent 0 p y z*ENNReal.ofReal z*boundarySlopeNN n p z) =
        ∫⁻ z : ℝ in Ioi 0, resolvent 0 p y z*ENNReal.ofReal z*boundarySlopeNN n p z := by
      symm
      apply setLIntegral_eq_of_support_subset
      intro z hz
      by_contra hz0
      have hzle : z ≤ 0 := le_of_not_gt hz0
      simp only [Function.mem_support,ENNReal.ofReal_eq_zero.mpr hzle,mul_zero,zero_mul,ne_eq,not_true_eq_false] at hz
    have hreplace : (∫⁻ z : ℝ in Ioi 0, resolvent 0 p y z*ENNReal.ofReal z*boundarySlopeNN n p z) =
        ∫⁻ z : ℝ in Ioi 0, resolvent 0 p y z*ENNReal.ofReal
          (Real.exp (-Real.sqrt (2*p)*z)*(X*boundaryPolynomial n (Real.sqrt (2*p))).eval z) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      rw [ih z hz,mul_assoc,← ENNReal.ofReal_mul hz.le]
      congr 2
      rw [eval_mul,eval_X]
      ring
    rw [hfull,hreplace,actual_green_polynomial_response _ p hp y hy
      (by intro z hz
          rw [eval_mul,eval_X]
          exact mul_nonneg hz.le (boundaryPolynomial_nonneg n p hp z hz))]
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg (n+1))]
    congr 1
    rw [boundaryPolynomial,eval_mul,eval_C]
    ring

theorem actual_resolvent_succ_polynomial_boundary_slope (n : ℕ) (p : ℝ) (hp : 0 < p)
    (y : ℝ) (hy : 0 < y) :
    Tendsto (fun x : ℝ ↦ resolvent (n+1) p x y/ENNReal.ofReal x) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (Real.exp (-Real.sqrt (2*p)*y)*
        (boundaryPolynomial (n+1) (Real.sqrt (2*p))).eval y))) := by
  have h := actual_resolvent_succ_boundary_slope n p hp y
  change Tendsto _ _ (𝓝 (boundarySlopeNN (n+1) p y)) at h
  rwa [boundarySlopeNN_eq_polynomial (n+1) p hp y hy] at h

end PerronWright.BrownianKilledBoundaryPolynomial
