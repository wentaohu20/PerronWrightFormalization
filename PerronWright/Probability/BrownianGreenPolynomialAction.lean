import PerronWright.Probability.BrownianGreenResponsePolynomial

/-! # Actual Green action on every exponentially weighted polynomial

Finite monomial expansion identifies the integral with a literal
polynomial. Its zero boundary value and differential equation follow
from the already proved monomial calculation.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Polynomial
open scoped Classical NNReal ENNReal Polynomial
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianGreenPolynomialAction

open BrownianKilledAreaMomentResolvent BrownianKilledGreenKernel
open BrownianGreenMonomialResponse BrownianGreenResponsePolynomial

def greenResponse (s : ℝ) (P : ℝ[X]) : ℝ[X] :=
  P.sum (fun m a ↦ C a*responsePoly m s)

theorem eval_zero_greenResponse (s : ℝ) (P : ℝ[X]) : (greenResponse s P).eval 0 = 0 := by
  unfold greenResponse
  rw [Polynomial.eval_sum,Polynomial.sum_def]
  simp only [eval_mul,eval_C,eval_zero_responsePoly,mul_zero,Finset.sum_const_zero]

theorem greenResponse_differential_equation (s : ℝ) (hs : s ≠ 0) (P : ℝ[X]) :
    C s*(greenResponse s P).derivative-
      C (1/2 : ℝ)*(greenResponse s P).derivative.derivative = P := by
  unfold greenResponse
  rw [Polynomial.sum_def]
  simp only [derivative_sum,derivative_C_mul]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  calc
    _ = ∑ m ∈ P.support, C (P.coeff m)*(C s*(responsePoly m s).derivative-
        C (1/2 : ℝ)*(responsePoly m s).derivative.derivative) :=
      Finset.sum_congr rfl (fun m _ ↦ by ring)
    _ = ∑ m ∈ P.support, C (P.coeff m)*X^m := by
      simp_rw [responsePoly_differential_equation _ _ hs]
    _ = P := P.sum_C_mul_X_pow_eq

private theorem weighted_polynomial_expansion (P : ℝ[X]) (p y z : ℝ) :
    greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*P.eval z =
      ∑ m ∈ P.support, P.coeff m*(greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*z^m) := by
  rw [Polynomial.eval_eq_sum,Polynomial.sum_def,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ ↦ by ring)

theorem integrableOn_green_polynomial (P : ℝ[X]) (p : ℝ) (hp : 0 < p)
    (y : ℝ) (hy : 0 ≤ y) :
    IntegrableOn (fun z : ℝ ↦ greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*P.eval z) (Ioi 0) := by
  have hf (m : ℕ) (_hm : m ∈ P.support) :
      IntegrableOn (fun z : ℝ ↦ P.coeff m*(greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*z^m)) (Ioi 0) :=
    (integrableOn_green_monomial m p hp y hy).const_mul (P.coeff m)
  apply (integrable_finsetSum P.support hf).congr
  exact ae_of_all _ (fun z ↦ (weighted_polynomial_expansion P p y z).symm)

theorem integral_green_polynomial (P : ℝ[X]) (p : ℝ) (hp : 0 < p)
    (y : ℝ) (hy : 0 ≤ y) :
    (∫ z : ℝ in Ioi 0, greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*P.eval z) =
      Real.exp (-Real.sqrt (2*p)*y)*(greenResponse (Real.sqrt (2*p)) P).eval y := by
  have hs : Real.sqrt (2*p) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < 2*p)).ne'
  have hf (m : ℕ) (_hm : m ∈ P.support) :
      IntegrableOn (fun z : ℝ ↦ P.coeff m*(greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*z^m)) (Ioi 0) :=
    (integrableOn_green_monomial m p hp y hy).const_mul (P.coeff m)
  calc
    _ = ∫ z : ℝ in Ioi 0, ∑ m ∈ P.support,
        P.coeff m*(greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*z^m) :=
      setIntegral_congr_fun measurableSet_Ioi (fun z _ ↦ weighted_polynomial_expansion P p y z)
    _ = ∑ m ∈ P.support, P.coeff m*(Real.exp (-Real.sqrt (2*p)*y)*
        responsePolynomial m (Real.sqrt (2*p)) y) := by
      rw [integral_finsetSum P.support hf]
      simp_rw [integral_const_mul,integral_green_monomial _ p hp y hy]
    _ = _ := by
      unfold greenResponse
      rw [Polynomial.eval_sum,Polynomial.sum_def,Finset.mul_sum]
      simp only [Polynomial.eval_mul,Polynomial.eval_C,eval_responsePoly _ _ hs]
      exact Finset.sum_congr rfl (fun m _ ↦ by ring)

theorem actual_green_polynomial_response (P : ℝ[X]) (p : ℝ) (hp : 0 < p)
    (y : ℝ) (hy : 0 < y) (hP : ∀ z : ℝ, 0 < z → 0 ≤ P.eval z) :
    (∫⁻ z : ℝ in Ioi 0, resolvent 0 p y z*
      ENNReal.ofReal (Real.exp (-Real.sqrt (2*p)*z)*P.eval z)) =
        ENNReal.ofReal (Real.exp (-Real.sqrt (2*p)*y)*(greenResponse (Real.sqrt (2*p)) P).eval y) := by
  have he : (∫⁻ z : ℝ in Ioi 0, resolvent 0 p y z*
      ENNReal.ofReal (Real.exp (-Real.sqrt (2*p)*z)*P.eval z)) =
      ∫⁻ z : ℝ in Ioi 0, ENNReal.ofReal
        (greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*P.eval z) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [resolvent_zero_eq_green p hp y z hy hz,
      ← ENNReal.ofReal_mul (greenReal_nonneg p y z hy hz)]
    congr 1
    ring
  rw [he,← ofReal_integral_eq_lintegral_ofReal (integrableOn_green_polynomial P p hp y hy.le)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        exact mul_nonneg (mul_nonneg (greenReal_nonneg p y z hy hz)
          (Real.exp_pos _).le) (hP z hz)),integral_green_polynomial P p hp y hy.le]

end PerronWright.BrownianGreenPolynomialAction
