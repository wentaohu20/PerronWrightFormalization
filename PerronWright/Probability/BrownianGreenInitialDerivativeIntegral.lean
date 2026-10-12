import PerronWright.Probability.BrownianKilledBoundaryPolynomial

/-! # Actual exponential insertion integral of the initial boundary slope

Finite polynomial expansion evaluates the integral explicitly. This
identifies the initial derivative without exchanging a boundary limit
and an integral or adding any new boundary theorem as a hypothesis.
-/

open MeasureTheory Set Polynomial
open scoped Polynomial Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianGreenInitialDerivativeIntegral

open BrownianGreenResponsePolynomial BrownianGreenPolynomialAction ExponentialMonomialTail
open BrownianKilledBoundaryPolynomial BrownianKilledBoundaryInsertionRecurrence

theorem responsePoly_initial_derivative (m : ℕ) (s : ℝ) (hs : s ≠ 0) :
    (responsePoly m s).derivative.eval 0 = 2*tailPolynomial m (2*s) 0 := by
  induction m with
  | zero =>
    simp only [responsePoly,derivative_C_mul_X,eval_C,tailPolynomial]
    field_simp
  | succ m ih =>
    rw [responsePoly,derivative_add,derivative_C_mul_X_pow,
      show m+2-1 = m+1 by omega,derivative_C_mul,eval_add,eval_mul,eval_mul,
      eval_C,eval_pow,eval_X,zero_pow (Nat.succ_ne_zero _),mul_zero,zero_add,ih,
      tailPolynomial,zero_pow (Nat.succ_ne_zero _),zero_div,zero_add]
    simp only [eval_C]
    ring

private theorem exponential_polynomial_expansion (P : ℝ[X]) (s z : ℝ) :
    2*Real.exp (-(2*s)*z)*P.eval z =
      ∑ m ∈ P.support, P.coeff m*(2*Real.exp (-(2*s)*z)*z^m) := by
  rw [eval_eq_sum,Polynomial.sum_def,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

theorem integrableOn_exponential_polynomial (P : ℝ[X]) (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun z : ℝ ↦ 2*Real.exp (-(2*s)*z)*P.eval z) (Ioi 0) := by
  have hf (m : ℕ) (_hm : m ∈ P.support) :
      IntegrableOn (fun z : ℝ ↦ P.coeff m*(2*Real.exp (-(2*s)*z)*z^m)) (Ioi 0) := by
    have hi := integrableOn_exponential_monomial m (2*s) (by positivity) 0 (by positivity)
    change Integrable _ (volume.restrict (Ioi 0))
    convert! (hi.const_mul 2).const_mul (P.coeff m) using 1
    funext z
    ring
  apply (integrable_finsetSum P.support hf).congr
  exact ae_of_all _ (fun z ↦ (exponential_polynomial_expansion P s z).symm)

theorem integral_exponential_polynomial_eq_green_initial_derivative
    (P : ℝ[X]) (s : ℝ) (hs : 0 < s) :
    (∫ z : ℝ in Ioi 0, 2*Real.exp (-(2*s)*z)*P.eval z) =
      (greenResponse s P).derivative.eval 0 := by
  have hf (m : ℕ) (_hm : m ∈ P.support) :
      IntegrableOn (fun z : ℝ ↦ P.coeff m*(2*Real.exp (-(2*s)*z)*z^m)) (Ioi 0) := by
    have hi := integrableOn_exponential_monomial m (2*s) (by positivity) 0 (by positivity)
    change Integrable _ (volume.restrict (Ioi 0))
    convert! (hi.const_mul 2).const_mul (P.coeff m) using 1
    funext z
    ring
  have hmon (m : ℕ) : (∫ z : ℝ in Ioi 0, 2*Real.exp (-(2*s)*z)*z^m) =
      2*tailPolynomial m (2*s) 0 := by
    have heq : (fun z : ℝ ↦ 2*Real.exp (-(2*s)*z)*z^m) =
        (fun z : ℝ ↦ 2*(Real.exp (-(2*s)*z)*z^m)) := by funext z; ring
    rw [heq,integral_const_mul,integral_exponential_monomial_tail _ _ (by positivity) 0 (by positivity)]
    simp
  calc
    _ = ∫ z : ℝ in Ioi 0, ∑ m ∈ P.support,
        P.coeff m*(2*Real.exp (-(2*s)*z)*z^m) :=
      setIntegral_congr_fun measurableSet_Ioi (fun z _ ↦ exponential_polynomial_expansion P s z)
    _ = ∑ m ∈ P.support, P.coeff m*(2*tailPolynomial m (2*s) 0) := by
      rw [integral_finsetSum P.support hf]
      simp_rw [integral_const_mul,hmon]
    _ = _ := by
      unfold greenResponse
      rw [Polynomial.sum_def,derivative_sum,eval_finsetSum]
      simp only [derivative_C_mul,eval_mul,eval_C,responsePoly_initial_derivative _ _ hs.ne']

theorem integral_boundary_insertion_eq_initial_slope (n : ℕ) (s : ℝ) (hs : 0 < s) :
    ((n+1 : ℕ) : ℝ)*
      (∫ z : ℝ in Ioi 0, 2*Real.exp (-(2*s)*z)*z*(boundaryPolynomial n s).eval z) =
      (boundaryPolynomial (n+1) s).derivative.eval 0 := by
  have h := integral_exponential_polynomial_eq_green_initial_derivative
    (X*boundaryPolynomial n s) s hs
  rw [boundaryPolynomial,derivative_C_mul,eval_mul,eval_C]
  rw [← h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z _
  dsimp only
  rw [eval_mul,eval_X]
  ring

theorem actual_boundary_insertion_lintegral_eq_initial_slope
    (n : ℕ) (p : ℝ) (hp : 0 < p) :
    ((n+1 : ℕ) : ℝ≥0∞)*
      (∫⁻ z : ℝ, ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p)))*
        ENNReal.ofReal z*boundarySlopeNN n p z) =
      ENNReal.ofReal ((boundaryPolynomial (n+1) (Real.sqrt (2*p))).derivative.eval 0) := by
  let s := Real.sqrt (2*p)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hfull : (∫⁻ z : ℝ, ENNReal.ofReal (2*Real.exp (-z*s))*ENNReal.ofReal z*
      boundarySlopeNN n p z) =
      ∫⁻ z : ℝ in Ioi 0, ENNReal.ofReal (2*Real.exp (-z*s))*ENNReal.ofReal z*
        boundarySlopeNN n p z := by
    symm
    apply setLIntegral_eq_of_support_subset
    intro z hz
    by_contra hz0
    have hzle : z ≤ 0 := le_of_not_gt hz0
    simp only [Function.mem_support,ENNReal.ofReal_eq_zero.mpr hzle,mul_zero,zero_mul,
      ne_eq,not_true_eq_false] at hz
  have hreplace : (∫⁻ z : ℝ in Ioi 0, ENNReal.ofReal (2*Real.exp (-z*s))*ENNReal.ofReal z*
      boundarySlopeNN n p z) =
      ∫⁻ z : ℝ in Ioi 0, ENNReal.ofReal
        (2*Real.exp (-(2*s)*z)*z*(boundaryPolynomial n s).eval z) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [boundarySlopeNN_eq_polynomial n p hp z hz,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*Real.exp (-z*s)),
      ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hz.le)]
    congr 1
    change (2*Real.exp (-z*s)*z)*(Real.exp (-s*z)*(boundaryPolynomial n s).eval z) = _
    rw [show (2*Real.exp (-z*s)*z)*(Real.exp (-s*z)*(boundaryPolynomial n s).eval z) =
      2*(Real.exp (-z*s)*Real.exp (-s*z))*z*(boundaryPolynomial n s).eval z by ring,
      ← Real.exp_add,show -z*s+-s*z = -(2*s)*z by ring]
  have hi : IntegrableOn (fun z : ℝ ↦ 2*Real.exp (-(2*s)*z)*z*
      (boundaryPolynomial n s).eval z) (Ioi 0) := by
    convert! integrableOn_exponential_polynomial (X*boundaryPolynomial n s) s hs using 1
    funext z
    rw [eval_mul,eval_X]
    ring
  have hnonneg : ∀ᵐ z : ℝ ∂volume.restrict (Ioi 0),
      0 ≤ 2*Real.exp (-(2*s)*z)*z*(boundaryPolynomial n s).eval z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact mul_nonneg (mul_nonneg (by positivity) hz.le) (boundaryPolynomial_nonneg n p hp z hz)
  change ((n+1 : ℕ) : ℝ≥0∞)*
    (∫⁻ z : ℝ, ENNReal.ofReal (2*Real.exp (-z*s))*ENNReal.ofReal z*boundarySlopeNN n p z) = _
  rw [hfull,hreplace,← ofReal_integral_eq_lintegral_ofReal hi hnonneg,
    ← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg (n+1)),
    integral_boundary_insertion_eq_initial_slope n s hs]

end PerronWright.BrownianGreenInitialDerivativeIntegral
