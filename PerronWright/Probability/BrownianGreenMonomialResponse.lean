import PerronWright.Probability.ExponentialMonomialTail
import PerronWright.Probability.BrownianKilledGreenBoundary
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exact monomial response of the genuine killed Green kernel

Splitting at the observation state evaluates the positive Green
integral of each exponentially weighted monomial. The resulting finite
polynomial is obtained from actual improper integrals.
-/

open MeasureTheory Filter Topology Set
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianGreenMonomialResponse

open BrownianKilledGreenKernel BrownianKilledGreenBoundary ExponentialMonomialTail

theorem green_weighted_of_target_le (p y z : ℝ) (hzy : z ≤ y) :
    greenReal p y z*Real.exp (-Real.sqrt (2*p)*z) =
      Real.exp (-Real.sqrt (2*p)*y)/Real.sqrt (2*p)*
        (1-Real.exp (-(2*Real.sqrt (2*p))*z)) := by
  let s := Real.sqrt (2*p)
  have he1 : Real.exp (-|z-y| * s)*Real.exp (-s*z) = Real.exp (-s*y) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hzy),← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (-(y+z)*s)*Real.exp (-s*z) =
      Real.exp (-s*y)*Real.exp (-(2*s)*z) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  change ((Real.exp (-|z-y| * s)-Real.exp (-(y+z)*s))/s)*Real.exp (-s*z) = _
  rw [div_mul_eq_mul_div,sub_mul,he1,he2]
  dsimp only [s]
  ring

theorem green_weighted_of_initial_le (p y z : ℝ) (hyz : y ≤ z) :
    greenReal p y z*Real.exp (-Real.sqrt (2*p)*z) =
      (Real.exp (Real.sqrt (2*p)*y)-Real.exp (-Real.sqrt (2*p)*y))/Real.sqrt (2*p)*
        Real.exp (-(2*Real.sqrt (2*p))*z) := by
  let s := Real.sqrt (2*p)
  have he1 : Real.exp (-|z-y| * s)*Real.exp (-s*z) =
      Real.exp (s*y)*Real.exp (-(2*s)*z) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hyz),← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (-(y+z)*s)*Real.exp (-s*z) =
      Real.exp (-s*y)*Real.exp (-(2*s)*z) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  change ((Real.exp (-|z-y| * s)-Real.exp (-(y+z)*s))/s)*Real.exp (-s*z) = _
  rw [div_mul_eq_mul_div,sub_mul,he1,he2]
  dsimp only [s]
  ring

private theorem continuous_green_monomial (m : ℕ) (p y : ℝ) :
    Continuous (fun z : ℝ ↦ greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*z^m) := by
  unfold greenReal
  fun_prop

private theorem integrableOn_green_monomial_tail (m : ℕ) (p : ℝ) (hp : 0 < p)
    (y : ℝ) (hy : 0 ≤ y) :
    IntegrableOn (fun z : ℝ ↦ greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*z^m) (Ioi y) := by
  have hs : 0 < 2*Real.sqrt (2*p) := by positivity
  apply ((integrableOn_exponential_monomial m _ hs y hy).const_mul
    ((Real.exp (Real.sqrt (2*p)*y)-Real.exp (-Real.sqrt (2*p)*y))/Real.sqrt (2*p))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [green_weighted_of_initial_le p y z hz.le]
  ring

theorem integrableOn_green_monomial (m : ℕ) (p : ℝ) (hp : 0 < p)
    (y : ℝ) (hy : 0 ≤ y) :
    IntegrableOn (fun z : ℝ ↦ greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*z^m) (Ioi 0) := by
  have hi : IntervalIntegrable (fun z : ℝ ↦ greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*z^m)
      volume 0 y := (continuous_green_monomial m p y).intervalIntegrable 0 y
  have hf := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mp hi).union
    (integrableOn_green_monomial_tail m p hp y hy)
  simpa only [Ioc_union_Ioi_eq_Ioi hy] using hf

def responsePolynomial (m : ℕ) (s y : ℝ) : ℝ :=
  (y^(m+1)/((m+1 : ℕ) : ℝ)+tailPolynomial m (2*s) y-tailPolynomial m (2*s) 0)/s

theorem integral_green_monomial (m : ℕ) (p : ℝ) (hp : 0 < p)
    (y : ℝ) (hy : 0 ≤ y) :
    (∫ z : ℝ in Ioi 0, greenReal p y z*Real.exp (-Real.sqrt (2*p)*z)*z^m) =
      Real.exp (-Real.sqrt (2*p)*y)*responsePolynomial m (Real.sqrt (2*p)) y := by
  let s := Real.sqrt (2*p)
  have hs : 0 < 2*s := by dsimp [s]; positivity
  have hmono := integrableOn_exponential_monomial m (2*s) hs 0 le_rfl
  have hshort : (∫ z : ℝ in 0..y, Real.exp (-(2*s)*z)*z^m) =
      tailPolynomial m (2*s) 0-Real.exp (-(2*s)*y)*tailPolynomial m (2*s) y := by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi hmono hy,
      integral_exponential_monomial_tail m (2*s) hs 0 le_rfl,
      integral_exponential_monomial_tail m (2*s) hs y hy]
    simp only [mul_zero,Real.exp_zero,one_mul]
  have hleft : (∫ z : ℝ in 0..y, greenReal p y z*Real.exp (-s*z)*z^m) =
      Real.exp (-s*y)/s*(y^(m+1)/((m+1 : ℕ) : ℝ)-
        (tailPolynomial m (2*s) 0-Real.exp (-(2*s)*y)*tailPolynomial m (2*s) y)) := by
    calc
      _ = ∫ z : ℝ in 0..y, Real.exp (-s*y)/s*(z^m-Real.exp (-(2*s)*z)*z^m) := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [uIcc_of_le hy] at hz
        dsimp only [s]
        rw [green_weighted_of_target_le p y z hz.2]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub
          ((continuous_pow m).intervalIntegrable 0 y)
          ((by fun_prop : Continuous (fun z : ℝ ↦ Real.exp (-(2*s)*z)*z^m)).intervalIntegrable 0 y),
          integral_pow,hshort]
        simp only [zero_pow (Nat.succ_ne_zero _),sub_zero,Nat.cast_add,Nat.cast_one]
  have hright : (∫ z : ℝ in Ioi y, greenReal p y z*Real.exp (-s*z)*z^m) =
      (Real.exp (s*y)-Real.exp (-s*y))/s*
        (Real.exp (-(2*s)*y)*tailPolynomial m (2*s) y) := by
    calc
      _ = ∫ z : ℝ in Ioi y, (Real.exp (s*y)-Real.exp (-s*y))/s*
          (Real.exp (-(2*s)*z)*z^m) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro z hz
        dsimp only [s]
        rw [green_weighted_of_initial_le p y z hz.le]
        ring
      _ = _ := by
        rw [integral_const_mul,integral_exponential_monomial_tail m (2*s) hs y hy]
  have he : Real.exp (s*y)*Real.exp (-(2*s)*y) = Real.exp (-s*y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← intervalIntegral.integral_interval_add_Ioi
    (integrableOn_green_monomial m p hp y hy)
    (integrableOn_green_monomial_tail m p hp y hy)]
  change (∫ z : ℝ in 0..y, greenReal p y z*Real.exp (-s*z)*z^m)+
      (∫ z : ℝ in Ioi y, greenReal p y z*Real.exp (-s*z)*z^m) = _
  rw [hleft,hright]
  unfold responsePolynomial
  change _ = Real.exp (-s*y)*((y^(m+1)/((m+1 : ℕ) : ℝ)+
    tailPolynomial m (2*s) y-tailPolynomial m (2*s) 0)/s)
  calc
    _ = Real.exp (-s*y)*(y^(m+1)/((m+1 : ℕ) : ℝ)-tailPolynomial m (2*s) 0)/s+
        (Real.exp (s*y)*Real.exp (-(2*s)*y))*tailPolynomial m (2*s) y/s := by ring
    _ = _ := by rw [he]; ring

end PerronWright.BrownianGreenMonomialResponse
