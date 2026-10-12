import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Exact exponentially weighted monomial tails

Finite recursive polynomials give antiderivatives of every nonnegative
monomial times a decaying exponential. The improper integral is proved
from the derivative and its actual limit, not supplied as an interface.
-/

open MeasureTheory Filter Topology Set
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.ExponentialMonomialTail

def tailPolynomial : ℕ → ℝ → ℝ → ℝ
  | 0, s, _ => 1/s
  | n+1, s, y => y^(n+1)/s+((n+1 : ℕ) : ℝ)/s*tailPolynomial n s y

def tailPrimitive (n : ℕ) (s y : ℝ) : ℝ :=
  -Real.exp (-s*y)*tailPolynomial n s y

theorem tailPrimitive_succ (n : ℕ) (s y : ℝ) :
    tailPrimitive (n+1) s y = -Real.exp (-s*y)*y^(n+1)/s+
      ((n+1 : ℕ) : ℝ)/s*tailPrimitive n s y := by
  unfold tailPrimitive
  rw [tailPolynomial]
  ring

theorem tailPolynomial_nonneg (n : ℕ) (s : ℝ) (hs : 0 < s)
    (y : ℝ) (hy : 0 ≤ y) : 0 ≤ tailPolynomial n s y := by
  induction n with
  | zero => dsimp [tailPolynomial]; positivity
  | succ n ih =>
    dsimp only [tailPolynomial]
    exact add_nonneg (div_nonneg (pow_nonneg hy _) hs.le)
      (mul_nonneg (by positivity) ih)

theorem hasDerivAt_tailPrimitive (n : ℕ) (s : ℝ) (hs : s ≠ 0) (y : ℝ) :
    HasDerivAt (tailPrimitive n s) (Real.exp (-s*y)*y^n) y := by
  have he : HasDerivAt (fun z : ℝ ↦ Real.exp (-s*z))
      (-s*Real.exp (-s*y)) y := by
    simpa only [id_eq,mul_one,mul_comm] using ((hasDerivAt_id y).const_mul (-s)).exp
  induction n with
  | zero =>
    convert! (he.neg.div_const s) using 1
    · funext z
      simp only [tailPrimitive,tailPolynomial]
      dsimp
      ring
    · simp only [pow_zero,mul_one]
      field_simp
  | succ n ih =>
    have hp := hasDerivAt_pow (n+1) y
    have h := (he.mul hp).neg.div_const s
    have hsum := h.add (ih.const_mul (((n+1 : ℕ) : ℝ)/s))
    convert! hsum using 1
    · funext z
      rw [tailPrimitive_succ]
      dsimp
      ring
    · dsimp
      simp only [Nat.cast_add,Nat.cast_one]
      field_simp
      ring

theorem tendsto_tailPrimitive (n : ℕ) (s : ℝ) (hs : 0 < s) :
    Tendsto (tailPrimitive n s) atTop (𝓝 0) := by
  have hm (m : ℕ) : Tendsto (fun y : ℝ ↦ y^m*Real.exp (-s*y)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m : ℝ) s hs
  induction n with
  | zero =>
    convert! (hm 0).const_mul (-1/s) using 1
    · funext y
      simp only [tailPrimitive,tailPolynomial,pow_zero,one_mul]
      ring
    · norm_num
  | succ n ih =>
    convert! ((hm (n+1)).const_mul (-1/s)).add
      (ih.const_mul (((n+1 : ℕ) : ℝ)/s)) using 1
    · funext y
      rw [tailPrimitive_succ]
      ring
    · norm_num

theorem integrableOn_exponential_monomial (n : ℕ) (s : ℝ) (hs : 0 < s)
    (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun y : ℝ ↦ Real.exp (-s*y)*y^n) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun _y _ ↦ hasDerivAt_tailPrimitive n s hs.ne' _y)
    (fun y hy ↦ mul_nonneg (Real.exp_pos _).le (pow_nonneg (ha.trans (show a ≤ y from hy.le)) n))
    (tendsto_tailPrimitive n s hs)

theorem integral_exponential_monomial_tail (n : ℕ) (s : ℝ) (hs : 0 < s)
    (a : ℝ) (ha : 0 ≤ a) :
    (∫ y : ℝ in Ioi a, Real.exp (-s*y)*y^n) =
      Real.exp (-s*a)*tailPolynomial n s a := by
  simpa only [tailPrimitive,zero_sub,neg_mul,neg_neg] using
    integral_Ioi_of_hasDerivAt_of_nonneg'
      (fun y _ ↦ hasDerivAt_tailPrimitive n s hs.ne' y)
      (fun y hy ↦ mul_nonneg (Real.exp_pos _).le (pow_nonneg (ha.trans hy.le) _))
      (tendsto_tailPrimitive n s hs)

end PerronWright.ExponentialMonomialTail
