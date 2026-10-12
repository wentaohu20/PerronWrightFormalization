import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # All-order polynomial control of the actual area Laplace weight

The negative exponential has a global Taylor remainder bound on the
nonnegative half-line. This is proved from the Lagrange remainder, rather
than supplied as a stochastic differentiability or moment interface.
-/

open Set
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace PerronWright.BrownianKilledAreaLaplaceTaylorGeometry

def negativeExponentialTaylor (n : ℕ) (v : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (-v)^j/(j.factorial : ℝ)

theorem taylorWithin_negative_exponential (n : ℕ) (v : ℝ) (hv : 0 < v) :
    taylorWithinEval (fun z : ℝ ↦ Real.exp ((-1 : ℝ)*z)) n (uIcc 0 v) 0 v =
      negativeExponentialTaylor n v := by
  have hd (j : ℕ) : ContDiffAt ℝ j (fun z : ℝ ↦ Real.exp ((-1 : ℝ)*z)) 0 := by
    fun_prop
  induction n with
  | zero => simp [negativeExponentialTaylor]
  | succ n ih =>
    have hp : negativeExponentialTaylor (n+1) v = negativeExponentialTaylor n v+
        (-v)^(n+1)/((n+1).factorial : ℝ) := by
      unfold negativeExponentialTaylor
      rw [Finset.sum_range_succ]
    rw [taylorWithinEval_succ,ih,hp]
    congr 1
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_uIcc (ne_of_gt hv).symm) (hd (n+1)) (left_mem_uIcc)]
    rw [iteratedDeriv_exp_const_mul]
    simp only [mul_zero,Real.exp_zero,mul_one,sub_zero,smul_eq_mul]
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [show (-v)^(n+1) = (-1 : ℝ)^(n+1)*v^(n+1) by
      rw [← neg_one_mul v,mul_pow]]
    simp only [div_eq_mul_inv]
    ring

theorem negative_exponential_taylor_bound (n : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    |Real.exp (-v)-negativeExponentialTaylor n v| ≤
      v^(n+1)/((n+1).factorial : ℝ) := by
  rcases eq_or_lt_of_le hv with hzero | hpos
  · subst v
    have hsum : negativeExponentialTaylor n 0 = 1 := by
      unfold negativeExponentialTaylor
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj
        simp [zero_pow hj]
      · simp
    simp [hsum]
  have hf : ContDiffOn ℝ (n+1) (fun z : ℝ ↦ Real.exp ((-1 : ℝ)*z)) (uIcc 0 v) := by
    fun_prop
  obtain ⟨z,hz,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (ne_of_gt hpos).symm hf
  rw [taylorWithin_negative_exponential n v hpos,iteratedDeriv_exp_const_mul] at he
  have hzpos : 0 < z := by
    rw [uIoo_of_le hv] at hz
    exact hz.1
  have hexp : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hzpos.le)
  have hfac : 0 ≤ ((n+1).factorial : ℝ) := Nat.cast_nonneg _
  have he' : Real.exp (-v)-negativeExponentialTaylor n v =
      (-1 : ℝ)^(n+1)*Real.exp (-z)*v^(n+1)/((n+1).factorial : ℝ) := by
    simpa only [neg_one_mul,sub_zero] using he
  rw [he',abs_div,abs_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    Real.abs_exp,abs_pow,abs_of_nonneg hv,abs_of_nonneg hfac]
  exact div_le_div_of_nonneg_right
    ((mul_le_mul_of_nonneg_right hexp (pow_nonneg hv (n+1))).trans_eq (one_mul _)) hfac

theorem area_exponential_taylor_bound (n : ℕ) (u A : ℝ) (hu : 0 ≤ u) (hA : 0 ≤ A) :
    |Real.exp (-u*A)-∑ j ∈ Finset.range (n+1),
        ((-u)^j/(j.factorial : ℝ))*A^j| ≤
      (u^(n+1)/((n+1).factorial : ℝ))*A^(n+1) := by
  have he : negativeExponentialTaylor n (u*A) =
      ∑ j ∈ Finset.range (n+1), ((-u)^j/(j.factorial : ℝ))*A^j := by
    unfold negativeExponentialTaylor
    apply Finset.sum_congr rfl
    intro j _
    rw [← neg_mul,mul_pow]
    ring
  have h := negative_exponential_taylor_bound n (u*A) (mul_nonneg hu hA)
  rw [he,mul_pow] at h
  simpa only [neg_mul,div_mul_eq_mul_div] using h

end PerronWright.BrownianKilledAreaLaplaceTaylorGeometry
