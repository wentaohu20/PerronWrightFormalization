import PerronWright.Probability.CriticalScalarField
import PerronWright.Probability.FactorialDensity

/-! # The literal thermal, cubic, and enumeration exponent combination -/

open Filter Topology
open scoped Real Topology

noncomputable section
set_option maxHeartbeats 600000

namespace PerronWright.CriticalEnumeratorExponent

/-- The actual squared critical time displacement has precisely the
enumeration Gaussian rate on the normalized component-size scale. -/
theorem quadratic_time_size_tendsto (N K : ℕ → ℕ)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop) (lambda : ℝ) {s : ℝ}
    (hs : Tendsto (fun m ↦ (K m : ℝ)/(N m : ℝ)^(2/3 : ℝ)) atTop (𝓝 s)) :
    Tendsto (fun m ↦ (CriticalScaling.time lambda (N m)-1)^2*(K m : ℝ))
      atTop (𝓝 (lambda^2*s)) := by
  apply (hs.const_mul (lambda^2)).congr'
  filter_upwards [hNt.eventually (CriticalScaling.time_eq_raw_eventually lambda)] with m hm
  have hn : (0 : ℝ) < N m := Nat.cast_pos.mpr (hN m)
  have hA : (N m : ℝ)^(2/3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
  have hp := CriticalScalarField.twoThird_mul_negativeThird_sq hn
  rw [hm]
  have hscale : ((N m : ℝ)^(-(1/3 : ℝ)))^2 =
      ((N m : ℝ)^(2/3 : ℝ))⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hA).mpr
    simpa only [mul_comm] using hp
  rw [show 1 + lambda*(N m : ℝ)^(-(1/3 : ℝ))-1 =
    lambda*(N m : ℝ)^(-(1/3 : ℝ)) by ring,mul_pow,hscale]
  ring

/-- Combining the true residual coefficients with the enumeration rate
gives the literal density exponent, with no Brownian identification assumed. -/
theorem combined_exponent_tendsto (N K : ℕ → ℕ)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (lambda alpha beta : ℝ) {s : ℝ}
    (hs : Tendsto (fun m ↦ (K m : ℝ)/(N m : ℝ)^(2/3 : ℝ)) atTop (𝓝 s)) :
    Tendsto (fun m ↦
      alpha/2*((CriticalScaling.time lambda (N m)-1)*(K m : ℝ)^2/(N m : ℝ)) -
      beta/6*((K m : ℝ)^3/(N m : ℝ)^2) -
      alpha^2/(2*beta)*((CriticalScaling.time lambda (N m)-1)^2*(K m : ℝ)))
      atTop (𝓝 (-FactorialDensity.criticalExponent alpha beta lambda s)) := by
  have hr := CriticalResidualScaling.perron_residual_exponent_tendsto N K hN hNt lambda alpha beta hs
  have hg := (quadratic_time_size_tendsto N K hN hNt lambda hs).const_mul (alpha^2/(2*beta))
  have h := hr.sub hg
  have he : lambda*alpha*s^2/2-beta*s^3/6-alpha^2/(2*beta)*(lambda^2*s) =
      -FactorialDensity.criticalExponent alpha beta lambda s := by
    unfold FactorialDensity.criticalExponent
    ring
  simpa only [he] using h

theorem combined_exponential_tendsto (N K : ℕ → ℕ)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (lambda alpha beta : ℝ) {s : ℝ}
    (hs : Tendsto (fun m ↦ (K m : ℝ)/(N m : ℝ)^(2/3 : ℝ)) atTop (𝓝 s)) :
    Tendsto (fun m ↦ Real.exp (
      alpha/2*((CriticalScaling.time lambda (N m)-1)*(K m : ℝ)^2/(N m : ℝ)) -
      beta/6*((K m : ℝ)^3/(N m : ℝ)^2) -
      alpha^2/(2*beta)*((CriticalScaling.time lambda (N m)-1)^2*(K m : ℝ))))
      atTop (𝓝 (Real.exp (-FactorialDensity.criticalExponent alpha beta lambda s))) :=
  (Real.continuous_exp.tendsto _).comp
    (combined_exponent_tendsto N K hN hNt lambda alpha beta hs)

end PerronWright.CriticalEnumeratorExponent
