import PerronWright.Probability.CriticalConnectedEnumeration
import PerronWright.Probability.FactorialDensity
import PerronWright.Transfer.QuantitativeStirling

/-! # Exact Stirling normalization of the local enumeration factors -/

open Filter Topology
open scoped Real Topology

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.CriticalStirlingNormalization

/-- Exact scalar conversion, with an arbitrary real power exponent. -/
theorem stirlingMain_rpow {k : ℕ} (hk : 0 < k) (p : ℝ) :
    (Transfer.factorialStirlingMainTerm k / Real.sqrt (2*Real.pi)) * (k : ℝ)^p =
      Real.exp (-(k : ℝ)) * (k : ℝ)^((k : ℝ)+p+1/2) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hpi : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
  have hsqrt : Real.sqrt (2*Real.pi*(k : ℝ)) / Real.sqrt (2*Real.pi) = Real.sqrt (k : ℝ) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2*Real.pi)]
    field_simp
  have hbase : ((k : ℝ)/Real.exp 1)^k = Real.exp (-(k : ℝ)) * (k : ℝ)^k := by
    rw [div_pow,Real.exp_one_pow,Real.exp_neg]
    ring
  unfold Transfer.factorialStirlingMainTerm
  calc
    (Real.sqrt (2*Real.pi*(k : ℝ))*((k : ℝ)/Real.exp 1)^k / Real.sqrt (2*Real.pi)) * (k : ℝ)^p =
        (Real.sqrt (2*Real.pi*(k : ℝ)) / Real.sqrt (2*Real.pi))*
          ((k : ℝ)/Real.exp 1)^k*(k : ℝ)^p := by ring
    _ = Real.exp (-(k : ℝ)) *
        (((k : ℝ)^(1/2 : ℝ) * (k : ℝ)^(k : ℝ)) * (k : ℝ)^p) := by
      rw [hsqrt,hbase,Real.sqrt_eq_rpow,← Real.rpow_natCast]
      ring
    _ = _ := by
      rw [← Real.rpow_add hkR,← Real.rpow_add hkR]
      congr 2
      ring

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The literal Gaussian enumeration main term is the Stirling factorial
main term times the actual local size factor and Gaussian rate. -/
theorem gaussianMain_eq_stirling_sizeFactor (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) {k : ℕ} (hk : 0 < k) (r : ℕ) (t : ℝ) :
    BoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm M hM k r t =
      Transfer.factorialStirlingMainTerm k * FactorialDensity.sizeFactor (M.beta hM) (k : ℝ) r *
        Real.exp (-CriticalWindowRadiusConversion.criticalQuadraticRate M hM * (k : ℝ)*(t-1)^2) := by
  have h := stirlingMain_rpow hk (3*(r : ℝ)/2-5/2)
  have he : (k : ℝ)+(3*(r : ℝ)/2-5/2)+1/2 = (k : ℝ)+3*(r : ℝ)/2-2 := by ring
  rw [he] at h
  unfold BoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm FactorialDensity.sizeFactor
  rw [show Transfer.factorialStirlingMainTerm k *
      (PerronWrightFormulaMainTerm.wrightConstant r * (M.beta hM)^(((r : ℝ)-1)/2) /
        Real.sqrt (2*Real.pi) * (k : ℝ)^(3*(r : ℝ)/2-5/2)) =
      (PerronWrightFormulaMainTerm.wrightConstant r * (M.beta hM)^(((r : ℝ)-1)/2)) *
        ((Transfer.factorialStirlingMainTerm k / Real.sqrt (2*Real.pi))*
          (k : ℝ)^(3*(r : ℝ)/2-5/2)) by ring,h]
  ring

/-- The true Stirling correction along any divergent component sizes. -/
theorem stirling_factorial_ratio_tendsto_one (k : ℕ → ℕ) (hk : Tendsto k atTop atTop) :
    Tendsto (fun m ↦ Transfer.factorialStirlingMainTerm (k m) / ((k m).factorial : ℝ))
      atTop (𝓝 1) := by
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have ht := (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hk).div_const (Real.sqrt Real.pi)
  rw [div_self hpi] at ht
  have hr : Tendsto (fun m ↦ ((k m).factorial : ℝ) / Transfer.factorialStirlingMainTerm (k m))
      atTop (𝓝 1) := by
    apply ht.congr'
    filter_upwards [hk.eventually (eventually_ge_atTop 1)] with m hm
    exact (Transfer.factorial_div_stirlingMainTerm_eq (k m) (by omega)).symm
  simpa only [inv_div,inv_one] using hr.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

/-- Actual connected weights divided by their actual factorials have
the literal size-factor Gaussian main term on the graph critical scale. -/
theorem connectedWeight_div_factorial_gaussian_ratio_tendsto_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R : ℕ) (N k r : ℕ → ℕ)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (hk : Tendsto k atTop atTop) (lambda b : ℝ) (hb : 0 ≤ b)
    (hsize : ∀ᶠ m in atTop, (k m : ℝ) ≤ b*(N m : ℝ)^(2/3 : ℝ))
    (hr : ∀ᶠ m in atTop, r m ≤ R) :
    Tendsto (fun m ↦ (M.connectedWeight (CriticalScaling.time lambda (N m)) (k m) (r m) /
      ((k m).factorial : ℝ)) /
      (FactorialDensity.sizeFactor (M.beta hM) (k m : ℝ) (r m) *
        Real.exp (-CriticalWindowRadiusConversion.criticalQuadraticRate M hM * (k m : ℝ)*
          (CriticalScaling.time lambda (N m)-1)^2))) atTop (𝓝 1) := by
  have he := CriticalConnectedEnumeration.gaussian_ratio_tendsto_one_critical_scale
    M hM R N k r hN hNt hk lambda b hb hsize hr
  have hs := stirling_factorial_ratio_tendsto_one k hk
  have h := he.mul hs
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [hk.eventually (eventually_ge_atTop 1)] with m hm
  have hkpos : 0 < k m := by omega
  have hkR : (0 : ℝ) < k m := Nat.cast_pos.mpr hkpos
  have hF : ((k m).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hS : Transfer.factorialStirlingMainTerm (k m) ≠ 0 := by
    unfold Transfer.factorialStirlingMainTerm
    positivity
  have hsizeFactor : FactorialDensity.sizeFactor (M.beta hM) (k m : ℝ) (r m) ≠ 0 :=
    (FactorialDensity.sizeFactor_pos (M.beta_pos hM) hkR _).ne'
  have hE : Real.exp (-CriticalWindowRadiusConversion.criticalQuadraticRate M hM * (k m : ℝ)*
      (CriticalScaling.time lambda (N m)-1)^2) ≠ 0 := (Real.exp_pos _).ne'
  rw [gaussianMain_eq_stirling_sizeFactor M hM hkpos]
  field_simp

end PerronWright.CriticalStirlingNormalization
