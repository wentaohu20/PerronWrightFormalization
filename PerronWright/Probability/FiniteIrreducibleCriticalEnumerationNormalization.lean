import PerronWright.Analysis.FiniteIrreduciblePerronWrightTerminal
import PerronWright.Probability.CriticalStirlingNormalization

/-!
# Actual finite irreducible factorial-divided Gaussian enumeration

Only the genuine finite irreducible enumeration terminal is used for the
model-dependent asymptotics. The generic proved Stirling identity and
Stirling convergence supply the literal factorial normalization.
-/

open Filter Topology
open scoped Real Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleCriticalEnumerationNormalization

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem gaussianMain_eq_stirling_sizeFactor (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) {k : ℕ} (hk : 0 < k) (r : ℕ) (t : ℝ) :
    FiniteIrreducibleBoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm M hM k r t =
      Transfer.factorialStirlingMainTerm k * FactorialDensity.sizeFactor (M.beta hM) (k : ℝ) r *
        Real.exp (-FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
          (k : ℝ) * (t-1)^2) := by
  have h := CriticalStirlingNormalization.stirlingMain_rpow hk (3*(r : ℝ)/2-5/2)
  have he : (k : ℝ)+(3*(r : ℝ)/2-5/2)+1/2 = (k : ℝ)+3*(r : ℝ)/2-2 := by ring
  rw [he] at h
  unfold FiniteIrreducibleBoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm
    FactorialDensity.sizeFactor
  rw [show Transfer.factorialStirlingMainTerm k *
      (PerronWrightFormulaMainTerm.wrightConstant r * (M.beta hM)^(((r : ℝ)-1)/2) /
        Real.sqrt (2*Real.pi) * (k : ℝ)^(3*(r : ℝ)/2-5/2)) =
      (PerronWrightFormulaMainTerm.wrightConstant r * (M.beta hM)^(((r : ℝ)-1)/2)) *
        ((Transfer.factorialStirlingMainTerm k / Real.sqrt (2*Real.pi)) *
          (k : ℝ)^(3*(r : ℝ)/2-5/2)) by ring, h]
  rw [FiniteIrreduciblePerronWrightFormulaMainTerm.wrightConstant_eq_classical]
  ring

theorem factorial_divided_ratio_identity (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) {k : ℕ} (hk : 0 < k) (r : ℕ) (t : ℝ) :
    (M.bjrModel.connectedWeight t k r / (k.factorial : ℝ)) /
      (FactorialDensity.sizeFactor (M.beta hM) (k : ℝ) r *
        Real.exp (-FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
          (k : ℝ) * (t-1)^2)) =
      (M.bjrModel.connectedWeight t k r /
        FiniteIrreducibleBoundedSurplusPerronWrightFormula.perronWrightGaussianMainTerm M hM k r t) *
        (Transfer.factorialStirlingMainTerm k / (k.factorial : ℝ)) := by
  have hF : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hS : Transfer.factorialStirlingMainTerm k ≠ 0 := by
    unfold Transfer.factorialStirlingMainTerm
    have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    positivity
  have hSF := (FactorialDensity.sizeFactor_pos (M.beta_pos hM) (Nat.cast_pos.mpr hk) r).ne'
  have hE := (Real.exp_pos (-FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
    (k : ℝ) * (t-1)^2)).ne'
  rw [gaussianMain_eq_stirling_sizeFactor M hM hk]
  field_simp

/-- True factorial-divided enumeration has a common threshold for every
bounded surplus and every scalar intensity in the square-root window. -/
theorem eventually_uniform_factorial_divided_gaussian_ratio
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (R : ℕ) (L : ℝ) (hL : 0 ≤ L) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ r : ℕ, r ≤ R → ∀ t : ℝ,
      Real.sqrt (k : ℝ) * |t-1| ≤ L →
      |(M.bjrModel.connectedWeight t k r / (k.factorial : ℝ)) /
        (FactorialDensity.sizeFactor (M.beta hM) (k : ℝ) r *
          Real.exp (-FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
            (k : ℝ) * (t-1)^2)) - 1| ≤ ε := by
  let δ : ℝ := min 1 (ε / 3)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by norm_num))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : 3 * δ ≤ ε := by have := min_le_right (1 : ℝ) (ε/3); dsimp only [δ]; linarith
  obtain ⟨C, _hC, hbound⟩ :=
    FiniteIrreduciblePerronWrightTerminal.Main.exists_boundedSurplusPerronWright_gaussian_relative_bound
      M hM R L hL
  have hzero : Tendsto (fun k : ℕ ↦ C / Real.sqrt (k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul C
  have hsmall := hzero.eventually (Iio_mem_nhds hδ)
  have hstirling := (CriticalStirlingNormalization.stirling_factorial_ratio_tendsto_one
    (fun k : ℕ ↦ k) tendsto_id).eventually (Metric.ball_mem_nhds 1 hδ)
  filter_upwards [hbound, hsmall, hstirling, eventually_ge_atTop (1 : ℕ)]
    with k hk hks hkt hk1
  intro r hr t ht
  rw [factorial_divided_ratio_identity M hM (by omega)]
  have hs : |Transfer.factorialStirlingMainTerm k / (k.factorial : ℝ) - 1| ≤ δ := by
    exact (show |Transfer.factorialStirlingMainTerm k / (k.factorial : ℝ) - 1| < δ by
      simpa only [Metric.mem_ball, Real.dist_eq] using hkt).le
  have he := (hk r hr t ht).trans hks.le
  exact (RelativeErrorProduct.abs_two_factor_sub_one_le hδ.le hδ1
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa using he) (by simpa using hs)).trans (by nlinarith [hδε])

end PerronWright.FiniteIrreducibleCriticalEnumerationNormalization

