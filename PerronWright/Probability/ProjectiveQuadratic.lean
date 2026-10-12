import PerronWright.Probability.ProjectiveKernel
import PerronWright.Probability.EmpiricalTypeMarks
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# The actual centered projective quadratic statistic

The double integral against an empirical law minus the Perron law is
defined by its four ordinary product-measure integrals.  Its feature-square
expansion is proved by applying a continuous linear functional to the
absolutely convergent kernel series.  This is a deterministic identity;
the scale-matched exponential moment estimate is not assumed here.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.ProjectiveKernel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private def integralCLM (mu : Measure S) [IsFiniteMeasure mu] : C(S, ℝ) →L[ℝ] ℝ :=
  (MeasureTheory.L1.integralCLM' (α := S) (E := ℝ) (μ := mu) ℝ).comp
    (ContinuousMap.toLp 1 mu ℝ)

private theorem integralCLM_apply (mu : Measure S) [IsFiniteMeasure mu]
    (f : C(S, ℝ)) : integralCLM mu f = ∫ x, f x ∂mu := by
  unfold integralCLM
  rw [ContinuousLinearMap.comp_apply, ← MeasureTheory.L1.integral_eq' ℝ,
    MeasureTheory.L1.integral_eq_integral]
  apply integral_congr_ae
  exact ContinuousMap.coeFn_toLp (p := 1) (μ := mu) (𝕜 := ℝ) f

/-- Integration against `(mu-nu)⊗(mu-nu)`, without postulating a signed
measure integration API. -/
def centeredQuadraticCLM (mu nu : Measure S)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] : C(S × S, ℝ) →L[ℝ] ℝ :=
  integralCLM (mu.prod mu) - integralCLM (mu.prod nu) -
    integralCLM (nu.prod mu) + integralCLM (nu.prod nu)

theorem centeredQuadraticCLM_apply (mu nu : Measure S)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (H : C(S × S, ℝ)) :
    centeredQuadraticCLM mu nu H =
      (∫ z, H z ∂mu.prod mu) - (∫ z, H z ∂mu.prod nu) -
        (∫ z, H z ∂nu.prod mu) + (∫ z, H z ∂nu.prod nu) := by
  simp only [centeredQuadraticCLM, add_apply, sub_apply, integralCLM_apply]

/-- Rank-one feature kernels give exactly squared centered linear tests. -/
theorem centeredQuadraticCLM_square (mu nu : Measure S)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (f : C(S, ℝ)) :
    centeredQuadraticCLM mu nu (square f) =
      ((∫ x, f x ∂mu) - (∫ x, f x ∂nu)) ^ 2 := by
  rw [centeredQuadraticCLM_apply]
  change (∫ z : S × S, f z.1 * f z.2 ∂mu.prod mu) -
    (∫ z : S × S, f z.1 * f z.2 ∂mu.prod nu) -
    (∫ z : S × S, f z.1 * f z.2 ∂nu.prod mu) +
    (∫ z : S × S, f z.1 * f z.2 ∂nu.prod nu) = _
  simp_rw [integral_prod_mul]
  ring

omit [BorelSpace S] in
theorem norm_centered_test_le (mu nu : Measure S)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (f : C(S, ℝ)) :
    ‖(∫ x, f x ∂mu) - (∫ x, f x ∂nu)‖ ≤ 2 * ‖f‖ := by
  have h (rho : Measure S) [IsProbabilityMeasure rho] :
      ‖∫ x, f x ∂rho‖ ≤ ‖f‖ := by
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := rho)
        (Filter.Eventually.of_forall (fun x ↦ f.norm_coe_le_norm x))
  calc
    _ ≤ ‖∫ x, f x ∂mu‖ + ‖∫ x, f x ∂nu‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (h mu) (h nu)
    _ = _ := by ring

omit [BorelSpace S] in
theorem norm_feature_quadratic_le (mu nu : Measure S)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (a : ℝ) (f : C(S, ℝ)) :
    ‖a * ((∫ x, f x ∂mu) - (∫ x, f x ∂nu)) ^ 2‖ ≤
      4 * (|a| * ‖f‖ ^ 2) := by
  have hb := norm_centered_test_le mu nu f
  rw [norm_mul, norm_pow, Real.norm_eq_abs]
  have hsq : ‖(∫ x, f x ∂mu) - (∫ x, f x ∂nu)‖ ^ 2 ≤ (2 * ‖f‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc
    _ ≤ |a| * (2 * ‖f‖) ^ 2 := mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
    _ = _ := by ring

omit [BorelSpace S] in
/-- Summability of the centered feature squares follows from the literal
projective majorant, not from a separate quadratic-control interface. -/
theorem summable_feature_quadratics (mu nu : Measure S)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (h : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) :
    Summable (fun j ↦ a j *
      ((∫ x, f j x ∂mu) - (∫ x, f j x ∂nu)) ^ 2) :=
  (h.mul_left 4).of_norm_bounded (fun j ↦ norm_feature_quadratic_le mu nu (a j) (f j))

/-- The kernel double integral equals the absolutely convergent feature
square series, including for the actual empirical and Perron measures. -/
theorem centeredQuadratic_eq_tsum (mu nu : Measure S)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (h : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) :
    centeredQuadraticCLM mu nu (∑' j, (a j) • square (f j)) =
      ∑' j, a j * ((∫ x, f j x ∂mu) - (∫ x, f j x ∂nu)) ^ 2 := by
  have hs := (centeredQuadraticCLM mu nu).hasSum (summable_terms h).hasSum
  simp only [map_smul, smul_eq_mul, centeredQuadraticCLM_square] at hs
  exact hs.tsum_eq.symm

theorem norm_centeredQuadratic_le (mu nu : Measure S)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (h : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) :
    ‖centeredQuadraticCLM mu nu (∑' j, (a j) • square (f j))‖ ≤
      4 * ∑' j, |a j| * ‖f j‖ ^ 2 := by
  rw [centeredQuadratic_eq_tsum mu nu h]
  have hn := (h.mul_left 4).of_nonneg_of_le
    (fun j ↦ norm_nonneg _) (fun j ↦ norm_feature_quadratic_le mu nu (a j) (f j))
  calc
    _ ≤ ∑' j, ‖a j * ((∫ x, f j x ∂mu) - (∫ x, f j x ∂nu)) ^ 2‖ :=
      norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j, 4 * (|a j| * ‖f j‖ ^ 2) :=
      hn.tsum_le_tsum (fun j ↦ norm_feature_quadratic_le mu nu (a j) (f j)) (h.mul_left 4)
    _ = _ := h.tsum_mul_left 4

/-- The paper's centered empirical quadratic statistic on a nonempty
selected vertex set, centered at the genuine Perron probability law. -/
def empiricalQuadratic (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (x : Fin n → S) (B : Finset (Fin n)) (hB : B.Nonempty)
    (H : C(S × S, ℝ)) : ℝ := by
  letI := EmpiricalTypeMarks.empiricalMeasure_isProbability x B hB
  exact (B.card : ℝ) * centeredQuadraticCLM
    (EmpiricalTypeMarks.empiricalMeasure x B) (M.perronLaw hM) H

/-- The empirical statistic's exact feature-square representation. -/
theorem empiricalQuadratic_eq_tsum (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (x : Fin n → S) (B : Finset (Fin n)) (hB : B.Nonempty)
    {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (h : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) :
    empiricalQuadratic M hM x B hB (∑' j, (a j) • square (f j)) =
      (B.card : ℝ) * ∑' j, a j *
        ((B.card : ℝ)⁻¹ * ∑ v ∈ B, f j (x v) - ∫ y, f j y ∂M.perronLaw hM) ^ 2 := by
  let _ := EmpiricalTypeMarks.empiricalMeasure_isProbability x B hB
  unfold empiricalQuadratic
  rw [centeredQuadratic_eq_tsum _ _ h]
  simp_rw [EmpiricalTypeMarks.empiricalMeasure_integral]

end PerronWright.ProjectiveKernel
