import PerronWright.Probability.CountableFixedSupportTVLocal
import PerronWright.Probability.CountablePerronMarkConvergence

/-! # Actual fixed reference truncations approach the countable model

The normalized retained weights have exactly twice the discarded mass
as their full atomic absolute error. The reference spectral roots,
quadratic/cubic Perron scales and actual TV marks therefore converge by
the already proved weighted-operator and Perron approximation theorems.
No diagonal graph law or point-process convergence is asserted here.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open GrowingTypeCounts
open CountableTypeRealization (weights)

theorem fixedSupportWeights_variation_eq (M : CountableKernel) (m : ℕ) :
    (∑' a : ℕ, |M.fixedSupportWeights m a - M.mu.real {a}|) =
      2 * (1 - mass (weights M) m) := by
  have he := ((M.fixedSupportWeights_hasSum m).summable.sub
    M.atomMass_hasSum.summable).abs.sum_add_tsum_nat_add (m + 1)
  have ht := M.atomMass_hasSum.summable.sum_add_tsum_nat_add (m + 1)
  rw [M.atomMass_hasSum.tsum_eq, ← mass_eq_sum_range] at ht
  change mass (weights M) m + (∑' a : ℕ, M.mu.real {a + (m + 1)}) = 1 at ht
  have htail : (∑' a : ℕ,
      |M.fixedSupportWeights m (a + (m + 1)) - M.mu.real {a + (m + 1)}|) =
      1 - mass (weights M) m := by
    have hz (a : ℕ) : M.fixedSupportWeights m (a + (m + 1)) = 0 :=
      M.fixedSupportWeights_zero m _ (by simp only [Finset.mem_range]; omega)
    simp_rw [hz, zero_sub, abs_neg, abs_of_pos (M.atomMass_pos _)]
    linarith
  rw [htail, ← Fin.sum_univ_eq_sum_range] at he
  simp only [M.fixedSupportWeights_fin] at he
  have hin := truncation_error_eq (weights M) M.atomMass_pos M.atomMass_hasSum m
  change (∑ a : Fin (m + 1), |truncatedLaw (weights M) m a - M.mu.real {(a : ℕ)}|) =
    1 - mass (weights M) m at hin
  rw [hin] at he
  linarith

theorem fixedSupportWeights_variation_tendsto (M : CountableKernel) :
    Tendsto (fun m ↦ ∑' a : ℕ, |M.fixedSupportWeights m a - M.mu.real {a}|)
      atTop (𝓝 0) := by
  simp_rw [M.fixedSupportWeights_variation_eq]
  simpa only [sub_self, mul_zero] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
      (mass_tendsto_one (weights M) M.atomMass_hasSum)).const_mul 2

theorem fixedSupportSpectralRadius_tendsto_one (M : CountableKernel) (hM : M.IsCritical) :
    Tendsto (M.fixedSupportSpectralRadius) atTop (𝓝 1) :=
  M.weightedSpectralRadius_tendsto_one hM (M.fixedSupportWeights)
    (M.fixedSupportWeights_nonneg) (M.fixedSupportWeights_hasSum)
    M.fixedSupportWeights_variation_tendsto

theorem fixedSupportModel_alpha_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    Tendsto (fun m ↦ (M.fixedSupportModel m hlower hlo).alpha
      (M.fixedSupportModel_isCritical m hlower hlo)) atTop (𝓝 (M.alpha hM)) := by
  have ht := M.finitePerronAlpha_tendsto hM (M.fixedSupportWeights)
    (M.fixedSupportWeights_nonneg) (M.fixedSupportWeights_hasSum)
    (fun m ↦ Finset.range (m + 1)) (M.fixedSupportWeights_zero) hlower hlo
    M.fixedSupportWeights_variation_tendsto
  simpa only [fixedSupportModel, M.finiteCriticalModel_alpha] using ht

theorem fixedSupportModel_beta_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    Tendsto (fun m ↦ (M.fixedSupportModel m hlower hlo).beta
      (M.fixedSupportModel_isCritical m hlower hlo)) atTop (𝓝 (M.beta hM)) := by
  have ht := M.finitePerronBeta_tendsto hM (M.fixedSupportWeights)
    (M.fixedSupportWeights_nonneg) (M.fixedSupportWeights_hasSum)
    (fun m ↦ Finset.range (m + 1)) (M.fixedSupportWeights_zero) hlower hlo
    M.fixedSupportWeights_variation_tendsto
  simpa only [fixedSupportModel, M.finiteCriticalModel_beta] using ht

theorem fixedSupportPerronMark_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    Tendsto (fun m ↦ M.fixedSupportPerronMark m hlower hlo) atTop
      (𝓝 (CountablePerronMarkConvergence.perronMark M hM)) := by
  apply (CountableVariationMarks.tendsto_iff_atomic_variation _ _).mpr
  simp only [M.fixedSupportPerronMark_measure, CountablePerronMarkConvergence.perronMark,
    CountableVariationMarks.ofProbability]
  exact M.finitePerronLaw_atomic_variation_tendsto hM (M.fixedSupportWeights)
    (M.fixedSupportWeights_nonneg) (M.fixedSupportWeights_hasSum)
    (fun m ↦ Finset.range (m + 1)) (M.fixedSupportWeights_zero) hlower hlo
    M.fixedSupportWeights_variation_tendsto

theorem fixedSupportPerronMark_joint_test_tendsto (M : CountableKernel)
    (hM : M.IsRegularCritical) {q : ℕ}
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (Ψ : (Fin q → CountableVariationMarks.VariationMark) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun m ↦ Ψ (fun _ ↦ M.fixedSupportPerronMark m hlower hlo)) atTop
      (𝓝 (Ψ (fun _ ↦ CountablePerronMarkConvergence.perronMark M hM))) :=
  hΨ.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr (fun _ ↦ M.fixedSupportPerronMark_tendsto hM hlower hlo))

/-- The retained limiting densities are the literal formulas and
converge to the countable Perron formula as the support is exhausted. -/
theorem fixedSupport_density_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    {q : ℕ} (lambda : ℝ) (y : Fin q → ℝ) (r : Fin q → ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    Tendsto (fun m ↦ FactorialDensity.density
      ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
      ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
      lambda y r) atTop (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r)) := by
  have hα := M.fixedSupportModel_alpha_tendsto hM hlower hlo
  have hβ := M.fixedSupportModel_beta_tendsto hM hlower hlo
  have hb : M.beta hM ≠ 0 := (M.beta_pos hM).ne'
  have hc := (((hβ.mul_const ((∑ i, y i) ^ 3)).div_const 6).sub
    (((hα.mul_const lambda).mul_const ((∑ i, y i) ^ 2)).div_const 2)).add
    ((((hα.pow 2).mul_const (lambda ^ 2)).mul_const (∑ i, y i)).div
      (hβ.const_mul 2) (mul_ne_zero (by norm_num) hb))
  change Tendsto (fun m ↦ FactorialDensity.criticalExponent
    ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
    ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
    lambda (∑ i, y i)) atTop
      (𝓝 (FactorialDensity.criticalExponent (M.alpha hM) (M.beta hM) lambda (∑ i, y i))) at hc
  have hp := tendsto_finsetProd Finset.univ (fun i _ ↦ by
    have hi := (((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦
      PerronWrightFormulaMainTerm.wrightConstant (r i)) atTop
      (𝓝 (PerronWrightFormulaMainTerm.wrightConstant (r i)))).mul
      (hβ.rpow_const (p := ((r i : ℝ) - 1) / 2) (Or.inl hb))).div_const
        (Real.sqrt (2 * Real.pi))).mul_const (y i ^ (3 * (r i : ℝ) / 2 - 5 / 2))
    exact hi)
  have he := Real.continuous_exp.continuousAt.tendsto.comp hc.neg
  exact he.mul hp

theorem fixedSupport_marked_density_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    {q : ℕ} (lambda : ℝ) (y : Fin q → ℝ) (r : Fin q → ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (Ψ : (Fin q → CountableVariationMarks.VariationMark) → ℝ) (hΨ : Continuous Ψ) :
    Tendsto (fun m ↦ FactorialDensity.density
      ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
      ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
      lambda y r * Ψ (fun _ ↦ M.fixedSupportPerronMark m hlower hlo)) atTop
      (𝓝 (FactorialDensity.density (M.alpha hM) (M.beta hM) lambda y r *
        Ψ (fun _ ↦ CountablePerronMarkConvergence.perronMark M hM))) :=
  (M.fixedSupport_density_tendsto hM lambda y r hlower hlo).mul
    (M.fixedSupportPerronMark_joint_test_tendsto hM hlower hlo Ψ hΨ)

end PerronWright.CountableKernel
