import PerronWright.Analysis.FiniteIrreducibleCriticalSimplicity

/-! The positive eigenvector of the constructed real critical pair is a genuine
Perron vector: every spectral value of its actual operator has modulus at most
one. Negative unit eigenvalues are deliberately not excluded. -/

open scoped Topology BigOperators ENNReal

noncomputable section

namespace PerronWright.FiniteIrreducibleCriticalPair

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem perturbed_norm_apply_le (M : FiniteIrreducibleModel S) (τ f : C(S, ℂ))
    (hτ : ∀ b, (τ b).im = 0) (hτpos : ∀ b, 0 ≤ (τ b).re) (a : S) :
    ‖perturbedOperator M τ f a‖ ≤
      ∑ b, (M.kernel a b * M.weight b * (τ b).re) * ‖f b‖ := by
  rw [perturbedOperator_apply, FiniteIrreducibleModel.complexOperator_apply]
  calc
    ‖∑ b, (M.kernel a b * M.weight b : ℝ) * (τ * f) b‖ ≤
        ∑ b, ‖(M.kernel a b * M.weight b : ℝ) * (τ * f) b‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      have he : τ b = ((τ b).re : ℂ) := by
        apply Complex.ext
        · rfl
        · simpa only [Complex.ofReal_im] using hτ b
      have hn : ‖τ b‖ = (τ b).re := by
        calc
          ‖τ b‖ = ‖((τ b).re : ℂ)‖ := congrArg norm he
          _ = (τ b).re := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hτpos b)]
      simp only [ContinuousMap.mul_apply, norm_mul, hn, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (M.kernel_nonneg a b),
        abs_of_nonneg (M.weight_pos b).le, mul_assoc]

theorem eigenvalue_norm_le_one_of_positive_fixed (M : FiniteIrreducibleModel S)
    (τ u : C(S, ℂ)) (hτ : ∀ b, (τ b).im = 0) (hτpos : ∀ b, 0 ≤ (τ b).re)
    (hu : ∀ b, (u b).im = 0) (hupos : ∀ b, 0 < (u b).re)
    (hfix : perturbedOperator M τ u = u) {lam : ℂ}
    (hev : Module.End.HasEigenvalue (perturbedOperator M τ).toLinearMap lam) : ‖lam‖ ≤ 1 := by
  let _ := M.nonempty
  obtain ⟨f, hf, hfne⟩ := hev.exists_hasEigenvector
  have heq : perturbedOperator M τ f = lam • f := Module.End.mem_eigenspace_iff.mp hf
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ
    (fun b ↦ ‖f b‖ / (u b).re) Finset.univ_nonempty
  have hbound (b : S) : ‖f b‖ ≤ (‖f a‖ / (u a).re) * (u b).re :=
    (div_le_iff₀ (hupos b)).mp (ha b (Finset.mem_univ b))
  have hfa : 0 < ‖f a‖ := by
    by_contra hh
    have hz : ‖f a‖ = 0 := le_antisymm (not_lt.mp hh) (norm_nonneg _)
    apply hfne
    ext b
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [hz, zero_div, zero_mul] using hbound b
  have hrow : (∑ b, M.kernel a b * M.weight b * (τ b).re * (u b).re) = (u a).re := by
    have he := congrArg (fun v : C(S, ℂ) ↦ (v a).re) hfix
    simp only [perturbedOperator_apply, FiniteIrreducibleModel.complexOperator_apply,
      ContinuousMap.mul_apply, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hτ, hu, mul_zero, zero_mul, sub_zero] at he
    simpa only [mul_assoc] using he
  have hn : ‖lam‖ * ‖f a‖ ≤ ‖f a‖ := by
    calc
      ‖lam‖ * ‖f a‖ = ‖perturbedOperator M τ f a‖ := by
        rw [heq]
        exact (norm_smul lam (f a)).symm
      _ ≤ ∑ b, (M.kernel a b * M.weight b * (τ b).re) * ‖f b‖ :=
        perturbed_norm_apply_le M τ f hτ hτpos a
      _ ≤ ∑ b, (M.kernel a b * M.weight b * (τ b).re) *
          ((‖f a‖ / (u a).re) * (u b).re) := by
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left (hbound b)
          (mul_nonneg (mul_nonneg (M.kernel_nonneg a b) (M.weight_pos b).le) (hτpos b))
      _ = (‖f a‖ / (u a).re) * (u a).re := by
        rw [← hrow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = ‖f a‖ := div_mul_cancel₀ _ (hupos a).ne'
  nlinarith

theorem spectrum_norm_le_one_of_positive_fixed (M : FiniteIrreducibleModel S)
    (τ u : C(S, ℂ)) (hτ : ∀ b, (τ b).im = 0) (hτpos : ∀ b, 0 ≤ (τ b).re)
    (hu : ∀ b, (u b).im = 0) (hupos : ∀ b, 0 < (u b).re)
    (hfix : perturbedOperator M τ u = u) {lam : ℂ}
    (hlam : lam ∈ spectrum ℂ (perturbedOperator M τ)) : ‖lam‖ ≤ 1 := by
  by_cases hz : lam = 0
  · simp [hz]
  have hk : IsCompactOperator (perturbedOperator M τ) :=
    (M.continuousKernel.isCompactOperator_complexActionCLM M.measure).comp_clm
      (ContinuousLinearMap.mul ℂ C(S, ℂ) τ)
  exact eigenvalue_norm_le_one_of_positive_fixed M τ u hτ hτpos hu hupos hfix
    ((hk.hasEigenvalue_iff_mem_spectrum hz).mpr hlam)

theorem criticalPair_spectrum_norm_le_one (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ∀ᶠ g in 𝓝 (0 : C(S, ℂ)), star g = g →
      ∀ lam ∈ spectrum ℂ (perturbedOperator M (criticalPair M hcrit g).2), ‖lam‖ ≤ 1 := by
  have hs := Classical.choose_spec (criticalPair_germ M hcrit)
  rw [← criticalPair] at hs
  have ht : Filter.Tendsto (fun g ↦ (criticalPair M hcrit g).2) (𝓝 0) (𝓝 1) := by
    simpa only [hs.2.1] using hs.1.continuousAt.snd.tendsto
  filter_upwards [criticalPair_real_positive M hcrit,
    criticalPair_positive_simple_one M hcrit, ht.eventually (eigenpair_equations M hcrit),
    hs.2.2.1] with g hp hu he hg
  intro hreal lam hlam
  have hτ := (hp hreal).2.2
  have huv := (hu hreal).1
  apply spectrum_norm_le_one_of_positive_fixed M (criticalPair M hcrit g).2
    (eigenvector M hcrit (criticalPair M hcrit g).2)
    (fun b ↦ (hτ b).1) (fun b ↦ (hτ b).2.le)
    (fun b ↦ (huv b).1) (fun b ↦ (huv b).2) _ hlam
  simpa only [perturbedOperator_apply, hg.2, one_smul] using he.1

/-- The spectral radius of the actual real critical operator is exactly one,
not merely the eigenvalue of a chosen analytic branch. -/
theorem criticalPair_spectralRadius_eq_one (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ∀ᶠ g in 𝓝 (0 : C(S, ℂ)), star g = g →
      spectralRadius ℂ (perturbedOperator M (criticalPair M hcrit g).2) = 1 := by
  have hs := Classical.choose_spec (criticalPair_germ M hcrit)
  rw [← criticalPair] at hs
  have ht : Filter.Tendsto (fun g ↦ (criticalPair M hcrit g).2) (𝓝 0) (𝓝 1) := by
    simpa only [hs.2.1] using hs.1.continuousAt.snd.tendsto
  filter_upwards [criticalPair_spectrum_norm_le_one M hcrit, criticalPair_simple_one M hcrit,
    ht.eventually (eigenpair_equations M hcrit), hs.2.2.1] with g hb hsimp he hg
  intro hreal
  apply le_antisymm
  · apply iSup₂_le
    intro lam hlam
    have hn := hb hreal lam hlam
    exact_mod_cast hn
  · have hfix : perturbedOperator M (criticalPair M hcrit g).2
        (eigenvector M hcrit (criticalPair M hcrit g).2) =
          (1 : ℂ) • eigenvector M hcrit (criticalPair M hcrit g).2 := by
      simpa only [perturbedOperator_apply, hg.2] using he.1
    have hev := Module.End.hasEigenvalue_of_hasEigenvector
      (show Module.End.HasEigenvector
        (perturbedOperator M (criticalPair M hcrit g).2).toLinearMap 1
        (eigenvector M hcrit (criticalPair M hcrit g).2) from
          ⟨Module.End.mem_eigenspace_iff.mpr hfix, hsimp.1⟩)
    have hmem : (1 : ℂ) ∈ spectrum ℂ (perturbedOperator M (criticalPair M hcrit g).2) := by
      rw [ContinuousLinearMap.spectrum_eq]
      exact hev.mem_spectrum
    have hl : (‖(1 : ℂ)‖₊ : ℝ≥0∞) ≤
        spectralRadius ℂ (perturbedOperator M (criticalPair M hcrit g).2) :=
      le_iSup_of_le (1 : ℂ) (le_iSup_of_le hmem (le_refl
        (‖(1 : ℂ)‖₊ : ℝ≥0∞)))
    simpa only [nnnorm_one, ENNReal.coe_one] using hl

end PerronWright.FiniteIrreducibleCriticalPair
