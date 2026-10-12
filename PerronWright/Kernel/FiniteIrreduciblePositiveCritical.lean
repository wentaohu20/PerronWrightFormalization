import PerronWright.Model.FiniteIrreduciblePerronQuantities

/-!
# Literal criticality from an actual positive fixed vector

The positive fixed vector is used to prove a spectral bound by a finite
maximum-ratio argument. No spectral conclusion is stored as model data,
and negative unit eigenvalues are allowed.
-/

open scoped BigOperators Topology ENNReal
noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem eigenvalue_norm_le_one_of_positive_fixed_hilbert
    (M : FiniteIrreducibleModel S) (u : M.Hilbert)
    (hu : ∀ a, 0 < u a) (hfix : M.operator u = u)
    {lam : ℝ} (hev : Module.End.HasEigenvalue M.operator.toLinearMap lam) :
    ‖lam‖ ≤ 1 := by
  let _ := M.nonempty
  obtain ⟨f, hf, hfne⟩ := hev.exists_hasEigenvector
  have heq : M.operator f = lam • f := Module.End.mem_eigenspace_iff.mp hf
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ
    (fun b ↦ ‖f b‖ / u b) Finset.univ_nonempty
  have hbound (b : S) : ‖f b‖ ≤ (‖f a‖ / u a) * u b :=
    (div_le_iff₀ (hu b)).mp (ha b (Finset.mem_univ b))
  have hfa : 0 < ‖f a‖ := by
    by_contra hh
    have hz : ‖f a‖ = 0 := le_antisymm (not_lt.mp hh) (norm_nonneg _)
    apply hfne
    apply (WithLp.ext_iff 2).mpr
    funext b
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [hz, zero_div, zero_mul] using hbound b
  have hrow : (∑ b, M.symmetricMatrix a b * u b) = u a :=
    congrArg (fun v : M.Hilbert ↦ v a) hfix
  have hn : ‖lam‖ * ‖f a‖ ≤ ‖f a‖ := by
    calc
      ‖lam‖ * ‖f a‖ = ‖M.operator f a‖ := by
        rw [heq]
        exact (norm_smul lam (f a)).symm
      _ ≤ ∑ b, ‖M.symmetricMatrix a b * f b‖ := by
        rw [M.operator_apply]
        exact norm_sum_le _ _
      _ = ∑ b, M.symmetricMatrix a b * ‖f b‖ := by
        apply Finset.sum_congr rfl
        intro b _
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (M.symmetricMatrix_nonneg a b)]
      _ ≤ ∑ b, M.symmetricMatrix a b * ((‖f a‖ / u a) * u b) := by
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left (hbound b) (M.symmetricMatrix_nonneg a b)
      _ = (‖f a‖ / u a) * u a := by
        rw [← hrow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = ‖f a‖ := div_mul_cancel₀ _ (hu a).ne'
  nlinarith

theorem isCritical_of_positive_fixed_hilbert (M : FiniteIrreducibleModel S)
    (u : M.Hilbert) (hu : ∀ a, 0 < u a) (hfix : M.operator u = u) :
    M.IsCritical := by
  have hune : u ≠ 0 := by
    intro hz
    let a := Classical.choice M.nonempty
    have hp := hu a
    rw [hz] at hp
    simp at hp
  have hev : Module.End.HasEigenvalue M.operator.toLinearMap (1 : ℝ) :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hfix), hune⟩
  have hmem : (1 : ℝ) ∈ spectrum ℝ M.operator := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact hev.mem_spectrum
  change spectralRadius ℝ M.meanMatrix = 1
  rw [← M.spectralRadius_operator]
  apply le_antisymm
  · apply iSup₂_le
    intro lam hlam
    have hn : ‖lam‖ ≤ 1 := by
      by_cases hz : lam = 0
      · simp [hz]
      exact M.eigenvalue_norm_le_one_of_positive_fixed_hilbert u hu hfix
        ((M.isCompactOperator_operator.hasEigenvalue_iff_mem_spectrum hz).mpr hlam)
    exact_mod_cast hn
  · have hl : (‖(1 : ℝ)‖₊ : ℝ≥0∞) ≤ spectralRadius ℝ M.operator :=
      le_iSup_of_le (1 : ℝ) (le_iSup_of_le hmem (le_refl _))
    simpa only [nnnorm_one, ENNReal.coe_one] using hl

theorem isCritical_of_positive_fixed_function (M : FiniteIrreducibleModel S)
    (u : S → ℝ) (hu : ∀ a, 0 < u a) (hfix : M.action u = u) :
    M.IsCritical := by
  apply M.isCritical_of_positive_fixed_hilbert (M.toHilbert u)
  · intro a
    exact mul_pos (M.sqrtWeight_pos a) (hu a)
  · rw [M.toHilbert_intertwines, hfix]

end PerronWright.FiniteIrreducibleModel
