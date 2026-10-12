import PerronWright.Kernel.CountableCompact
import PerronWright.Kernel.CountablePositive
import PerronWright.Analysis.CompactSymmetric

/-!
# Criticality and positive fixed vectors for the actual countable operator

Criticality refers to the spectral radius of the constructed operator.
It is not a field containing an eigenvector or a spectral conclusion.
-/

open MeasureTheory Module
open scoped ENNReal NNReal

noncomputable section

namespace PerronWright.CountableKernel

def IsCritical (M : CountableKernel) : Prop := spectralRadius ℝ M.actionCLM = 1

theorem norm_eq_one_of_critical (M : CountableKernel) (hcrit : M.IsCritical) :
    ‖M.actionCLM‖ = 1 := by
  change spectralRadius ℝ M.actionCLM = 1 at hcrit
  cases subsingleton_or_nontrivial M.L2 with
  | inl h =>
    let _ := h
    have hz : M.actionCLM = 0 := Subsingleton.elim _ _
    simp [hz] at hcrit
  | inr h =>
    let _ := h
    have hrad : (‖M.actionCLM‖₊ : ℝ≥0∞) ≤ spectralRadius ℝ M.actionCLM := by
      rcases PerronWright.norm_or_neg_norm_mem_spectrum M.actionCLM M.isSymmetric_actionCLM
        with hp | hn
      · have he : (‖(‖M.actionCLM‖ : ℝ)‖₊ : ℝ≥0∞) ≤ spectralRadius ℝ M.actionCLM := by
          unfold spectralRadius
          exact le_iSup_of_le (‖M.actionCLM‖ : ℝ) (le_iSup_of_le hp (le_refl _))
        have hn : ‖(‖M.actionCLM‖ : ℝ)‖₊ = ‖M.actionCLM‖₊ := by
          apply NNReal.eq
          simp only [coe_nnnorm, Real.norm_of_nonneg (norm_nonneg _)]
        simpa only [hn] using he
      · have he : (‖(-‖M.actionCLM‖ : ℝ)‖₊ : ℝ≥0∞) ≤ spectralRadius ℝ M.actionCLM := by
          unfold spectralRadius
          exact le_iSup_of_le (-‖M.actionCLM‖ : ℝ) (le_iSup_of_le hn (le_refl _))
        have heq : ‖(-‖M.actionCLM‖ : ℝ)‖₊ = ‖M.actionCLM‖₊ := by
          apply NNReal.eq
          simp only [coe_nnnorm, norm_neg, Real.norm_of_nonneg (norm_nonneg _)]
        simpa only [heq] using he
    have heq : (‖M.actionCLM‖₊ : ℝ≥0∞) = 1 := by
      apply le_antisymm
      · simpa [IsCritical] using hrad.trans_eq hcrit
      · simpa [IsCritical, hcrit] using (spectrum.spectralRadius_le_nnnorm (𝕜 := ℝ) M.actionCLM)
    have hn : ‖M.actionCLM‖₊ = (1 : ℝ≥0) := by exact_mod_cast heq
    simpa using congrArg (fun t : ℝ≥0 ↦ (t : ℝ)) hn

def absVector (M : CountableKernel) (v : M.L2) : M.L2 :=
  (Lp.memLp v).norm.toLp (fun a ↦ ‖v a‖)

theorem absVector_apply (M : CountableKernel) (v : M.L2) (a : ℕ) :
    M.absVector v a = |v a| := by
  exact (M.forall_of_ae (Lp.memLp v).norm.coeFn_toLp a).trans (Real.norm_eq_abs _)

theorem norm_absVector (M : CountableKernel) (v : M.L2) : ‖M.absVector v‖ = ‖v‖ := by
  rw [absVector, Lp.norm_toLp, eLpNorm_norm, Lp.norm_def]

theorem norm_sq_eq_integral (M : CountableKernel) (v : M.L2) :
    ‖v‖ ^ 2 = ∫ a, (v a) ^ 2 ∂M.mu := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [pow_two]

theorem eq_of_nonneg_le_of_norm_le (M : CountableKernel) (v w : M.L2)
    (hv : ∀ a, 0 ≤ v a) (hvw : ∀ a, v a ≤ w a) (hnorm : ‖w‖ ≤ ‖v‖) : v = w := by
  have hvi := (Lp.memLp v).integrable_sq
  have hwi := (Lp.memLp w).integrable_sq
  have hsq : ∀ a, (v a) ^ 2 ≤ (w a) ^ 2 := fun a ↦
    (sq_le_sq₀ (hv a) ((hv a).trans (hvw a))).mpr (hvw a)
  have hnormsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
  rw [M.norm_sq_eq_integral w, M.norm_sq_eq_integral v] at hnormsq
  have hi : (∫ a, (v a) ^ 2 ∂M.mu) = ∫ a, (w a) ^ 2 ∂M.mu :=
    le_antisymm (integral_mono hvi hwi hsq) hnormsq
  have hae := (integral_eq_iff_of_ae_le hvi hwi (Filter.Eventually.of_forall hsq)).mp hi
  apply Lp.ext
  filter_upwards [hae] with a ha
  exact (sq_eq_sq₀ (hv a) ((hv a).trans (hvw a))).mp ha

theorem abs_action_le (M : CountableKernel) (v : M.L2) (a : ℕ) :
    |M.actionCLM v a| ≤ M.actionCLM (M.absVector v) a := by
  rw [M.actionCLM_apply_integral, M.actionCLM_apply_integral]
  calc
    |∫ b, M.kernel a b * v b ∂M.mu| ≤ ∫ b, |M.kernel a b * v b| ∂M.mu :=
      abs_integral_le_integral_abs
    _ = ∫ b, M.kernel a b * M.absVector v b ∂M.mu := by
      apply integral_congr_ae
      filter_upwards [] with b
      rw [abs_mul, abs_of_nonneg (M.nonneg a b), M.absVector_apply]

theorem fixed_of_nonneg_subfixed (M : CountableKernel) (hcrit : M.IsCritical)
    (v : M.L2) (hv : ∀ a, 0 ≤ v a) (hsub : ∀ a, v a ≤ M.actionCLM v a) :
    M.actionCLM v = v := by
  apply Eq.symm
  apply M.eq_of_nonneg_le_of_norm_le v (M.actionCLM v) hv hsub
  simpa [M.norm_eq_one_of_critical hcrit] using M.actionCLM.le_opNorm v

theorem fixed_abs_of_eigenvector (M : CountableKernel) (hcrit : M.IsCritical)
    {lam : ℝ} (hlam : |lam| = 1) (v : M.L2) (hev : M.actionCLM v = lam • v) :
    M.actionCLM (M.absVector v) = M.absVector v := by
  apply M.fixed_of_nonneg_subfixed hcrit _ (fun a ↦ by rw [M.absVector_apply]; positivity)
  intro a
  have he : |M.actionCLM v a| = |v a| := by
    rw [hev, M.coe_smul_at, abs_mul, hlam, one_mul]
  rw [M.absVector_apply, ← he]
  exact M.abs_action_le v a

theorem exists_positive_fixed (M : CountableKernel) (hcrit : M.IsCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    ∃ u : M.L2, u ≠ 0 ∧ (∀ a, 0 < u a) ∧ M.actionCLM u = u := by
  have hev := PerronWright.eigenvalue_one_or_neg_one M.actionCLM M.isCompactOperator_actionCLM
    M.isSymmetric_actionCLM (M.norm_eq_one_of_critical hcrit)
  have he : ∃ lam : ℝ, |lam| = 1 ∧ Module.End.HasEigenvalue M.actionCLM.toLinearMap lam := by
    rcases hev with hp | hn
    · exact ⟨1, by norm_num, hp⟩
    · exact ⟨-1, by norm_num, hn⟩
  obtain ⟨lam, hlam, hev⟩ := he
  obtain ⟨v, hv, hvne⟩ := hev.exists_hasEigenvector
  have hfix := M.fixed_abs_of_eigenvector hcrit hlam v (Module.End.mem_eigenspace_iff.mp hv)
  have habsne : M.absVector v ≠ 0 := by
    intro hz
    apply hvne
    apply norm_eq_zero.mp
    rw [← M.norm_absVector v, hz, norm_zero]
  refine ⟨M.absVector v, habsne, ?_, hfix⟩
  intro a
  have hp := M.actionCLM_strict_pos hlower hlo (M.absVector v)
    (fun b ↦ by rw [M.absVector_apply]; positivity) habsne a
  rwa [hfix] at hp

end PerronWright.CountableKernel
