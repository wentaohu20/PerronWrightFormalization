import PerronWright.Kernel.CountableApproximationSpectral

/-! # Actual spectral perturbation between two atomic probability laws

The spectral roots are the norms of the genuine self-adjoint shared-space
operators. Their difference is controlled by the actual square-root density
features and atomic absolute variation, with no spectral-continuity premise.
-/

open MeasureTheory
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.CountableKernel

theorem weightFeatureFunction_sub_square_le (M : CountableKernel) (w z : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hz : ∀ a, 0 ≤ z a) (a : ℕ) :
    M.mu.real {a} * (M.weightFeatureFunction w a - M.weightFeatureFunction z a) ^ 2 ≤
      |w a - z a| := by
  have hm := M.atomMass_pos a
  have hb := mul_le_mul_of_nonneg_left
    (sqrt_sub_sq_le_abs_sub (div_nonneg (hw a) hm.le) (div_nonneg (hz a) hm.le)) hm.le
  unfold weightFeatureFunction
  refine hb.trans_eq ?_
  rw [← sub_div, abs_div, abs_of_pos hm, mul_div_cancel₀ _ hm.ne']

theorem norm_weightFeature_sub_square_le (M : CountableKernel) (w z : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hz : ∀ a, 0 ≤ z a) (hsw : HasSum w 1) (hsz : HasSum z 1) :
    ‖M.weightFeature w hw hsw - M.weightFeature z hz hsz‖ ^ 2 ≤ ∑' a, |w a - z a| := by
  have habs := (hsw.summable.sub hsz.summable).abs
  have hterms : Summable (fun a ↦ M.mu.real {a} *
      (M.weightFeatureFunction w a - M.weightFeatureFunction z a) ^ 2) :=
    habs.of_nonneg_of_le (fun a ↦ mul_nonneg (M.atomMass_pos a).le (sq_nonneg _))
      (M.weightFeatureFunction_sub_square_le w z hw hz)
  rw [M.norm_sq_eq_integral, M.integral_eq_tsum_atom]
  simp_rw [M.coe_sub_at, M.weightFeature_apply]
  exact hterms.tsum_le_tsum (M.weightFeatureFunction_sub_square_le w z hw hz) habs

theorem weightedSpectralRadius_sub_abs_le (M : CountableKernel) (w z : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hz : ∀ a, 0 ≤ z a) (hsw : HasSum w 1) (hsz : HasSum z 1) :
    |M.weightedSpectralRadius w hw hsw - M.weightedSpectralRadius z hz hsz| ≤
      2 * M.upper * Real.sqrt (∑' a, |w a - z a|) := by
  rw [M.weightedSpectralRadius_eq_norm, M.weightedSpectralRadius_eq_norm]
  calc
    _ ≤ ‖M.weightedActionCLM (M.weightFeature w hw hsw) -
        M.weightedActionCLM (M.weightFeature z hz hsz)‖ := abs_norm_sub_norm_le _ _
    _ ≤ M.upper * (‖M.weightFeature w hw hsw‖ + ‖M.weightFeature z hz hsz‖) *
        ‖M.weightFeature w hw hsw - M.weightFeature z hz hsz‖ := M.norm_weightedActionCLM_sub_le _ _
    _ = 2 * M.upper * ‖M.weightFeature w hw hsw - M.weightFeature z hz hsz‖ := by
      rw [M.norm_weightFeature, M.norm_weightFeature]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.le_sqrt_of_sq_le (M.norm_weightFeature_sub_square_le w z hw hz hsw hsz))
      (mul_nonneg (by norm_num) M.upper_nonneg)

theorem weightedSpectralRadius_sub_square_le (M : CountableKernel) (w z : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hz : ∀ a, 0 ≤ z a) (hsw : HasSum w 1) (hsz : HasSum z 1) :
    (M.weightedSpectralRadius w hw hsw - M.weightedSpectralRadius z hz hsz) ^ 2 ≤
      4 * M.upper ^ 2 * (∑' a, |w a - z a|) := by
  have h := M.weightedSpectralRadius_sub_abs_le w z hw hz hsw hsz
  have hnn : 0 ≤ ∑' a, |w a - z a| := tsum_nonneg (fun _ ↦ abs_nonneg _)
  have hh := mul_self_le_mul_self (abs_nonneg _) h
  rw [← sq, ← sq, sq_abs, mul_pow, mul_pow, Real.sq_sqrt hnn] at hh
  norm_num at hh ⊢
  exact hh

end PerronWright.CountableKernel
