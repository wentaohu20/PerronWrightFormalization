import PerronWright.Kernel.CountableApproximationFinite

/-!
# Perron existence for actual finite probability laws

The top spectral value of the actual weighted finite-support operator is
positive under the literal lower kernel bound.  Its nonnegative Perron
vector is obtained from a compact self-adjoint endpoint eigenvector using
the absolute-value argument, not supplied as an assumption.
-/

open MeasureTheory

noncomputable section

namespace PerronWright.CountableKernel

theorem integrable_feature_row_mul_input (M : CountableKernel) (h v : M.L2) (a : ℕ) :
    Integrable (fun b ↦ M.kernel a b * h b * v b) M.mu := by
  have hi := (Lp.memLp (M.featureRow h a)).integrable_mul (Lp.memLp v)
  exact hi.congr (Filter.Eventually.of_forall (fun b ↦ by
    change M.featureRow h a b * v b = M.kernel a b * h b * v b
    rw [M.featureRow_apply]))

theorem weightedActionCLM_nonneg (M : CountableKernel) (h v : M.L2)
    (hh : ∀ a, 0 ≤ h a) (hv : ∀ a, 0 ≤ v a) (a : ℕ) :
    0 ≤ M.weightedActionCLM h v a := by
  rw [weightedActionCLM, M.featureActionCLM_apply_integral]
  exact mul_nonneg (hh a) (integral_nonneg (fun b ↦
    mul_nonneg (mul_nonneg (M.nonneg a b) (hh b)) (hv b)))

theorem abs_weightedAction_le (M : CountableKernel) (h v : M.L2)
    (hh : ∀ a, 0 ≤ h a) (a : ℕ) :
    |M.weightedActionCLM h v a| ≤ M.weightedActionCLM h (M.absVector v) a := by
  rw [weightedActionCLM, M.featureActionCLM_apply_integral,
    M.featureActionCLM_apply_integral, abs_mul, abs_of_nonneg (hh a)]
  apply mul_le_mul_of_nonneg_left _ (hh a)
  calc
    |∫ b, M.kernel a b * h b * v b ∂M.mu| ≤
        ∫ b, |M.kernel a b * h b * v b| ∂M.mu := abs_integral_le_integral_abs
    _ = ∫ b, M.kernel a b * h b * M.absVector v b ∂M.mu := by
      apply integral_congr_ae
      filter_upwards [] with b
      rw [abs_mul, abs_mul, abs_of_nonneg (M.nonneg a b), abs_of_nonneg (hh b), M.absVector_apply]

theorem weighted_norm_ge_lower (M : CountableKernel) (h : M.L2) (hn : ‖h‖ = 1)
    {lower : ℝ} (hlo : ∀ a b, lower ≤ M.kernel a b) :
    lower ≤ ‖M.weightedActionCLM h‖ := by
  have hs : (∫ a, h a ^ 2 ∂M.mu) = 1 := by rw [← M.norm_sq_eq_integral, hn]; norm_num
  have hrow : ∀ a, lower ≤ ∫ b, M.kernel a b * h b * h b ∂M.mu := by
    intro a
    calc
      lower = ∫ b, lower * h b ^ 2 ∂M.mu := by rw [integral_const_mul, hs, mul_one]
      _ ≤ ∫ b, M.kernel a b * h b * h b ∂M.mu := by
        apply integral_mono ((Lp.memLp h).integrable_sq.const_mul lower)
          (M.integrable_feature_row_mul_input h h a)
        intro b
        nlinarith [mul_le_mul_of_nonneg_right (hlo a b) (sq_nonneg (h b))]
  have hi : lower ≤ inner ℝ (M.weightedActionCLM h h) h := by
    rw [L2.inner_def]
    calc
      lower = ∫ a, lower * h a ^ 2 ∂M.mu := by rw [integral_const_mul, hs, mul_one]
      _ ≤ ∫ a, inner ℝ (M.weightedActionCLM h h a) (h a) ∂M.mu := by
        apply integral_mono ((Lp.memLp h).integrable_sq.const_mul lower)
          (L2.integrable_inner (M.weightedActionCLM h h) h)
        intro a
        change lower * h a ^ 2 ≤ inner ℝ (M.weightedActionCLM h h a) (h a)
        rw [weightedActionCLM, M.featureActionCLM_apply_integral]
        simpa [pow_two, mul_comm, mul_assoc, mul_left_comm] using
          mul_le_mul_of_nonneg_right (hrow a) (sq_nonneg (h a))
  calc
    lower ≤ inner ℝ (M.weightedActionCLM h h) h := hi
    _ ≤ ‖M.weightedActionCLM h h‖ * ‖h‖ := real_inner_le_norm _ _
    _ ≤ ‖M.weightedActionCLM h‖ * ‖h‖ * ‖h‖ := by
      gcongr
      exact (M.weightedActionCLM h).le_opNorm h
    _ = ‖M.weightedActionCLM h‖ := by rw [hn]; ring

theorem weighted_abs_eigenvector_at_norm (M : CountableKernel) (h : M.L2)
    (hh : ∀ a, 0 ≤ h a) {lam : ℝ} (hlam : |lam| = ‖M.weightedActionCLM h‖)
    (v : M.L2) (hev : M.weightedActionCLM h v = lam • v) :
    M.weightedActionCLM h (M.absVector v) = ‖M.weightedActionCLM h‖ • M.absVector v := by
  apply Eq.symm
  apply M.eq_of_nonneg_le_of_norm_le
  · intro a
    rw [M.coe_smul_at, M.absVector_apply]
    exact mul_nonneg (norm_nonneg _) (abs_nonneg _)
  · intro a
    rw [M.coe_smul_at, M.absVector_apply, ← hlam]
    have he : |M.weightedActionCLM h v a| = |lam| * |v a| := by
      rw [hev, M.coe_smul_at, abs_mul]
    rw [← he]
    exact M.abs_weightedAction_le h v hh a
  · rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
    exact (M.weightedActionCLM h).le_opNorm _

/-- Genuine normalized nonnegative Perron vectors for finite-support
probability weights, with positive eigenvalue equal to the real spectral
radius.  No Perron vector or eigenvalue is a model field. -/
theorem exists_nonnegative_weighted_perron (M : CountableKernel)
    (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) {lower : ℝ}
    (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    0 < M.weightedSpectralRadius w hw hs ∧
      ∃ v : M.L2, ‖v‖ = 1 ∧ (∀ a, 0 ≤ v a) ∧
        M.weightedActionCLM (M.weightFeature w hw hs) v =
          M.weightedSpectralRadius w hw hs • v := by
  classical
  let h := M.weightFeature w hw hs
  let T := M.weightedActionCLM h
  have hhn : ‖h‖ = 1 := M.norm_weightFeature w hw hs
  have hhp : ∀ a, 0 ≤ h a := by
    intro a
    dsimp [h]
    rw [M.weightFeature_apply, weightFeatureFunction]
    exact Real.sqrt_nonneg _
  have hr : 0 < ‖T‖ := hlower.trans_le (M.weighted_norm_ge_lower h hhn hlo)
  rw [M.weightedSpectralRadius_eq_norm]
  refine ⟨hr, ?_⟩
  have hc : IsCompactOperator T := M.isCompactOperator_weighted_probability_of_finite_support w hw hs s hzero
  have hsym : T.IsSymmetric := M.isSymmetric_weightedActionCLM h
  have hnt : Nontrivial M.L2 := by
    cases subsingleton_or_nontrivial M.L2 with
    | inl hsub =>
      let _ := hsub
      have hz : T = 0 := Subsingleton.elim _ _
      simp [hz] at hr
    | inr hnon => exact hnon
  let _ := hnt
  have hend := PerronWright.norm_or_neg_norm_mem_spectrum T hsym
  have he : ∃ lam : ℝ, |lam| = ‖T‖ ∧ Module.End.HasEigenvalue T.toLinearMap lam := by
    rcases hend with hp | hn
    · exact ⟨‖T‖, abs_of_pos hr, (hc.hasEigenvalue_iff_mem_spectrum hr.ne').mpr hp⟩
    · exact ⟨-‖T‖, by rw [abs_neg, abs_of_pos hr],
        (hc.hasEigenvalue_iff_mem_spectrum (neg_ne_zero.mpr hr.ne')).mpr hn⟩
  obtain ⟨lam, hlam, hev⟩ := he
  obtain ⟨v, hv, hvne⟩ := hev.exists_hasEigenvector
  have habs : M.absVector v ≠ 0 := by
    intro hz
    apply hvne
    apply norm_eq_zero.mp
    rw [← M.norm_absVector v, hz, norm_zero]
  have hnabs : 0 < ‖M.absVector v‖ := norm_pos_iff.mpr habs
  have hfix := M.weighted_abs_eigenvector_at_norm h hhp hlam v (Module.End.mem_eigenspace_iff.mp hv)
  refine ⟨‖M.absVector v‖⁻¹ • M.absVector v, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnabs.le), inv_mul_cancel₀ hnabs.ne']
  · intro a
    rw [M.coe_smul_at, M.absVector_apply]
    exact mul_nonneg (inv_nonneg.mpr hnabs.le) (abs_nonneg _)
  · rw [map_smul, hfix, smul_comm]

end PerronWright.CountableKernel
