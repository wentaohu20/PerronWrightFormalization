import PerronWright.Kernel.CountablePerron

/-!
# Geometric simplicity of the critical countable Perron eigenvector

Every nonzero fixed vector has a strictly positive absolute value at every
atom.  Subtracting the scalar multiple matching one coordinate therefore
proves that the whole fixed eigenspace is one-dimensional.  This proof does
not require a maximum to be attained on the countable type space.
-/

open MeasureTheory Module

noncomputable section

namespace PerronWright.CountableKernel

theorem coe_sub_at (M : CountableKernel) (v w : M.L2) (a : ℕ) :
    (v - w) a = v a - w a :=
  M.forall_of_ae (Lp.coeFn_sub v w) a

theorem fixed_abs_strict_pos (M : CountableKernel) (hcrit : M.IsCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (v : M.L2) (hvne : v ≠ 0) (hfix : M.actionCLM v = v) (a : ℕ) : 0 < |v a| := by
  have hfa := M.fixed_abs_of_eigenvector hcrit (lam := 1) (by norm_num) v (by simpa using hfix)
  have hne : M.absVector v ≠ 0 := by
    intro hz
    apply hvne
    apply norm_eq_zero.mp
    rw [← M.norm_absVector v, hz, norm_zero]
  have hp := M.actionCLM_strict_pos hlower hlo (M.absVector v)
    (fun b ↦ by rw [M.absVector_apply]; positivity) hne a
  rwa [hfa, M.absVector_apply] at hp

theorem fixed_eq_scalar_multiple (M : CountableKernel) (hcrit : M.IsCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (u : M.L2) (hu : ∀ a, 0 < u a) (hTu : M.actionCLM u = u)
    (v : M.L2) (hTv : M.actionCLM v = v) : ∃ c : ℝ, v = c • u := by
  let c : ℝ := v 0 / u 0
  let h : M.L2 := v - c • u
  have hTh : M.actionCLM h = h := by
    dsimp only [h]
    rw [map_sub, map_smul, hTv, hTu]
  have hh0 : h 0 = 0 := by
    dsimp only [h]
    rw [M.coe_sub_at, M.coe_smul_at]
    dsimp only [c]
    rw [div_mul_cancel₀ _ (hu 0).ne', sub_self]
  have hz : h = 0 := by
    by_contra hne
    have hp := M.fixed_abs_strict_pos hcrit hlower hlo h hne hTh 0
    simp [hh0] at hp
  exact ⟨c, sub_eq_zero.mp hz⟩

theorem eigenspace_one_eq_span (M : CountableKernel) (hcrit : M.IsCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (u : M.L2) (hu : ∀ a, 0 < u a) (hTu : M.actionCLM u = u) :
    Module.End.eigenspace M.actionCLM.toLinearMap 1 = Submodule.span ℝ {u} := by
  apply le_antisymm
  · intro v hv
    obtain ⟨c, hc⟩ := M.fixed_eq_scalar_multiple hcrit hlower hlo u hu hTu v
      (by simpa using Module.End.mem_eigenspace_iff.mp hv)
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · apply Submodule.span_le.mpr
    intro v hv
    obtain rfl := Set.mem_singleton_iff.mp hv
    apply Module.End.mem_eigenspace_iff.mpr
    simpa using hTu

theorem eigenspace_one_finrank (M : CountableKernel) (hcrit : M.IsCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (u : M.L2) (hu : ∀ a, 0 < u a) (hTu : M.actionCLM u = u) :
    Module.finrank ℝ (Module.End.eigenspace M.actionCLM.toLinearMap 1) = 1 := by
  rw [M.eigenspace_one_eq_span hcrit hlower hlo u hu hTu]
  apply finrank_span_singleton
  intro hz
  have hp := hu 0
  simp [hz] at hp

theorem integral_smul_input (M : CountableKernel) (c : ℝ) (v : M.L2) :
    (∫ a, (c • v) a ∂M.mu) = c * ∫ a, v a ∂M.mu := by
  simp_rw [M.coe_smul_at]
  exact integral_const_mul _ _

/-- The normalization used by the paper is proved to exist and be unique. -/
theorem existsUnique_normalized_positive_fixed (M : CountableKernel) (hcrit : M.IsCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    ∃! u : M.L2, (∀ a, 0 < u a) ∧ M.actionCLM u = u ∧ (∫ a, u a ∂M.mu) = 1 := by
  obtain ⟨v, hvne, hvpos, hTv⟩ := M.exists_positive_fixed hcrit hlower hlo
  have hvint : 0 < ∫ a, v a ∂M.mu := M.integral_input_pos v (fun a ↦ (hvpos a).le) hvne
  let u : M.L2 := (∫ a, v a ∂M.mu)⁻¹ • v
  have hupos : ∀ a, 0 < u a := by
    intro a
    dsimp only [u]
    rw [M.coe_smul_at]
    exact mul_pos (inv_pos.mpr hvint) (hvpos a)
  have hTu : M.actionCLM u = u := by
    dsimp only [u]
    rw [map_smul, hTv]
  have huint : (∫ a, u a ∂M.mu) = 1 := by
    dsimp only [u]
    rw [M.integral_smul_input, inv_mul_cancel₀ hvint.ne']
  refine ⟨u, ⟨hupos, hTu, huint⟩, ?_⟩
  intro w hw
  obtain ⟨c, hc⟩ := M.fixed_eq_scalar_multiple hcrit hlower hlo u hupos hTu w hw.2.1
  have hc1 : c = 1 := by
    have hi := hw.2.2
    rw [hc, M.integral_smul_input, huint, mul_one] at hi
    exact hi
  simpa [hc1] using hc

theorem normalized_fixed_bounds (M : CountableKernel) {lower : ℝ}
    (hlo : ∀ a b, lower ≤ M.kernel a b) (u : M.L2) (hu : ∀ a, 0 ≤ u a)
    (hTu : M.actionCLM u = u) (hint : (∫ a, u a ∂M.mu) = 1) (a : ℕ) :
    lower ≤ u a ∧ u a ≤ M.upper := by
  constructor
  · have h := M.actionCLM_ge_lower_integral hlo u hu a
    simpa [hTu, hint] using h
  · have h : M.actionCLM u a ≤ M.upper * (∫ b, u b ∂M.mu) := by
      rw [M.actionCLM_apply_integral, ← integral_const_mul]
      apply integral_mono (M.integrable_row_mul_input u a) ((M.integrable_input u).const_mul _)
      intro b
      exact mul_le_mul_of_nonneg_right (M.le_upper a b) (hu b)
    simpa [hTu, hint] using h

end PerronWright.CountableKernel
