import PerronWright.Kernel.CountableSymmetric

/-!
# Positivity of the actual countable integral action

Pointwise nonnegative inputs are mapped to pointwise nonnegative outputs.
A literal strictly positive lower kernel bound makes every nonzero
nonnegative input map to a strictly positive function.
-/

open MeasureTheory

noncomputable section

namespace PerronWright.CountableKernel

theorem integrable_row_mul_input (M : CountableKernel) (v : M.L2) (a : ℕ) :
    Integrable (fun b ↦ M.kernel a b * v b) M.mu :=
  (M.integrable_input v).bdd_mul (measurable_of_countable _).aestronglyMeasurable
    (Filter.Eventually.of_forall (M.norm_kernel_le a))

theorem actionCLM_nonneg (M : CountableKernel) (v : M.L2) (hv : ∀ a, 0 ≤ v a) (a : ℕ) :
    0 ≤ M.actionCLM v a := by
  rw [M.actionCLM_apply_integral]
  exact integral_nonneg (fun b ↦ mul_nonneg (M.nonneg a b) (hv b))

theorem integral_input_pos (M : CountableKernel) (v : M.L2) (hv : ∀ a, 0 ≤ v a)
    (hvne : v ≠ 0) : 0 < ∫ a, v a ∂M.mu := by
  have hn : 0 ≤ ∫ a, v a ∂M.mu := integral_nonneg hv
  apply lt_of_le_of_ne hn
  intro hz
  have hae : v =ᵐ[M.mu] (fun _ ↦ (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hv)
      (M.integrable_input v)).mp hz.symm
  apply hvne
  apply Lp.ext
  filter_upwards [hae] with a ha
  simpa using ha

theorem actionCLM_ge_lower_integral (M : CountableKernel) {lower : ℝ}
    (hlo : ∀ a b, lower ≤ M.kernel a b) (v : M.L2) (hv : ∀ a, 0 ≤ v a) (a : ℕ) :
    lower * (∫ b, v b ∂M.mu) ≤ M.actionCLM v a := by
  rw [M.actionCLM_apply_integral, ← integral_const_mul]
  apply integral_mono ((M.integrable_input v).const_mul lower) (M.integrable_row_mul_input v a)
  intro b
  exact mul_le_mul_of_nonneg_right (hlo a b) (hv b)

/-- Strong positivity is a consequence of the literal lower kernel bound,
not an operator-positivity assumption. -/
theorem actionCLM_strict_pos (M : CountableKernel) {lower : ℝ} (hlower : 0 < lower)
    (hlo : ∀ a b, lower ≤ M.kernel a b) (v : M.L2)
    (hv : ∀ a, 0 ≤ v a) (hvne : v ≠ 0) (a : ℕ) : 0 < M.actionCLM v a :=
  lt_of_lt_of_le (mul_pos hlower (M.integral_input_pos v hv hvne))
    (M.actionCLM_ge_lower_integral hlo v hv a)

end PerronWright.CountableKernel
