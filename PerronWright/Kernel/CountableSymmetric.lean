import PerronWright.Kernel.CountableIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Symmetry and self-adjointness of the countable integral operator

The symmetry of the actual kernel is transported to the constructed `L²`
operator by an integrable Fubini calculation.  No spectral conclusions are
assumed in the countable model.
-/

open MeasureTheory

noncomputable section

namespace PerronWright.CountableKernel

theorem integrable_input (M : CountableKernel) (v : M.L2) : Integrable v M.mu :=
  (Lp.memLp v).integrable (by norm_num)

theorem integrable_bilinear_kernel (M : CountableKernel) (v w : M.L2) :
    Integrable (fun p : ℕ × ℕ ↦ M.kernel p.1 p.2 * v p.2 * w p.1) (M.mu.prod M.mu) := by
  have hi := (M.integrable_input w).mul_prod (M.integrable_input v)
  have hκ : AEStronglyMeasurable (fun p : ℕ × ℕ ↦ M.kernel p.1 p.2) (M.mu.prod M.mu) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hb := hi.bdd_mul hκ
    (Filter.Eventually.of_forall (fun p : ℕ × ℕ ↦ M.norm_kernel_le p.1 p.2))
  exact hb.congr (Filter.Eventually.of_forall (fun p ↦ by dsimp; ring))

theorem inner_action_eq_double_integral (M : CountableKernel) (v w : M.L2) :
    inner ℝ (M.actionCLM v) w =
      ∫ a, ∫ b, M.kernel a b * v b * w a ∂M.mu ∂M.mu := by
  simp_rw [integral_mul_const]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [M.actionCLM_eq_integral_ae v] with a ha
  rw [ha]
  simp [mul_comm]

theorem isSymmetric_actionCLM (M : CountableKernel) : M.actionCLM.IsSymmetric := by
  intro v w
  change inner ℝ (M.actionCLM v) w = inner ℝ v (M.actionCLM w)
  rw [M.inner_action_eq_double_integral v w, real_inner_comm,
    M.inner_action_eq_double_integral w v]
  rw [integral_integral_swap (M.integrable_bilinear_kernel v w)]
  apply integral_congr_ae
  filter_upwards [] with b
  apply integral_congr_ae
  filter_upwards [] with a
  rw [M.symmetric a b]
  ring

theorem isSelfAdjoint_actionCLM (M : CountableKernel) : IsSelfAdjoint M.actionCLM :=
  M.isSymmetric_actionCLM.isSelfAdjoint

end PerronWright.CountableKernel
