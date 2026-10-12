import PerronWright.Kernel.Compact
import PerronWright.Model.CompactBJR
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The bridge between the continuous and `L²` kernel realizations

Assumption `(B1)` is stated for the self-adjoint `L²` realization, whereas
positivity and pointwise kernel arguments are most naturally carried out on
`C(S, ℝ)`.  This file proves, from the weak association condition in the
model, that the canonical inclusion of continuous functions into `L²`
intertwines the two operators.
-/

open MeasureTheory

noncomputable section

namespace PerronWright
namespace CompactBJRModel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem action_eq_integralAction (M : CompactBJRModel S) (f : C(S, ℝ)) (x : S) :
    M.kernel.action M.mu f x = M.integralAction f x := by
  rw [ContinuousKernel.action_apply]
  rfl

/-- The `C(S)` and `L²(μ)` realizations agree on every continuous
function. -/
theorem IsAssociatedL2Operator.intertwines (M : CompactBJRModel S)
    (K : M.L2 →L[ℝ] M.L2) (hK : M.IsAssociatedL2Operator K) (f : C(S, ℝ)) :
    K (ContinuousMap.toLp 2 M.mu ℝ f) =
      ContinuousMap.toLp 2 M.mu ℝ (M.kernel.action M.mu f) := by
  have hdense : DenseRange
      (ContinuousMap.toLp 2 M.mu ℝ : C(S, ℝ) →L[ℝ] M.L2) :=
    ContinuousMap.toLp_denseRange ℝ M.mu ℝ (by norm_num)
  apply hdense.eq_of_inner_left (𝕜 := ℝ)
  intro g
  rw [hK f g, ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [M.action_eq_integralAction f x]
  simp only [conj_trivial]

end CompactBJRModel
end PerronWright
