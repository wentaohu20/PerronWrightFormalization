import PerronWright.Kernel.Integral
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Compactness of continuous-kernel integral operators

The proof is a direct Arzelà--Ascoli argument.  A bounded family of inputs
gives a uniformly bounded family of outputs, while the rows of the continuous
kernel supply a common modulus of continuity.
-/

open MeasureTheory

noncomputable section

namespace PerronWright
namespace ContinuousKernel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem dist_action_apply_le (k : ContinuousKernel S) (mu : Measure S)
    [IsProbabilityMeasure mu] (f : C(S, ℝ)) (x x' : S) :
    dist (k.action mu f x) (k.action mu f x') ≤ ‖k.rows x - k.rows x'‖ * ‖f‖ := by
  rw [dist_eq_norm, action_apply, action_apply, ← integral_sub]
  · calc
      ‖∫ y, k x y * f y - k x' y * f y ∂mu‖
          ≤ (‖k.rows x - k.rows x'‖ * ‖f‖) * mu.real Set.univ := by
        apply norm_integral_le_of_norm_le_const
        filter_upwards [] with y
        rw [← sub_mul, norm_mul]
        gcongr
        · exact (k.rows x - k.rows x').norm_coe_le_norm y
        · exact f.norm_coe_le_norm y
      _ = ‖k.rows x - k.rows x'‖ * ‖f‖ := by simp
  · exact (k.continuous_left x).mul f.continuous |>.integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  · exact (k.continuous_left x').mul f.continuous |>.integrable_of_hasCompactSupport
      isClosed_closure.isCompact

/-- A continuous kernel on a compact type defines a compact operator on
`C(S, ℝ)`. -/
theorem isCompactOperator_actionCLM (k : ContinuousKernel S) (mu : Measure S)
    [IsProbabilityMeasure mu] : IsCompactOperator (k.actionCLM mu) := by
  let e := ContinuousMap.linearIsometryBoundedOfCompact S ℝ ℝ
  let A : Set (BoundedContinuousFunction S ℝ) :=
    e '' ((k.actionCLM mu) '' Metric.closedBall 0 1)
  have hA_range : ∀ (g : BoundedContinuousFunction S ℝ) (x : S), g ∈ A →
      g x ∈ Metric.closedBall (0 : ℝ) ‖k.toContinuousMap‖ := by
    rintro g x ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖k.action mu f x‖ ≤ ‖k.toContinuousMap‖
    exact le_trans (ContinuousMap.norm_coe_le_norm (k.action mu f) x)
      (le_trans (k.norm_action_le mu f) (mul_le_of_le_one_right (norm_nonneg _)
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hf)))
  have hA_equicont : Equicontinuous ((↑) : A → S → ℝ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [k.rows.continuous.continuousAt.eventually (Metric.ball_mem_nhds _ hε)]
      with x hx g
    rw [dist_comm] at hx
    rcases g.property with ⟨_, ⟨f, hf, rfl⟩, hg⟩
    rw [← hg]
    rw [ContinuousMap.linearIsometryBoundedOfCompact_apply_apply,
      ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]
    refine lt_of_le_of_lt (k.dist_action_apply_le mu f x₀ x) ?_
    calc
      ‖k.rows x₀ - k.rows x‖ * ‖f‖ ≤ ‖k.rows x₀ - k.rows x‖ * 1 := by
        gcongr
        simpa [Metric.mem_closedBall, dist_zero_right] using hf
      _ = dist (k.rows x₀) (k.rows x) := by rw [mul_one, dist_eq_norm]
      _ < ε := hx
  have hcompactA : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli
      (Metric.closedBall (0 : ℝ) ‖k.toContinuousMap‖)
      (isCompact_closedBall _ _) A hA_range hA_equicont
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ zero_lt_one,
    e.symm '' closure A, hcompactA.image e.symm.continuous, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  refine ⟨e (k.actionCLM mu f),
    subset_closure ⟨k.actionCLM mu f, ⟨f, hf, rfl⟩, rfl⟩, ?_⟩
  simp [e]

end ContinuousKernel
end PerronWright

