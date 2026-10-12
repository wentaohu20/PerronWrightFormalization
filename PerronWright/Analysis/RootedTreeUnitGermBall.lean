import PerronWright.Analysis.RootedTreeUnitCircleGerm
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Explicit analytic balls for noncritical unit-circle tree germs

The implicit germ at a noncritical unit-circle point is made quantitative:
one common Euclidean ball supports analyticity of the zero-field slice, the
tree equation, and agreement with the actual labelled-tree series on the
interior part of that ball.  A second lemma records the corresponding
identity principle on overlaps which meet the open unit disk.
-/

open Filter
open scoped Classical Topology
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Every noncritical unit-circle point admits a genuine analytic tree
solution on an explicit positive-radius ball.  On the part of the ball
inside the open unit disk, this solution is the actual rooted-tree Taylor
sum. -/
theorem CompactBJRModel.exists_rootedTreeSeries_unit_germ_ball
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ (ψ : ℂ × C(S, ℂ) → C(S, ℂ)) (r : ℝ),
      0 < r ∧
      ψ (z, 0) = M.rootedTreeSeries z ∧
      (∀ w ∈ Metric.ball z r,
        AnalyticAt ℂ (fun u : ℂ => ψ (u, 0)) w) ∧
      (∀ w ∈ Metric.ball z r,
        TreeCritical.residual M ((w, 0), ψ (w, 0)) = 0) ∧
      ∀ w ∈ Metric.ball z r, ‖w‖ < 1 →
        ψ (w, 0) = M.rootedTreeSeries w := by
  obtain ⟨ψ, hψa, hψz, hψres, -, hglue⟩ :=
    M.exists_rootedTreeSeries_unit_germ_glued hM hz hz1
  let slice : ℂ → C(S, ℂ) := fun w => ψ (w, 0)
  have hembA : AnalyticAt ℂ
      (fun w : ℂ => (w, (0 : C(S, ℂ)))) z :=
    analyticAt_id.prod analyticAt_const
  have hsliceAt : AnalyticAt ℂ slice z :=
    hψa.comp_of_eq hembA rfl
  have hsliceNhd : ∀ᶠ w : ℂ in 𝓝 z, AnalyticAt ℂ slice w :=
    hsliceAt.eventually_analyticAt
  have hembT : Filter.Tendsto
      (fun w : ℂ => (w, (0 : C(S, ℂ)))) (𝓝 z) (𝓝 (z, 0)) :=
    hembA.continuousAt.tendsto
  have hresNhd : ∀ᶠ w : ℂ in 𝓝 z,
      TreeCritical.residual M ((w, 0), slice w) = 0 := by
    simpa only [slice] using hembT.eventually hψres
  have hlocal : ∀ᶠ w : ℂ in 𝓝 z,
      AnalyticAt ℂ slice w ∧
        TreeCritical.residual M ((w, 0), slice w) = 0 :=
    hsliceNhd.and hresNhd
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.mem_nhds_iff.mp hlocal
  have hglue' : slice =ᶠ[
      𝓝[{w : ℂ | ‖w‖ < 1}] z] M.rootedTreeSeries := by
    simpa only [slice, Function.comp_def] using hglue
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhdsWithin_iff.mp hglue'
  refine ⟨ψ, min r₀ r₁, lt_min hr₀ hr₁, hψz, ?_, ?_, ?_⟩
  · intro w hw
    exact (hball₀ ((Metric.ball_subset_ball (min_le_left r₀ r₁)) hw)).1
  · intro w hw
    exact (hball₀ ((Metric.ball_subset_ball (min_le_left r₀ r₁)) hw)).2
  · intro w hw hwI
    have hw₁ : w ∈ Metric.ball z r₁ :=
      (Metric.ball_subset_ball (min_le_right r₀ r₁)) hw
    exact hball₁ ⟨hw₁, hwI⟩

/-- Two analytic germ balls agree on their whole connected overlap as soon
as that overlap contains one point of the open unit disk.  Thus the local
continuations have the expected sheaf compatibility without any additional
multiplier or continuation hypothesis. -/
theorem CompactBJRModel.rootedTreeSeries_unit_germ_balls_agree_on_overlap
    (M : CompactBJRModel S)
    (z₁ z₂ : ℂ) (r₁ r₂ : ℝ)
    (ψ₁ ψ₂ : ℂ × C(S, ℂ) → C(S, ℂ))
    (h₁a : ∀ w ∈ Metric.ball z₁ r₁,
      AnalyticAt ℂ (fun u : ℂ => ψ₁ (u, 0)) w)
    (h₂a : ∀ w ∈ Metric.ball z₂ r₂,
      AnalyticAt ℂ (fun u : ℂ => ψ₂ (u, 0)) w)
    (h₁eq : ∀ w ∈ Metric.ball z₁ r₁, ‖w‖ < 1 →
      ψ₁ (w, 0) = M.rootedTreeSeries w)
    (h₂eq : ∀ w ∈ Metric.ball z₂ r₂, ‖w‖ < 1 →
      ψ₂ (w, 0) = M.rootedTreeSeries w)
    {w₀ : ℂ} (hw₀₁ : w₀ ∈ Metric.ball z₁ r₁)
    (hw₀₂ : w₀ ∈ Metric.ball z₂ r₂) (hw₀I : ‖w₀‖ < 1) :
    Set.EqOn (fun w : ℂ => ψ₁ (w, 0))
      (fun w : ℂ => ψ₂ (w, 0))
      (Metric.ball z₁ r₁ ∩ Metric.ball z₂ r₂) := by
  let U : Set ℂ := Metric.ball z₁ r₁ ∩ Metric.ball z₂ r₂
  have h₁an : AnalyticOnNhd ℂ (fun w : ℂ => ψ₁ (w, 0)) U := by
    intro w hw
    exact h₁a w hw.1
  have h₂an : AnalyticOnNhd ℂ (fun w : ℂ => ψ₂ (w, 0)) U := by
    intro w hw
    exact h₂a w hw.2
  have hU : IsPreconnected U :=
    ((convex_ball z₁ r₁).inter (convex_ball z₂ r₂)).isPreconnected
  have hw₀U : w₀ ∈ U := ⟨hw₀₁, hw₀₂⟩
  have hw₀unit : w₀ ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hw₀I
  have heq : (fun w : ℂ => ψ₁ (w, 0)) =ᶠ[𝓝 w₀]
      (fun w : ℂ => ψ₂ (w, 0)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw₀₁,
      Metric.isOpen_ball.mem_nhds hw₀₂,
      Metric.isOpen_ball.mem_nhds hw₀unit] with w hw₁ hw₂ hwI
    have hwnorm : ‖w‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hwI
    exact (h₁eq w hw₁ hwnorm).trans (h₂eq w hw₂ hwnorm).symm
  exact h₁an.eqOn_of_preconnected_of_eventuallyEq h₂an hU hw₀U heq

end PerronWright
