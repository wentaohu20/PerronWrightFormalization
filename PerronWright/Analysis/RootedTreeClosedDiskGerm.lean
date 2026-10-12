import PerronWright.Analysis.RootedTreeClosedDiskPartial

/-!
# Joint rooted-tree germs on the noncritical closed unit disk

The proved invertibility of the unknown derivative supplies a genuine joint
implicit-function germ at every `z` in the closed unit disk except `1`.
Shrinking the germ finitely many times gives one explicit product box which
retains analyticity, the residual equation, agreement with the literal
rooted-tree series on the open-disk slice, and local residual uniqueness
along its zero-field spine.
-/

open Filter
open scoped Classical Topology

noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The actual rooted-tree profile at any noncritical point of the closed
unit disk has a jointly analytic and locally unique `(z,g)` continuation. -/
theorem CompactBJRModel.rootedTreeSeries_closedDisk_analytic_neighborhood
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    ∃ ψ : ℂ × C(S, ℂ) → C(S, ℂ),
      AnalyticAt ℂ ψ (z, 0) ∧
      ψ (z, 0) = M.rootedTreeSeries z ∧
      (∀ᶠ q in 𝓝 (z, 0), TreeCritical.residual M (q, ψ q) = 0) ∧
      ∀ᶠ p in 𝓝 ((z, 0), M.rootedTreeSeries z),
        TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2 := by
  let a : (ℂ × C(S, ℂ)) × C(S, ℂ) :=
    ((z, 0), M.rootedTreeSeries z)
  have hu : IsUnit (fderiv ℂ (TreeCritical.residual M) a ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)) :=
    M.rootedTreeSeries_closedDisk_partial_isUnit hM hz hz1
  have hi : (fderiv ℂ (TreeCritical.residual M) a ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofUnit hu.unit, by
      change (hu.unit : C(S, ℂ) →L[ℂ] C(S, ℂ)) = _
      exact hu.unit_spec⟩
  have hres : TreeCritical.residual M a = 0 :=
    M.rootedTreeSeries_residual_zero_closedDisk hM hz
  have hres' : TreeAnalytic.residual M.kernel M.mu
      (TreeCritical.degree M) a = 0 := hres
  obtain ⟨ψ, ha, heq, hloc, huniq⟩ :=
    TreeAnalytic.residual_implicit_exists M.kernel M.mu
      (TreeCritical.degree M) a hi
  rw [hres'] at hloc huniq
  exact ⟨ψ, ha, heq, hloc, huniq⟩

private theorem CompactBJRModel.exists_joint_germ_box_of_closedDisk_germ
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ ≤ 1)
    (ψ : ℂ × C(S, ℂ) → C(S, ℂ))
    (hψa : AnalyticAt ℂ ψ (z, 0))
    (hψz : ψ (z, 0) = M.rootedTreeSeries z)
    (hψres : ∀ᶠ q in 𝓝 (z, 0),
      TreeCritical.residual M (q, ψ q) = 0)
    (hψuniq : ∀ᶠ p in 𝓝 ((z, 0), M.rootedTreeSeries z),
      TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2) :
    ∃ r : ℝ, 0 < r ∧
      (∀ q ∈ Metric.ball z r ×ˢ Metric.ball (0 : C(S, ℂ)) r,
        AnalyticAt ℂ ψ q) ∧
      (∀ q ∈ Metric.ball z r ×ˢ Metric.ball (0 : C(S, ℂ)) r,
        TreeCritical.residual M (q, ψ q) = 0) ∧
      (∀ w ∈ Metric.ball z r, ‖w‖ < 1 →
        ψ (w, 0) = M.rootedTreeSeries w) ∧
      ∀ w ∈ Metric.ball z r,
        ∀ᶠ p in 𝓝 ((w, (0 : C(S, ℂ))), ψ (w, 0)),
          TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2 := by
  have hjoint : ∀ᶠ q in 𝓝 (z, (0 : C(S, ℂ))),
      AnalyticAt ℂ ψ q ∧ TreeCritical.residual M (q, ψ q) = 0 :=
    hψa.eventually_analyticAt.and hψres
  obtain ⟨rJoint, hrJoint, hJointBall⟩ := Metric.mem_nhds_iff.mp hjoint

  let H : Set ((ℂ × C(S, ℂ)) × C(S, ℂ)) :=
    {p | TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2}
  have hH : H ∈ 𝓝 (((z, (0 : C(S, ℂ))), M.rootedTreeSeries z)) := by
    exact hψuniq
  obtain ⟨d, hd, hdH⟩ := Metric.mem_nhds_iff.mp hH
  have hembA : AnalyticAt ℂ
      (fun w : ℂ => (w, (0 : C(S, ℂ)))) z :=
    analyticAt_id.prod analyticAt_const
  have hembT : Tendsto (fun w : ℂ => (w, (0 : C(S, ℂ))))
      (𝓝 z) (𝓝 (z, 0)) := hembA.continuousAt.tendsto
  have hψT : Tendsto (fun w : ℂ => ψ (w, 0)) (𝓝 z) (𝓝 (ψ (z, 0))) :=
    hψa.continuousAt.tendsto.comp hembT
  have hgraphT : Tendsto
      (fun w : ℂ => ((w, (0 : C(S, ℂ))), ψ (w, 0)))
      (𝓝 z) (𝓝 (((z, (0 : C(S, ℂ))), M.rootedTreeSeries z))) := by
    simpa only [hψz] using hembT.prodMk_nhds hψT
  have hgraphBall : ∀ᶠ w : ℂ in 𝓝 z,
      ((w, (0 : C(S, ℂ))), ψ (w, 0)) ∈
        Metric.ball (((z, (0 : C(S, ℂ))), M.rootedTreeSeries z)) d :=
    hgraphT.eventually
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hd))
  have hspineUniq : ∀ᶠ w : ℂ in 𝓝 z,
      ∀ᶠ p in 𝓝 ((w, (0 : C(S, ℂ))), ψ (w, 0)),
        TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2 := by
    filter_upwards [hgraphBall] with w hw
    exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hw) hdH
  obtain ⟨rUniq, hrUniq, hUniqBall⟩ := Metric.mem_nhds_iff.mp hspineUniq

  have hseries : Tendsto M.rootedTreeSeries
      (𝓝[{w : ℂ | ‖w‖ < 1}] z) (𝓝 (M.rootedTreeSeries z)) :=
    ((M.rootedTreeSeries_continuousOn_closedDisk hM z hz).mono
      (fun w hw => by
        change ‖w‖ ≤ 1
        exact hw.le)).tendsto
  have hpair : Tendsto
      (fun w : ℂ => ((w, (0 : C(S, ℂ))), M.rootedTreeSeries w))
      (𝓝[{w : ℂ | ‖w‖ < 1}] z)
      (𝓝 (((z, (0 : C(S, ℂ))), M.rootedTreeSeries z))) :=
    ((tendsto_id.mono_left inf_le_left).prodMk_nhds tendsto_const_nhds).prodMk_nhds
      hseries
  have hglue : (fun w : ℂ => ψ (w, 0)) =ᶠ[
      𝓝[{w : ℂ | ‖w‖ < 1}] z] M.rootedTreeSeries := by
    filter_upwards [hpair.eventually hψuniq, self_mem_nhdsWithin]
      with w hwuniq hwI
    exact hwuniq.mp (M.rootedTreeSeries_residual_zero_openDisk hM hwI)
  obtain ⟨rGlue, hrGlue, hGlueBall⟩ := Metric.mem_nhdsWithin_iff.mp hglue

  let r : ℝ := min rJoint (min rUniq rGlue)
  have hr : 0 < r := lt_min hrJoint (lt_min hrUniq hrGlue)
  have hrJoint' : r ≤ rJoint := min_le_left _ _
  have hrUniq' : r ≤ rUniq :=
    (min_le_right rJoint (min rUniq rGlue)).trans (min_le_left _ _)
  have hrGlue' : r ≤ rGlue :=
    (min_le_right rJoint (min rUniq rGlue)).trans (min_le_right _ _)
  refine ⟨r, hr, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hq' : q ∈ Metric.ball (z, (0 : C(S, ℂ))) rJoint := by
      rw [← ball_prod_same]
      exact ⟨Metric.ball_subset_ball hrJoint' hq.1,
        Metric.ball_subset_ball hrJoint' hq.2⟩
    exact (hJointBall hq').1
  · intro q hq
    have hq' : q ∈ Metric.ball (z, (0 : C(S, ℂ))) rJoint := by
      rw [← ball_prod_same]
      exact ⟨Metric.ball_subset_ball hrJoint' hq.1,
        Metric.ball_subset_ball hrJoint' hq.2⟩
    exact (hJointBall hq').2
  · intro w hw hwI
    exact hGlueBall ⟨Metric.ball_subset_ball hrGlue' hw, hwI⟩
  · intro w hw
    exact hUniqBall (Metric.ball_subset_ball hrUniq' hw)

/-- The noncritical closed-disk germ can be shrunk to one explicit joint
product box carrying all interfaces needed by a finite compatible atlas. -/
theorem CompactBJRModel.exists_rootedTreeSeries_closedDisk_joint_germ_box
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    ∃ (ψ : ℂ × C(S, ℂ) → C(S, ℂ)) (r : ℝ),
      0 < r ∧
      ψ (z, 0) = M.rootedTreeSeries z ∧
      (∀ q ∈ Metric.ball z r ×ˢ Metric.ball (0 : C(S, ℂ)) r,
        AnalyticAt ℂ ψ q) ∧
      (∀ q ∈ Metric.ball z r ×ˢ Metric.ball (0 : C(S, ℂ)) r,
        TreeCritical.residual M (q, ψ q) = 0) ∧
      (∀ w ∈ Metric.ball z r, ‖w‖ < 1 →
        ψ (w, 0) = M.rootedTreeSeries w) ∧
      ∀ w ∈ Metric.ball z r,
        ∀ᶠ p in 𝓝 ((w, (0 : C(S, ℂ))), ψ (w, 0)),
          TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2 := by
  obtain ⟨ψ, hψa, hψz, hψres, hψuniq⟩ :=
    M.rootedTreeSeries_closedDisk_analytic_neighborhood hM hz hz1
  obtain ⟨r, hr, ha, hres, hglue, huniq⟩ :=
    M.exists_joint_germ_box_of_closedDisk_germ hM hz ψ
      hψa hψz hψres hψuniq
  exact ⟨ψ, r, hr, hψz, ha, hres, hglue, huniq⟩

end PerronWright
