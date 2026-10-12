import PerronWright.Analysis.FiniteIrreducibleNormalizedUnitAway
import PerronWright.Analysis.NormalizedClosedDiskFoldGluing

/-! Actual normalized closed-disk continuation for literal finite models.
The model-independent component geometry is reused without a B2 adapter. -/
open Filter Topology
open scoped Classical
noncomputable section
namespace PerronWright.FiniteIrreducibleNormalizedClosedDiskGluing
open PerronWright
open PerronWright.FiniteIrreducibleNormalizedFoldActivity
open PerronWright.FiniteIrreducibleNormalizedUnitAway
open PerronWright.TreeNormalizedClosedDiskGluing
variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The production closed-disk chart, pulled back to normalized activity,
with exactly the interfaces used by the fold-overlap argument. -/
theorem exists_normalized_rootedTreeSeries_joint_analytic_continuation_closedDisk_away
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (U : Set ℂ) (ε : ℝ)
        (Ψ : ℂ × C(S, ℂ) → C(S, ℂ)),
      IsOpen U ∧
      closedUnitDiskAway δ ⊆ U ∧
      0 < ε ∧
      IsOpen (normalizedUnitAwayDomain M hM U ε) ∧
      AnalyticOnNhd ℂ (activityMap M hM)
        (Set.univ ×ˢ Metric.ball (0 : C(S, ℂ)) ε) ∧
      AnalyticOnNhd ℂ (normalizedUnitAwayProfile M hM Ψ)
        (normalizedUnitAwayDomain M hM U ε) ∧
      (∀ q ∈ normalizedUnitAwayDomain M hM U ε,
        FiniteIrreducibleRadiusResponse.radius M hM q.2 ≠ 0 ∧
        TreeCritical.residual M.bjrModel
          (activityMap M hM q, normalizedUnitAwayProfile M hM Ψ q) = 0) ∧
      (∀ w ∈ U, ‖w‖ < 1 →
        normalizedUnitAwayProfile M hM Ψ (w, 0) =
          M.bjrModel.rootedTreeSeries w) ∧
      ∀ w ∈ U,
        ∀ᶠ p in nhds
          (((w, (0 : C(S, ℂ))), normalizedUnitAwayProfile M hM Ψ (w, 0))),
          TreeCritical.residual M.bjrModel (activityMap M hM p.1, p.2) = 0 ↔
            normalizedUnitAwayProfile M hM Ψ p.1 = p.2 := by
  have hKdisk : closedUnitDiskAway δ ⊆ Metric.closedBall (0 : ℂ) 1 :=
    fun _ hw => hw.1
  have hnotone : (1 : ℂ) ∉ closedUnitDiskAway δ := by
    intro hOne
    have haway := hOne.2
    change δ ≤ dist (1 : ℂ) 1 at haway
    rw [dist_self] at haway
    exact (not_le_of_gt hδ) haway
  obtain ⟨U, εClosed, Ψ, hU, hKU, hεClosed, hΨ, hres,
      hinside, huniq⟩ :=
    M.exists_rootedTreeSeries_joint_analytic_continuation_near_compact_closedDisk
      hM (isCompact_closedUnitDiskAway δ) hKdisk hnotone
  obtain ⟨εActivity, hεActivity, hActivity, hRadiusNe⟩ :=
    exists_activityMap_analytic_field_ball M hM
  let ε : ℝ := min εClosed εActivity
  have hε : 0 < ε := lt_min hεClosed hεActivity
  have hActivity' : AnalyticOnNhd ℂ (activityMap M hM)
      (Set.univ ×ˢ Metric.ball (0 : C(S, ℂ)) ε) := by
    intro q hq
    exact hActivity q ⟨Set.mem_univ _,
      Metric.ball_subset_ball (min_le_right εClosed εActivity) hq.2⟩
  have hΨ' : AnalyticOnNhd ℂ Ψ
      (U ×ˢ Metric.ball (0 : C(S, ℂ)) ε) := by
    intro q hq
    exact hΨ q ⟨hq.1,
      Metric.ball_subset_ball (min_le_left εClosed εActivity) hq.2⟩
  have hDopen := isOpen_normalizedUnitAwayDomain M hM hU hActivity'
  have hProfile := normalizedUnitAwayProfile_analytic M hM hActivity' hΨ'
  refine ⟨U, ε, Ψ, hU, hKU, hε, hDopen, hActivity', hProfile,
    ?_, ?_, ?_⟩
  · intro q hq
    have htarget : activityMap M hM q ∈
        U ×ˢ Metric.ball (0 : C(S, ℂ)) ε := hq
    have hg : q.2 ∈ Metric.ball (0 : C(S, ℂ)) ε := by
      simpa only [activityMap] using htarget.2
    refine ⟨hRadiusNe q.2
      (Metric.ball_subset_ball (min_le_right εClosed εActivity) hg), ?_⟩
    exact hres (activityMap M hM q)
      ⟨htarget.1,
        Metric.ball_subset_ball (min_le_left εClosed εActivity) htarget.2⟩
  · intro w hwU hwNorm
    simpa only [normalizedUnitAwayProfile, activityMap_zeroField] using
      hinside w hwU hwNorm
  · intro w hwU
    have h0 : (0 : C(S, ℂ)) ∈ Metric.ball 0 ε :=
      Metric.mem_ball_self hε
    exact normalizedUnitAwayProfile_local_residual_uniqueness M hM Ψ w
      (hActivity' (w, 0) ⟨Set.mem_univ _, h0⟩).continuousAt
      (huniq w hwU)

end PerronWright.FiniteIrreducibleNormalizedClosedDiskGluing
