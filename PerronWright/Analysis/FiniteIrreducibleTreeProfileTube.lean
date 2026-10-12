import PerronWright.Analysis.FiniteIrreducibleFieldDeltaContinuation
import PerronWright.Enumeration.ZeroFieldUnicyclicDeltaContinuation

/-! Uniform strictly subcritical product tubes for the actual finite rooted-tree
profile. Compactness is applied only to the closed-disk zero-field spine, never
to a complex field ball. Actual positive first and second tree coefficients
break phase alignment, including for bipartite irreducible matrices. -/

open Filter Topology PerronWright Set
open scoped Classical Topology BigOperators
noncomputable section
namespace PerronWright.FiniteIrreducibleTreeProfileTube
export PerronWright.ZeroFieldUnicyclicDeltaContinuation
  (closedUnitDiskAway_subset_cartesianDelta)
variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

theorem zeroFieldProfile_eq_rootedTreeSeries_on_closedUnitDiskAway
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {eta delta : ℝ} {theta : ℂ → C(S, ℂ)}
    (heta : 0 < eta) (hdelta : 0 < delta)
    (htheta : AnalyticOnNhd ℂ theta (Transfer.cartesianDelta eta 0))
    (hinside : Set.EqOn theta M.bjrModel.rootedTreeSeries
      (Metric.ball (0 : ℂ) 1)) :
    Set.EqOn theta M.bjrModel.rootedTreeSeries
      (TreeNormalizedClosedDiskGluing.closedUnitDiskAway delta) := by
  let D : Set ℂ := Transfer.cartesianDelta eta 0
  let B : Set ℂ := Metric.ball (0 : ℂ) 1
  let C : Set ℂ := Metric.closedBall (0 : ℂ) 1
  have hBsubD : B ⊆ D := Transfer.unit_ball_subset_cartesianDelta heta
  have hDCsub : D ∩ C ⊆ closure (D ∩ B) := by
    intro w hw
    apply (Transfer.isOpen_cartesianDelta eta 0).inter_closure
    refine ⟨hw.1, ?_⟩
    have hwC : w ∈ Metric.closedBall (0 : ℂ) 1 := hw.2
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hwC
    exact hwC
  have hthetaCont : ContinuousOn theta (D ∩ C) :=
    htheta.continuousOn.mono inter_subset_left
  have hrootCont : ContinuousOn M.bjrModel.rootedTreeSeries (D ∩ C) := by
    apply (M.rootedTreeSeries_continuousOn_closedDisk hM).mono
    intro w hw
    change ‖w‖ ≤ 1
    simpa only [C, Metric.mem_closedBall, dist_zero_right] using hw.2
  have hEqDC : Set.EqOn theta M.bjrModel.rootedTreeSeries (D ∩ C) := by
    apply Set.EqOn.of_subset_closure
      (s := D ∩ B) (t := D ∩ C)
    · intro w hw
      exact hinside hw.2
    · exact hthetaCont
    · exact hrootCont
    · intro w hw
      exact ⟨hw.1, Metric.ball_subset_closedBall hw.2⟩
    · exact hDCsub
  intro w hw
  exact hEqDC ⟨closedUnitDiskAway_subset_cartesianDelta heta hdelta hw,
    hw.1⟩

theorem exists_uniform_profile_unitBall_tube
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {eta s delta : ℝ}
    {Theta : ℂ × C(S, ℂ) → C(S, ℂ)}
    (heta : 0 < eta) (hs : 0 < s)
    (hdelta : 0 < delta)
    (hTheta : AnalyticOnNhd ℂ Theta
      (Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s))
    (hInside : Set.EqOn (fun w : ℂ ↦ Theta (w, 0))
      M.bjrModel.rootedTreeSeries (Metric.ball (0 : ℂ) 1)) :
    ∃ t : ℝ, 0 < t ∧
      let K :=
        TreeNormalizedClosedDiskGluing.closedUnitDiskAway delta
      Metric.thickening t K ×ˢ
          Metric.ball (0 : C(S, ℂ)) t ⊆
        Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s ∧
      ∀ q ∈ Metric.thickening t K ×ˢ
          Metric.ball (0 : C(S, ℂ)) t,
        ‖Theta q‖ < 1 := by
  let K : Set ℂ :=
    TreeNormalizedClosedDiskGluing.closedUnitDiskAway delta
  let D : Set (ℂ × C(S, ℂ)) :=
    Transfer.cartesianDelta eta 0 ×ˢ
      Metric.ball (0 : C(S, ℂ)) s
  let V : Set (ℂ × C(S, ℂ)) :=
    D ∩ Theta ⁻¹' Metric.ball (0 : C(S, ℂ)) 1
  let K₀ : Set (ℂ × C(S, ℂ)) :=
    K ×ˢ {(0 : C(S, ℂ))}
  have hDopen : IsOpen D :=
    (Transfer.isOpen_cartesianDelta eta 0).prod Metric.isOpen_ball
  have hVopen : IsOpen V := by
    exact hTheta.continuousOn.isOpen_inter_preimage
      hDopen Metric.isOpen_ball
  have hKcompact : IsCompact K :=
    TreeNormalizedClosedDiskGluing.isCompact_closedUnitDiskAway delta
  have hK₀compact : IsCompact K₀ :=
    hKcompact.prod isCompact_singleton
  let theta : ℂ → C(S, ℂ) := fun w ↦ Theta (w, 0)
  have htheta : AnalyticOnNhd ℂ theta
      (Transfer.cartesianDelta eta 0) := by
    intro w hw
    have hq : (w, (0 : C(S, ℂ))) ∈ D :=
      ⟨hw, Metric.mem_ball_self hs⟩
    exact (hTheta (w, 0) hq).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  have hthetaK : Set.EqOn theta M.bjrModel.rootedTreeSeries K := by
    simpa only [theta, K] using
      (zeroFieldProfile_eq_rootedTreeSeries_on_closedUnitDiskAway
        M hM heta hdelta htheta hInside)
  have hK₀sub : K₀ ⊆ V := by
    rintro ⟨w, g⟩ ⟨hw, hg⟩
    have hg0 : g = 0 := by
      simpa only [Set.mem_singleton_iff] using hg
    subst g
    have hwDelta : w ∈ Transfer.cartesianDelta eta 0 :=
      closedUnitDiskAway_subset_cartesianDelta heta hdelta hw
    have hwne : w ≠ 1 := by
      intro hw1
      subst w
      have haway := hw.2
      change delta ≤ dist (1 : ℂ) 1 at haway
      rw [dist_self] at haway
      exact (not_le_of_gt hdelta) haway
    have hrootNorm : ‖M.bjrModel.rootedTreeSeries w‖ < 1 :=
      M.rootedTreeSeries_norm_lt_one_of_closedDisk_ne_one hM
        (by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1)
        hwne
    refine ⟨⟨hwDelta, Metric.mem_ball_self hs⟩, ?_⟩
    change Theta (w, 0) ∈ Metric.ball (0 : C(S, ℂ)) 1
    change ‖theta w‖ < 1
    rw [hthetaK hw]
    exact hrootNorm
  obtain ⟨t₀, ht₀, ht₀Sub⟩ :=
    hK₀compact.exists_thickening_subset_open hVopen hK₀sub
  let t : ℝ := t₀ / 2
  have ht : 0 < t := half_pos ht₀
  have htLe : t ≤ t₀ := by
    dsimp only [t]
    linarith
  have hTubeSubThickening :
      Metric.thickening t K ×ˢ
          Metric.ball (0 : C(S, ℂ)) t ⊆
        Metric.thickening t₀ K₀ := by
    intro q hq
    obtain ⟨w₀, hw₀, hdistw⟩ := Metric.mem_thickening_iff.mp hq.1
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(w₀, (0 : C(S, ℂ))), ⟨hw₀, Set.mem_singleton _⟩, ?_⟩
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hdistw.trans_le htLe,
      (Metric.mem_ball.mp hq.2).trans_le htLe⟩
  have hTubeSubV :
      Metric.thickening t K ×ˢ
          Metric.ball (0 : C(S, ℂ)) t ⊆ V :=
    hTubeSubThickening.trans ht₀Sub
  refine ⟨t, ht, ?_, ?_⟩
  · intro q hq
    exact (hTubeSubV hq).1
  · intro q hq
    have hball := (hTubeSubV hq).2
    change Theta q ∈ Metric.ball (0 : C(S, ℂ)) 1 at hball
    simpa only [Metric.mem_ball, dist_zero_right] using hball


end PerronWright.FiniteIrreducibleTreeProfileTube
