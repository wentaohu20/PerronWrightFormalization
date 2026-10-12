import PerronWright.Analysis.NormalizedFoldActivity
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Normalized pullback of the joint unit-away continuation

The unit-away continuation is constructed in the actual activity variable
`z`.  This file pulls it back through the proved analytic map
`(w,g) ↦ (rho(g) * w,g)`.  No geometric shape is imposed on the open
continuation set `U`: the uniform normalized annular neighborhood is extracted
from its proved containment of a compact unit-circle arc.
-/

open Filter Topology
open scoped Classical

noncomputable section

namespace PerronWright.TreeNormalizedUnitAway

open PerronWright
open PerronWright.TreeNormalizedFoldActivity

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The exact pullback of an actual-activity product under
`(w,g) ↦ (rho(g) * w,g)`. -/
def normalizedUnitAwayDomain (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (U : Set ℂ) (ε : ℝ) :
    Set (ℂ × C(S, ℂ)) :=
  activityMap M hM ⁻¹' (U ×ˢ Metric.ball (0 : C(S, ℂ)) ε)

/-- The actual unit-away profile expressed in normalized coordinates. -/
def normalizedUnitAwayProfile (M : CompactBJRModel S)
    (hM : M.IsRegularCritical)
    (Ψ : ℂ × C(S, ℂ) → C(S, ℂ))
    (q : ℂ × C(S, ℂ)) : C(S, ℂ) :=
  Ψ (activityMap M hM q)

/-- The compact normalized unit-circle arc separated from the critical point
by the metric cutoff `delta`. -/
def normalizedUnitArc (δ : ℝ) : Set ℂ :=
  Metric.sphere (0 : ℂ) 1 ∩ {w : ℂ | δ ≤ dist w 1}

theorem isCompact_normalizedUnitArc (δ : ℝ) :
    IsCompact (normalizedUnitArc δ) := by
  have haway : IsClosed {w : ℂ | δ ≤ dist w 1} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  exact (isCompact_sphere (0 : ℂ) 1).inter_right haway

/-- Analyticity of the activity map on the relevant field cylinder makes the
exact pullback of an open actual-activity product open. -/
theorem isOpen_normalizedUnitAwayDomain
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {U : Set ℂ} {ε : ℝ} (hU : IsOpen U)
    (hActivity : AnalyticOnNhd ℂ (activityMap M hM)
      (Set.univ ×ˢ Metric.ball (0 : C(S, ℂ)) ε)) :
    IsOpen (normalizedUnitAwayDomain M hM U ε) := by
  have hcylinder : IsOpen
      (Set.univ ×ˢ Metric.ball (0 : C(S, ℂ)) ε) :=
    (isOpen_univ : IsOpen (Set.univ : Set ℂ)).prod Metric.isOpen_ball
  have htarget : IsOpen
      (U ×ˢ Metric.ball (0 : C(S, ℂ)) ε) :=
    hU.prod Metric.isOpen_ball
  have hopen := hActivity.continuousOn.isOpen_inter_preimage
    hcylinder htarget
  have heq : normalizedUnitAwayDomain M hM U ε =
      (Set.univ ×ˢ Metric.ball (0 : C(S, ℂ)) ε) ∩
        activityMap M hM ⁻¹'
          (U ×ˢ Metric.ball (0 : C(S, ℂ)) ε) := by
    ext q
    simp only [normalizedUnitAwayDomain, Set.mem_preimage,
      Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, activityMap]
    tauto
  rw [heq]
  exact hopen

/-- Composition of the two genuine analytic maps on the exact pullback. -/
theorem normalizedUnitAwayProfile_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {U : Set ℂ} {ε : ℝ}
    {Ψ : ℂ × C(S, ℂ) → C(S, ℂ)}
    (hActivity : AnalyticOnNhd ℂ (activityMap M hM)
      (Set.univ ×ˢ Metric.ball (0 : C(S, ℂ)) ε))
    (hΨ : AnalyticOnNhd ℂ Ψ
      (U ×ˢ Metric.ball (0 : C(S, ℂ)) ε)) :
    AnalyticOnNhd ℂ (normalizedUnitAwayProfile M hM Ψ)
      (normalizedUnitAwayDomain M hM U ε) := by
  intro q hq
  have htarget : activityMap M hM q ∈
      U ×ˢ Metric.ball (0 : C(S, ℂ)) ε := hq
  have hg : q.2 ∈ Metric.ball (0 : C(S, ℂ)) ε := by
    simpa only [activityMap] using htarget.2
  exact (hΨ _ htarget).comp_of_eq
    (hActivity q ⟨Set.mem_univ _, hg⟩) rfl

/-- Local residual uniqueness pulls back through the normalized activity map
using continuity only; no local inverse of the activity map is needed. -/
theorem normalizedUnitAwayProfile_local_residual_uniqueness
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (Ψ : ℂ × C(S, ℂ) → C(S, ℂ)) (w : ℂ)
    (hActivity : ContinuousAt (activityMap M hM)
      (w, (0 : C(S, ℂ))))
    (huniq : ∀ᶠ p in nhds
      (((w, (0 : C(S, ℂ))), Ψ (w, 0))),
      TreeCritical.residual M p = 0 ↔ Ψ p.1 = p.2) :
    ∀ᶠ p in nhds
      (((w, (0 : C(S, ℂ))), normalizedUnitAwayProfile M hM Ψ (w, 0))),
      TreeCritical.residual M (activityMap M hM p.1, p.2) = 0 ↔
        normalizedUnitAwayProfile M hM Ψ p.1 = p.2 := by
  have hbase : normalizedUnitAwayProfile M hM Ψ (w, 0) = Ψ (w, 0) := by
    simp only [normalizedUnitAwayProfile, activityMap_zeroField]
  rw [hbase]
  have hfst : Tendsto
      (fun p : ((ℂ × C(S, ℂ)) × C(S, ℂ)) => p.1)
      (nhds (((w, (0 : C(S, ℂ))), Ψ (w, 0))))
      (nhds (w, (0 : C(S, ℂ)))) := continuousAt_fst
  have hsnd : Tendsto
      (fun p : ((ℂ × C(S, ℂ)) × C(S, ℂ)) => p.2)
      (nhds (((w, (0 : C(S, ℂ))), Ψ (w, 0))))
      (nhds (Ψ (w, 0))) := continuousAt_snd
  have hmap : Tendsto
      (fun p : ((ℂ × C(S, ℂ)) × C(S, ℂ)) =>
        (activityMap M hM p.1, p.2))
      (nhds (((w, (0 : C(S, ℂ))), Ψ (w, 0))))
      (nhds (((w, (0 : C(S, ℂ))), Ψ (w, 0)))) := by
    have h := (hActivity.tendsto.comp hfst).prodMk_nhds hsnd
    simpa only [Function.comp_apply, activityMap_zeroField] using h
  filter_upwards [hmap.eventually huniq] with p hp
  simpa only [normalizedUnitAwayProfile] using hp

/-- The field-uniform unit-away continuation pulled back to normalized
activity.  The same field radius controls both analytic maps and keeps the
critical radius nonzero. -/
theorem exists_normalized_rootedTreeSeries_joint_analytic_continuation_unit_away
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (U : Set ℂ) (ε : ℝ)
        (Ψ : ℂ × C(S, ℂ) → C(S, ℂ)),
      IsOpen U ∧
      normalizedUnitArc δ ⊆ U ∧
      0 < ε ∧
      IsOpen (normalizedUnitAwayDomain M hM U ε) ∧
      AnalyticOnNhd ℂ (activityMap M hM)
        (Set.univ ×ˢ Metric.ball (0 : C(S, ℂ)) ε) ∧
      AnalyticOnNhd ℂ (normalizedUnitAwayProfile M hM Ψ)
        (normalizedUnitAwayDomain M hM U ε) ∧
      (∀ q ∈ normalizedUnitAwayDomain M hM U ε,
        RadiusResponse.radius M hM q.2 ≠ 0 ∧
        TreeCritical.residual M
          (activityMap M hM q, normalizedUnitAwayProfile M hM Ψ q) = 0) ∧
      (∀ w ∈ U, ‖w‖ < 1 →
        normalizedUnitAwayProfile M hM Ψ (w, 0) =
          M.rootedTreeSeries w) ∧
      ∀ w ∈ U,
        ∀ᶠ p in nhds
          (((w, (0 : C(S, ℂ))), normalizedUnitAwayProfile M hM Ψ (w, 0))),
          TreeCritical.residual M (activityMap M hM p.1, p.2) = 0 ↔
            normalizedUnitAwayProfile M hM Ψ p.1 = p.2 := by
  obtain ⟨U, εUnit, Ψ, hU, hArc, hεUnit, hΨ, hres, hinside, huniq⟩ :=
    M.exists_rootedTreeSeries_joint_analytic_continuation_unit_away hM hδ
  obtain ⟨εActivity, hεActivity, hActivity, hRadiusNe⟩ :=
    exists_activityMap_analytic_field_ball M hM
  let ε : ℝ := min εUnit εActivity
  have hε : 0 < ε := lt_min hεUnit hεActivity
  have hActivity' : AnalyticOnNhd ℂ (activityMap M hM)
      (Set.univ ×ˢ Metric.ball (0 : C(S, ℂ)) ε) := by
    intro q hq
    exact hActivity q ⟨Set.mem_univ _,
      Metric.ball_subset_ball (min_le_right εUnit εActivity) hq.2⟩
  have hΨ' : AnalyticOnNhd ℂ Ψ
      (U ×ˢ Metric.ball (0 : C(S, ℂ)) ε) := by
    intro q hq
    exact hΨ q ⟨hq.1,
      Metric.ball_subset_ball (min_le_left εUnit εActivity) hq.2⟩
  have hDopen := isOpen_normalizedUnitAwayDomain M hM hU hActivity'
  have hProfile := normalizedUnitAwayProfile_analytic M hM hActivity' hΨ'
  refine ⟨U, ε, Ψ, hU, hArc, hε, hDopen, hActivity', hProfile,
    ?_, ?_, ?_⟩
  · intro q hq
    have htarget : activityMap M hM q ∈
        U ×ˢ Metric.ball (0 : C(S, ℂ)) ε := hq
    have hg : q.2 ∈ Metric.ball (0 : C(S, ℂ)) ε := by
      simpa only [activityMap] using htarget.2
    refine ⟨hRadiusNe q.2
      (Metric.ball_subset_ball (min_le_right εUnit εActivity) hg), ?_⟩
    exact hres (activityMap M hM q)
      ⟨htarget.1,
        Metric.ball_subset_ball (min_le_left εUnit εActivity) htarget.2⟩
  · intro w hwU hwNorm
    simpa only [normalizedUnitAwayProfile, activityMap_zeroField] using
      hinside w hwU hwNorm
  · intro w hwU
    have h0 : (0 : C(S, ℂ)) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
    exact normalizedUnitAwayProfile_local_residual_uniqueness M hM Ψ w
      (hActivity' (w, 0) ⟨Set.mem_univ _, h0⟩).continuousAt
      (huniq w hwU)

/-- Compactness of the unit arc and openness of the exact pullback produce a
single normalized annular thickness and a single field radius.  No shape of
`U` beyond its proved containment of the compact arc is used. -/
theorem exists_uniform_normalized_unitArc_thickening
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) {U : Set ℂ}
    (hArc : normalizedUnitArc δ ⊆ U)
    (hDopen : IsOpen (normalizedUnitAwayDomain M hM U ε)) :
    ∃ r : ℝ, 0 < r ∧ r < δ / 2 ∧
      Metric.thickening r (normalizedUnitArc δ) ×ˢ
          Metric.ball (0 : C(S, ℂ)) r ⊆
        normalizedUnitAwayDomain M hM U ε := by
  let K : Set (ℂ × C(S, ℂ)) :=
    normalizedUnitArc δ ×ˢ {(0 : C(S, ℂ))}
  have hKcompact : IsCompact K :=
    (isCompact_normalizedUnitArc δ).prod isCompact_singleton
  have hKsub : K ⊆ normalizedUnitAwayDomain M hM U ε := by
    rintro ⟨w, g⟩ ⟨hw, hg⟩
    have hg0 : g = 0 := by simpa only [Set.mem_singleton_iff] using hg
    subst g
    change activityMap M hM (w, 0) ∈
      U ×ˢ Metric.ball (0 : C(S, ℂ)) ε
    rw [activityMap_zeroField]
    exact ⟨hArc hw, Metric.mem_ball_self hε⟩
  obtain ⟨t, ht, htSub⟩ :=
    hKcompact.exists_thickening_subset_open hDopen hKsub
  let r : ℝ := min t (δ / 4)
  have hr : 0 < r := lt_min ht (by positivity)
  have hrδ : r < δ / 2 :=
    (min_le_right t (δ / 4)).trans_lt (by linarith)
  refine ⟨r, hr, hrδ, ?_⟩
  intro q hq
  apply htSub
  obtain ⟨w₀, hw₀, hdistw⟩ := Metric.mem_thickening_iff.mp hq.1
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(w₀, (0 : C(S, ℂ))), ⟨hw₀, Set.mem_singleton _⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨hdistw.trans_le (min_le_left t (δ / 4)),
    (Metric.mem_ball.mp hq.2).trans_le (min_le_left t (δ / 4))⟩

end PerronWright.TreeNormalizedUnitAway
