import PerronWright.Analysis.FiniteIrreducibleFieldComplexRadius

/-!
# Actual complex-field tree series on a common global Delta product

The analytic profile is constructed by the actual closed-disk implicit
atlas and the actual finite fold. Its Taylor coefficients are the literal
labelled-tree coefficients, and the exact radii are proved rather than
included as continuation hypotheses. Bipartite kernels remain admissible.
-/

open Filter Topology
open scoped Classical Topology ENNReal NNReal
noncomputable section

namespace PerronWright.FiniteIrreducibleFieldDeltaContinuation

open PerronWright
open PerronWright.FiniteIrreducibleNormalizedFoldActivity
open PerronWright.FiniteIrreducibleFieldRootedTree

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The normalized formal series is the same actual labelled-tree series
evaluated at the rescaled activity, even outside the convergence ball. -/
theorem normalizedFMS_sum_eq_fieldFMS_sum (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (g : C(S, ℂ)) (w : ℂ) :
    (normalizedFMS M hM g).sum w =
      (M.fieldFMS g).sum (FiniteIrreducibleRadiusResponse.radius M hM g * w) := by
  simp only [normalizedFMS, fms_eq_fieldFMS, FormalMultilinearSeries.sum,
    FormalMultilinearSeries.compContinuousLinearMap_apply,
    Function.comp_def, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- An actual normalized Delta-profile is the sum of the genuine normalized
series throughout the open unit disk, not merely near the origin. -/
theorem normalizedFMS_sum_eq_profile_on_unitBall
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {eta s : ℝ} {Theta : ℂ × C(S, ℂ) → C(S, ℂ)}
    (heta : 0 < eta) (hs : 0 < s)
    (hTheta : AnalyticOnNhd ℂ Theta
      (Transfer.cartesianDelta eta 0 ×ˢ Metric.ball (0 : C(S, ℂ)) s))
    (hData : ∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s,
      FiniteIrreducibleRadiusResponse.radius M hM q.2 ≠ 0 ∧
        TreeCritical.residual M.bjrModel (activityMap M hM q, Theta q) = 0)
    {g : C(S, ℂ)} (hg : g ∈ Metric.ball 0 s)
    (hrad : (normalizedFMS M hM g).radius = 1) :
    Set.EqOn (normalizedFMS M hM g).sum (fun w : ℂ ↦ Theta (w, g))
      (Metric.ball (0 : ℂ) 1) := by
  let p := normalizedFMS M hM g
  have hp : HasFPowerSeriesAt (fun w : ℂ ↦ Theta (w, g)) p 0 :=
    normalizedFMS_hasFPowerSeriesAt_of_cartesianDelta_profile
      M hM heta hs hTheta hData hg
  have hpos : 0 < p.radius := by rw [show p.radius = 1 from hrad]; norm_num
  have hpSum : HasFPowerSeriesAt p.sum p 0 :=
    (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  have hnear : p.sum =ᶠ[nhds (0 : ℂ)] fun w : ℂ ↦ Theta (w, g) := by
    filter_upwards [hpSum.eventually_hasSum_sub, hp.eventually_hasSum_sub]
      with w hsum hprofile
    exact hsum.unique hprofile
  have hsum : AnalyticOnNhd ℂ p.sum (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    apply p.analyticOnNhd w
    rw [show p.radius = 1 from hrad, ← ENNReal.coe_one, Metric.eball_coe]
    simpa only [NNReal.coe_one] using hw
  have hprofile : AnalyticOnNhd ℂ (fun w : ℂ ↦ Theta (w, g))
      (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    exact (hTheta (w, g) ⟨Transfer.unit_ball_subset_cartesianDelta heta hw, hg⟩).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  exact hsum.eqOn_of_preconnected_of_eventuallyEq hprofile
    (convex_ball (0 : ℂ) 1).isPreconnected
    (Metric.mem_ball_self zero_lt_one) hnear

/-- One common global Cartesian Delta times one common complex-field ball
carries the actual rooted-tree continuation, the exact radius, the actual
tree equation and the genuine local fold identity. No continuation or
radius premise is required beyond the literal finite critical model. -/
theorem exists_actual_field_tree_globalDelta
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ (eta r epsilon : ℝ) (Theta : ℂ × C(S, ℂ) → C(S, ℂ)),
      0 < eta ∧ 0 < r ∧ 0 < epsilon ∧
      AnalyticOnNhd ℂ (activityMap M hM)
        (Transfer.cartesianDelta eta 0 ×ˢ Metric.ball (0 : C(S, ℂ)) epsilon) ∧
      AnalyticOnNhd ℂ Theta
        (Transfer.cartesianDelta eta 0 ×ˢ Metric.ball (0 : C(S, ℂ)) epsilon) ∧
      (∀ q ∈ Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) epsilon,
        FiniteIrreducibleRadiusResponse.radius M hM q.2 ≠ 0 ∧
          TreeCritical.residual M.bjrModel (activityMap M hM q, Theta q) = 0) ∧
      Set.EqOn Theta (normalizedFoldProfile M hM)
        (localCartesianDelta 1 0 r ×ˢ Metric.ball (0 : C(S, ℂ)) epsilon) ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) epsilon,
        (normalizedFMS M hM g).radius = 1 ∧
        (M.fieldFMS g).radius = ‖FiniteIrreducibleRadiusResponse.radius M hM g‖ₑ ∧
        ∀ w : ℂ, ‖w‖ < 1 →
          (M.fieldFMS g).sum (FiniteIrreducibleRadiusResponse.radius M hM g * w) =
            Theta (w, g) := by
  obtain ⟨eta, r, s, Theta, heta, hr, hs, hActivity, hTheta,
      hData, hFold, -⟩ :=
    FiniteIrreducibleNormalizedDeltaProfile.exists_uniform_normalized_cartesianDelta_profile_of_terminal
      M hM
  obtain ⟨e, he, hRadius⟩ := normalizedFMS_radius_eq_one_eventually M hM
  let epsilon : ℝ := min s e
  have hepsilon : 0 < epsilon := lt_min hs he
  have hsub : Metric.ball (0 : C(S, ℂ)) epsilon ⊆ Metric.ball 0 s :=
    Metric.ball_subset_ball (min_le_left s e)
  refine ⟨eta, r, epsilon, Theta, heta, hr, hepsilon, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun q hq ↦ hActivity q ⟨hq.1, hsub hq.2⟩
  · exact fun q hq ↦ hTheta q ⟨hq.1, hsub hq.2⟩
  · exact fun q hq ↦ hData q ⟨hq.1, hsub hq.2⟩
  · exact fun q hq ↦ hFold ⟨hq.1, hsub hq.2⟩
  · intro g hg
    have hgs := hsub hg
    have hrad := hRadius g (Metric.ball_subset_ball (min_le_right s e) hg)
    have h0 : ((0 : ℂ), g) ∈ Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s :=
      ⟨Transfer.unit_ball_subset_cartesianDelta heta
        (Metric.mem_ball_self zero_lt_one), hgs⟩
    have hrho := (hData (0, g) h0).1
    refine ⟨hrad, ?_, ?_⟩
    · simpa only [fms_eq_fieldFMS] using
        fms_radius_eq_of_normalized_radius_eq_one M hM hrho hrad
    · intro w hw
      rw [← normalizedFMS_sum_eq_fieldFMS_sum]
      apply normalizedFMS_sum_eq_profile_on_unitBall M hM heta hs hTheta hData hgs hrad
      simpa only [Metric.mem_ball, dist_zero_right] using hw

end PerronWright.FiniteIrreducibleFieldDeltaContinuation
