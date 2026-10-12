import PerronWright.Enumeration.ProfileSimpleCycleFrechet
import PerronWright.Enumeration.ProfileSimpleCyclePowerSeries
import PerronWright.Analysis.RootedTreeClosedDiskPartial

/-!
# The direct simple-cycle series on the zero-field physical ray

This file joins the canonical compact-BJR fold profile to the direct
profile simple-cycle power series.  On a sufficiently short positive real
ray in the square-root coordinate, the fold profile is the genuine rooted
tree series and lies strictly inside the unit profile ball.  Consequently the
direct cycle series is represented by its proved formal multilinear series,
is analytic there, and has the independently constructed resolvent
continuation as its derivative.
-/

open Filter Topology PerronWright
open scoped Topology RightActions NNReal ENNReal

noncomputable section

namespace PerronWright.SimpleCyclePhysicalRayBridge

namespace MPR

export PerronWright.MarkedPathResolvent (profile profile_analytic)

end MPR

namespace MCS

export PerronWright.MarkedCycleSingularity (jointProfileVertical)

end MCS

namespace JS

export PerronWright.JointSimpleCycleEGF
  (profileSimpleCycleTerm profileSimpleCycleSeries
   profileSimpleCycleDerivative
   profileSimpleCycleDerivative_actual_eq_continuation)

end JS

namespace PS

export PerronWright.ProfileSimpleCyclePowerSeries
  (profileSimpleCycleFMS profileSimpleCycleFMS_hasSum_of_norm_lt_one
   profileSimpleCycleSeries_analyticOnNhd_unitBall)

end PS

namespace SC

export PerronWright.SimpleCycleResolventBridge
  (simpleCycleDerivativeContinuation)

end SC

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The zero-field fold profile as a function of the square-root coordinate. -/
private def profileRay (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (X : ℂ) : C(S, ℂ) :=
  MPR.profile M hM (0, X)

/-- The direct profile simple-cycle series restricted to the physical fold
coordinate. -/
private def simpleCycleRay (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (X : ℂ) : ℂ :=
  JS.profileSimpleCycleSeries M (profileRay M hM X)

/-- On one positive real square-root interval, the canonical fold profile is
the genuine rooted-tree profile, is strictly subcritical, and remains in the
analytic fold germ. -/
theorem exists_profileRay_physical_subcritical
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ X : ℝ, 0 < X → X < ε →
      profileRay M hM (X : ℂ) =
          M.rootedTreeSeries ((1 - X ^ 2 : ℝ) : ℂ) ∧
      ‖profileRay M hM (X : ℂ)‖ < 1 ∧
      AnalyticAt ℂ (MPR.profile M hM)
        ((0 : C(S, ℂ)), (X : ℂ)) := by
  obtain ⟨δ, hδ, hphysical⟩ :=
    TreeNormalizedFoldActivity.foldProfile_eq_rootedTreeSeries_real_near_one
      M hM
  have hprofileNear : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      AnalyticAt ℂ (MPR.profile M hM) q :=
    (MPR.profile_analytic M hM).eventually_analyticAt
  have hlineAt : AnalyticAt ℂ
      (fun X : ℂ => ((0 : C(S, ℂ)), X)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hprofileAlong : ∀ᶠ X : ℂ in 𝓝 0,
      AnalyticAt ℂ (MPR.profile M hM) ((0 : C(S, ℂ)), X) :=
    hlineAt.continuousAt.eventually hprofileNear
  obtain ⟨εa, hεa, hball⟩ :=
    Metric.eventually_nhds_iff.mp hprofileAlong
  let ε : ℝ := min δ (min 1 εa)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hδ (lt_min zero_lt_one hεa)
  refine ⟨ε, hε, ?_⟩
  intro X hX hXε
  have hXδ : X < δ := hXε.trans_le (min_le_left _ _)
  have hXone : X < 1 :=
    hXε.trans_le ((min_le_right δ (min 1 εa)).trans (min_le_left 1 εa))
  have hXεa : X < εa :=
    hXε.trans_le ((min_le_right δ (min 1 εa)).trans (min_le_right 1 εa))
  let w : ℝ := 1 - X ^ 2
  have hXsq_lt_one : X ^ 2 < 1 := by nlinarith
  have hw0 : 0 ≤ w := by dsimp [w]; linarith
  have hw1 : w < 1 := by
    dsimp [w]
    nlinarith [sq_pos_of_pos hX]
  have hXsq_lt_delta : X ^ 2 < δ := by
    have hXsq_lt_X : X ^ 2 < X := by nlinarith
    exact hXsq_lt_X.trans hXδ
  have hclose : |w - 1| < δ := by
    have hwsub : w - 1 = -(X ^ 2) := by dsimp [w]; ring
    rw [hwsub, abs_neg, abs_of_nonneg (sq_nonneg X)]
    exact hXsq_lt_delta
  have hsqrt : Real.sqrt (1 - w) = X := by
    have hone : 1 - w = X ^ 2 := by dsimp [w]; ring
    rw [hone, Real.sqrt_sq_eq_abs, abs_of_pos hX]
  have hprofileEq : profileRay M hM (X : ℂ) =
      M.rootedTreeSeries ((w : ℝ) : ℂ) := by
    have hseed := hphysical w hw0 hw1 hclose
    simpa only [profileRay, MPR.profile, hsqrt] using hseed
  have hwNorm : ‖((w : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    exact hw1.le
  have hwNe : ((w : ℝ) : ℂ) ≠ 1 := by
    exact_mod_cast (ne_of_lt hw1)
  have hsubRoot : ‖M.rootedTreeSeries ((w : ℝ) : ℂ)‖ < 1 :=
    M.rootedTreeSeries_norm_lt_one_of_closedDisk_ne_one
      hM hwNorm hwNe
  have hsub : ‖profileRay M hM (X : ℂ)‖ < 1 := by
    rw [hprofileEq]
    exact hsubRoot
  have hdist : dist (X : ℂ) 0 < εa := by
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hX]
    exact hXεa
  exact ⟨by simpa only [w] using hprofileEq, hsub, hball hdist⟩

/-- The direct cycle series on the positive zero-field physical ray is the
sum of its explicit Banach-space power series and is analytic.  Its complex
`X`-derivative is exactly the independently constructed marked-resolvent
continuation. -/
theorem exists_profileSimpleCycleSeries_physical_ray
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ X : ℝ, 0 < X → X < ε →
      profileRay M hM (X : ℂ) =
          M.rootedTreeSeries ((1 - X ^ 2 : ℝ) : ℂ) ∧
      HasSum
        (fun k : ℕ => PS.profileSimpleCycleFMS M k
          (fun _ => profileRay M hM (X : ℂ)))
        (simpleCycleRay M hM (X : ℂ)) ∧
      AnalyticAt ℂ (simpleCycleRay M hM) (X : ℂ) ∧
      HasDerivAt (simpleCycleRay M hM)
        (SC.simpleCycleDerivativeContinuation M hM
          ((0 : C(S, ℂ)), (X : ℂ))) (X : ℂ) := by
  obtain ⟨ε, hε, hdata⟩ := exists_profileRay_physical_subcritical M hM
  refine ⟨ε, hε, ?_⟩
  intro X hX hXε
  obtain ⟨hprofileEq, hsub, hprofileFull⟩ := hdata X hX hXε
  let tau : C(S, ℂ) := profileRay M hM (X : ℂ)
  have hsum : HasSum
      (fun k : ℕ => PS.profileSimpleCycleFMS M k (fun _ => tau))
      (JS.profileSimpleCycleSeries M tau) :=
    PS.profileSimpleCycleFMS_hasSum_of_norm_lt_one M hM tau hsub
  have hprofileSlice : AnalyticAt ℂ (profileRay M hM) (X : ℂ) := by
    have hline : AnalyticAt ℂ
        (fun Y : ℂ => ((0 : C(S, ℂ)), Y)) (X : ℂ) :=
      analyticAt_const.prod analyticAt_id
    exact hprofileFull.comp_of_eq hline rfl
  have htauMem : tau ∈ Metric.ball (0 : C(S, ℂ)) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, tau] using hsub
  have hcycleAt : AnalyticAt ℂ (JS.profileSimpleCycleSeries M) tau :=
    PS.profileSimpleCycleSeries_analyticOnNhd_unitBall M hM tau htauMem
  have hseriesAt : AnalyticAt ℂ (simpleCycleRay M hM) (X : ℂ) := by
    exact hcycleAt.comp_of_eq hprofileSlice rfl
  have hlineDeriv : HasDerivAt
      (fun Y : ℂ => ((0 : C(S, ℂ)), Y))
      ((0 : C(S, ℂ)), (1 : ℂ)) (X : ℂ) :=
    (hasDerivAt_const (X : ℂ) (0 : C(S, ℂ))).prodMk
      (hasDerivAt_id (X : ℂ))
  have hprofileDerivRaw :=
    hprofileFull.hasStrictFDerivAt.hasFDerivAt.comp_hasDerivAt
      (X : ℂ) hlineDeriv
  have hprofileDeriv : HasDerivAt (profileRay M hM)
      (MCS.jointProfileVertical M hM
        ((0 : C(S, ℂ)), (X : ℂ))) (X : ℂ) := by
    convert hprofileDerivRaw using 1 <;> rfl
  have hdirect :=
    ProfileSimpleCycleFrechet.profileSimpleCycleSeries_comp_hasDerivAt_of_norm_lt_one
      M hM hprofileDeriv hsub
  have hbridge :=
    JS.profileSimpleCycleDerivative_actual_eq_continuation M hM
      ((0 : C(S, ℂ)), (X : ℂ))
  have hderiv : HasDerivAt (simpleCycleRay M hM)
      (SC.simpleCycleDerivativeContinuation M hM
        ((0 : C(S, ℂ)), (X : ℂ))) (X : ℂ) := by
    exact hdirect.congr_deriv hbridge
  exact ⟨hprofileEq, by simpa only [tau, simpleCycleRay] using hsum,
    hseriesAt, hderiv⟩

end PerronWright.SimpleCyclePhysicalRayBridge
