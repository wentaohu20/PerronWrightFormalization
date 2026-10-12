import PerronWright.Analysis.FiniteIrreducibleFieldUnicyclicLocalBridge
import PerronWright.Enumeration.ZeroFieldUnicyclicDeltaContinuation
import PerronWright.Analysis.FiniteIrreducibleProfileSimpleCyclePowerSeries
import PerronWright.Analysis.FiniteIrreducibleTreeProfileTube
import PerronWright.Analysis.FiniteIrreducibleProfileSimpleCycleFrechet
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Joint Cartesian-Delta continuation for the complex-field unicyclic EGF

This file first constructs the global-away chart needed for the joint
unicyclic continuation.  The only compact set used is the zero-field
`w`-spine `K × {0}`.  A product thickening of that spine supplies one
common (noncompact) complex field ball on which the normalized tree profile
remains in the unit profile ball.  The direct simple-cycle functional is
therefore jointly analytic on the resulting away product.

The away chart is then glued to the local logarithmic primitive without a
determinant.  A single real activity belongs to every relevant overlap
component in a larger collar.  It fixes the field-dependent additive
constant, while equality of the two marked-cycle derivatives propagates the
normalization across each component.  This produces a genuine jointly
analytic scalar continuation and retains the literal normalized graph EGF
as its Taylor germ at the origin.
-/

open Filter Topology PerronWright Set
open scoped Classical Topology

noncomputable section

namespace PerronWright.FiniteIrreducibleFieldUnicyclicGlobalContinuation

namespace Local

export PerronWright.FiniteIrreducibleFieldUnicyclicLocalBridge
  (normalizedFieldUnicyclicFMS
   normalizedFieldUnicyclicFMS_hasFPowerSeriesAt_of_global_profile)

end Local

namespace PS

export PerronWright.FiniteIrreducibleProfileSimpleCyclePowerSeries
  (profileSimpleCycleSeries_analyticOnNhd_unitBall)

end PS

namespace JS

export PerronWright.JointSimpleCycleEGF
  (profileSimpleCycleSeries profileSimpleCycleDerivative)
export PerronWright.FiniteIrreducibleJointSimpleCycleEGF
  (profileSimpleCycleDerivative_actual_eq_continuation)

end JS

namespace PF

export PerronWright.FiniteIrreducibleProfileSimpleCycleFrechet
  (profileSimpleCycleSeries_comp_hasDerivAt_of_norm_lt_one)

end PF

namespace SC

export PerronWright.FiniteIrreducibleSimpleCycleResolventBridge
  (simpleCycleDerivativeContinuation
   exists_simpleCycleDerivativeContinuation_regularPrimitive)

end SC

namespace MPR

export PerronWright.FiniteIrreducibleMarkedPathResolvent (profile profile_analytic)

end MPR

namespace MCS

export PerronWright.FiniteIrreducibleMarkedCycleSingularity (jointProfileVertical)

end MCS

namespace ZA

export PerronWright.ZeroFieldUnicyclicActivitySingularity
  (cartesianDeltaSqrt_mem_slitPlane)

end ZA

namespace Global

export PerronWright.FiniteIrreducibleNormalizedDeltaProfile
  (exists_uniform_normalized_cartesianDelta_profile_of_terminal)

end Global

namespace DC

export PerronWright.FiniteIrreducibleTreeProfileTube
  (closedUnitDiskAway_subset_cartesianDelta
   zeroFieldProfile_eq_rootedTreeSeries_on_closedUnitDiskAway)

end DC

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

private theorem cartesianDelta_mono_eta {eta₁ eta₂ m : ℝ}
    (h : eta₁ ≤ eta₂) :
    Transfer.cartesianDelta eta₁ m ⊆
      Transfer.cartesianDelta eta₂ m := by
  intro w hw
  exact ⟨hw.1.trans_le (by linarith), hw.2⟩

export PerronWright.FiniteIrreducibleTreeProfileTube
  (exists_uniform_profile_unitBall_tube)

/-- The global normalized tree profile has a jointly analytic direct
simple-cycle chart on one common away product, and every fixed field in the
resulting ball retains the exact literal normalized unicyclic Taylor germ at
the origin. -/
theorem exists_normalizedFieldUnicyclic_away_chart
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    ∃ (eta r s : ℝ)
      (Theta : ℂ × C(S, ℂ) → C(S, ℂ))
      (A : ℂ × C(S, ℂ) → ℂ),
      0 < eta ∧ 0 < r ∧ 0 < s ∧
      let K :=
        TreeNormalizedClosedDiskGluing.closedUnitDiskAway delta
      let D := Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s
      let DAway := Metric.thickening r K ×ˢ
        Metric.ball (0 : C(S, ℂ)) r
      AnalyticOnNhd ℂ Theta D ∧
      (∀ q ∈ D,
        FiniteIrreducibleRadiusResponse.radius M hM q.2 ≠ 0 ∧
          TreeCritical.residual M.bjrModel
            (FiniteIrreducibleNormalizedFoldActivity.activityMap M hM q, Theta q) = 0) ∧
      Set.EqOn Theta
        (FiniteIrreducibleNormalizedFoldActivity.normalizedFoldProfile M hM)
        (FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      DAway ⊆ D ∧
      (∀ q ∈ DAway, ‖Theta q‖ < 1) ∧
      (∀ q : ℂ × C(S, ℂ),
        A q = JS.profileSimpleCycleSeries M.bjrModel (Theta q)) ∧
      AnalyticOnNhd ℂ A DAway ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) r,
        HasFPowerSeriesAt (fun w : ℂ ↦ A (w, g))
          (Local.normalizedFieldUnicyclicFMS M hM g) 0 := by
  obtain ⟨eta, rFold, s, Theta, heta, hrFold, hs,
      _hActivity, hTheta, hData, hThetaFold, hInside⟩ :=
    FiniteIrreducibleNormalizedDeltaProfile.exists_uniform_normalized_cartesianDelta_profile_of_terminal
      M hM
  obtain ⟨rAway, hrAway, hAwaySub, hAwayNorm⟩ :=
    exists_uniform_profile_unitBall_tube M hM
      heta hs hdelta hTheta hInside
  let K : Set ℂ :=
    TreeNormalizedClosedDiskGluing.closedUnitDiskAway delta
  let D : Set (ℂ × C(S, ℂ)) :=
    Transfer.cartesianDelta eta 0 ×ˢ
      Metric.ball (0 : C(S, ℂ)) s
  let DAway : Set (ℂ × C(S, ℂ)) :=
    Metric.thickening rAway K ×ˢ
      Metric.ball (0 : C(S, ℂ)) rAway
  let A : ℂ × C(S, ℂ) → ℂ := fun q ↦
    JS.profileSimpleCycleSeries M.bjrModel (Theta q)
  have hA : AnalyticOnNhd ℂ A DAway := by
    intro q hq
    have hqD : q ∈ D := by
      exact hAwaySub hq
    have hprofile : AnalyticAt ℂ Theta q := hTheta q hqD
    have hnorm : ‖Theta q‖ < 1 := hAwayNorm q hq
    have hcycle : AnalyticAt ℂ
        (JS.profileSimpleCycleSeries M.bjrModel) (Theta q) :=
      PS.profileSimpleCycleSeries_analyticOnNhd_unitBall M hM _
        (by
          simpa only [Metric.mem_ball, dist_zero_right] using hnorm)
    exact hcycle.comp_of_eq hprofile rfl
  have hzeroK : (0 : ℂ) ∈ K := by
    constructor
    · simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
      norm_num
    · change delta ≤ dist (0 : ℂ) 1
      simpa only [dist_zero_left, norm_one] using hdeltaOne
  have hTaylor : ∀ g ∈ Metric.ball (0 : C(S, ℂ)) rAway,
      HasFPowerSeriesAt (fun w : ℂ ↦ A (w, g))
        (Local.normalizedFieldUnicyclicFMS M hM g) 0 := by
    intro g hg
    have hzeroAway : ((0 : ℂ), g) ∈ DAway := by
      refine ⟨Metric.self_subset_thickening hrAway K hzeroK, hg⟩
    have hzeroD : ((0 : ℂ), g) ∈ D := hAwaySub hzeroAway
    simpa only [A] using
      Local.normalizedFieldUnicyclicFMS_hasFPowerSeriesAt_of_global_profile
        M hM heta hs hTheta hData hzeroD.2
  let r : ℝ := min rAway rFold
  have hr : 0 < r := lt_min hrAway hrFold
  have hAwayMono :
      Metric.thickening r K ×ˢ
          Metric.ball (0 : C(S, ℂ)) r ⊆ DAway := by
    exact Set.prod_mono
      (Metric.thickening_mono (min_le_left rAway rFold) K)
      (Metric.ball_subset_ball (min_le_left rAway rFold))
  refine ⟨eta, r, s, Theta, A, heta, hr, hs, ?_⟩
  dsimp only [K, D, DAway]
  refine ⟨hTheta, hData, ?_, ?_, ?_, fun _ ↦ rfl, ?_, ?_⟩
  · intro q hq
    apply hThetaFold
    exact ⟨⟨hq.1.1,
      Metric.ball_subset_ball (min_le_right rAway rFold) hq.1.2⟩, hq.2⟩
  · exact hAwayMono.trans hAwaySub
  · intro q hq
    exact hAwayNorm q (hAwayMono hq)
  · exact hA.mono hAwayMono
  · intro g hg
    exact hTaylor g
      (Metric.ball_subset_ball (min_le_left rAway rFold) hg)

/-- The literal normalized complex-field unicyclic germ has a genuine
joint continuation to one Cartesian Delta-domain and one fixed complex
field ball.  On the chosen square-root sheet its only singular term is
`-(1/2) log X`; the remaining primitive is jointly analytic and vanishes
on the critical axis.

The two scalar charts are glued without a determinant.  Their derivatives
agree on the overlap, and the additive constant of the local primitive is
fixed at the same real anchor `1 - delta` in every overlap component.  The
only compactness argument is the thickening of the zero-field `w`-spine. -/
theorem exists_normalizedFieldUnicyclic_cartesianDelta_continuation
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ (eta r s : ℝ)
      (H : C(S, ℂ) × ℂ → ℂ)
      (C₀ : C(S, ℂ) → ℂ)
      (G : ℂ × C(S, ℂ) → ℂ),
      0 < eta ∧ 0 < r ∧ 0 < s ∧
      AnalyticOnNhd ℂ H
        (Metric.ball (0 : C(S, ℂ)) s ×ˢ Metric.ball (0 : ℂ) r) ∧
      (∀ g : C(S, ℂ), H (g, 0) = 0) ∧
      AnalyticOnNhd ℂ C₀ (Metric.ball (0 : C(S, ℂ)) s) ∧
      AnalyticOnNhd ℂ G
        (Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        HasFPowerSeriesAt (fun w : ℂ ↦ G (w, g))
          (Local.normalizedFieldUnicyclicFMS M hM g) 0) ∧
      ∀ q ∈ FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        G q = -(1 / 2 : ℂ) *
            Complex.log (Transfer.cartesianDeltaSqrt q.1) +
          H (q.2, Transfer.cartesianDeltaSqrt q.1) + C₀ q.2 := by
  obtain ⟨eta₀, rTheta, sTheta, Theta,
      heta₀, hrTheta, hsTheta, _hActivity, hTheta, hData,
      hThetaFold, hInside⟩ :=
    FiniteIrreducibleNormalizedDeltaProfile.exists_uniform_normalized_cartesianDelta_profile_of_terminal
      M hM
  obtain ⟨B, H, _hB, hH, hHaxis, hsplit, hHderiv⟩ :=
    SC.exists_simpleCycleDerivativeContinuation_regularPrimitive M hM

  have hgoodPrimitive : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      AnalyticAt ℂ H q ∧
      AnalyticAt ℂ (MPR.profile M hM) q ∧
      (q.2 ≠ 0 →
        SC.simpleCycleDerivativeContinuation M hM q =
          -(1 / 2 : ℂ) * q.2⁻¹ + B q) ∧
      (fderiv ℂ H q) (0, 1) = B q := by
    filter_upwards [hH.eventually_analyticAt,
      (MPR.profile_analytic M hM).eventually_analyticAt,
      hsplit, hHderiv] with q hHq hProfileq hsplitq hHderivq
    exact ⟨hHq, hProfileq, hsplitq, hHderivq⟩
  obtain ⟨rPrimitive, hrPrimitive, hPrimitive⟩ :=
    Metric.eventually_nhds_iff.mp hgoodPrimitive

  let rBig : ℝ := min (min rTheta rPrimitive) 1 / 2
  let rSmall : ℝ := rBig / 2
  have hrBig : 0 < rBig := by
    dsimp only [rBig]
    exact half_pos (lt_min (lt_min hrTheta hrPrimitive) zero_lt_one)
  have hrSmall : 0 < rSmall := half_pos hrBig
  have hrBigTheta : rBig ≤ rTheta := by
    dsimp only [rBig]
    nlinarith [min_le_left rTheta rPrimitive,
      min_le_left (min rTheta rPrimitive) 1]
  have hrBigPrimitive : rBig ≤ rPrimitive := by
    dsimp only [rBig]
    nlinarith [min_le_right rTheta rPrimitive,
      min_le_left (min rTheta rPrimitive) 1]
  have hrSmallBig : rSmall < rBig := by
    dsimp only [rSmall]
    linarith
  have hrSmallTheta : rSmall ≤ rTheta :=
    (le_of_lt hrSmallBig).trans hrBigTheta
  have hrSmallPrimitive : rSmall ≤ rPrimitive :=
    (le_of_lt hrSmallBig).trans hrBigPrimitive

  let delta : ℝ := min 1 (rSmall ^ 2) / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact half_pos (lt_min zero_lt_one (pow_pos hrSmall 2))
  have hdeltaOne : delta ≤ 1 := by
    dsimp only [delta]
    nlinarith [min_le_left (1 : ℝ) (rSmall ^ 2)]
  have hdeltaTwo : delta ≤ 2 := hdeltaOne.trans (by norm_num)
  have hdeltaSmall : delta ≤ rSmall ^ 2 := by
    dsimp only [delta]
    nlinarith [min_le_right (1 : ℝ) (rSmall ^ 2),
      pow_pos hrSmall 2]
  let K : Set ℂ :=
    TreeNormalizedClosedDiskGluing.closedUnitDiskAway delta

  obtain ⟨t₀, ht₀, hAwaySub₀, hAwayNorm₀⟩ :=
    exists_uniform_profile_unitBall_tube M hM
      heta₀ hsTheta hdelta hTheta hInside
  let gap : ℝ := (rBig ^ 2 - rSmall ^ 2) / 2
  have hgap : 0 < gap := by
    dsimp only [gap]
    nlinarith [pow_pos hrBig 2, pow_pos hrSmall 2]
  let t : ℝ := min t₀ gap
  have ht : 0 < t := lt_min ht₀ hgap
  have ht₀' : t ≤ t₀ := min_le_left t₀ gap
  have htGap : t ≤ gap := min_le_right t₀ gap
  have hmargin : rSmall ^ 2 + t < rBig ^ 2 := by
    dsimp only [gap] at htGap
    nlinarith

  let s : ℝ := min t (min sTheta rPrimitive)
  have hs : 0 < s := lt_min ht (lt_min hsTheta hrPrimitive)
  have hsT : s ≤ t := min_le_left t (min sTheta rPrimitive)
  have hsTheta' : s ≤ sTheta :=
    (min_le_right t (min sTheta rPrimitive)).trans
      (min_le_left sTheta rPrimitive)
  have hsPrimitive : s ≤ rPrimitive :=
    (min_le_right t (min sTheta rPrimitive)).trans
      (min_le_right sTheta rPrimitive)

  obtain ⟨etaCover, hetaCover, hCover⟩ :=
    FiniteIrreducibleNormalizedDeltaProfile.exists_cartesianDelta_subset_fold_union_away
      hrSmall ht hdeltaSmall
  let eta : ℝ := min etaCover eta₀
  have heta : 0 < eta := lt_min hetaCover heta₀
  have hDeltaCover : Transfer.cartesianDelta eta 0 ⊆
      FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rSmall ∪
        Metric.thickening t K := by
    intro w hw
    apply hCover
    exact cartesianDelta_mono_eta (min_le_left etaCover eta₀) hw

  let D₀ : Set (ℂ × C(S, ℂ)) :=
    Transfer.cartesianDelta eta₀ 0 ×ˢ
      Metric.ball (0 : C(S, ℂ)) sTheta
  let DAway : Set (ℂ × C(S, ℂ)) :=
    Metric.thickening t K ×ˢ Metric.ball (0 : C(S, ℂ)) s
  have hAwaySub : DAway ⊆ D₀ := by
    intro q hq
    apply hAwaySub₀
    exact ⟨Metric.thickening_mono ht₀' K hq.1,
      Metric.ball_subset_ball (hsT.trans ht₀') hq.2⟩
  have hAwayNorm : ∀ q ∈ DAway, ‖Theta q‖ < 1 := by
    intro q hq
    exact hAwayNorm₀ q
      ⟨Metric.thickening_mono ht₀' K hq.1,
        Metric.ball_subset_ball (hsT.trans ht₀') hq.2⟩

  let A : ℂ × C(S, ℂ) → ℂ := fun q ↦
    JS.profileSimpleCycleSeries M.bjrModel (Theta q)
  have hA : AnalyticOnNhd ℂ A DAway := by
    intro q hq
    have hqD : q ∈ D₀ := hAwaySub hq
    have hprofile : AnalyticAt ℂ Theta q := hTheta q hqD
    have hnorm : ‖Theta q‖ < 1 := hAwayNorm q hq
    have hcycle : AnalyticAt ℂ
        (JS.profileSimpleCycleSeries M.bjrModel) (Theta q) :=
      PS.profileSimpleCycleSeries_analyticOnNhd_unitBall M hM _
        (by simpa only [Metric.mem_ball, dist_zero_right] using hnorm)
    exact hcycle.comp_of_eq hprofile rfl

  let a : ℂ := ((1 - delta : ℝ) : ℂ)
  have hAnchorGeometry :=
    TreeNormalizedClosedDiskGluing.localDelta_thickening_target_components_contain_real_anchor
      hdelta hdeltaTwo ht hrSmall hrBig hmargin hdeltaSmall
  have haO : a ∈
      FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rBig ∩
        Metric.thickening t K := by
    simpa only [a, K, FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta,
      TreeNormalizedFoldActivity.localCartesianDelta] using hAnchorGeometry.1
  let Xₐ : ℂ := Transfer.cartesianDeltaSqrt a
  have hXₐBall : Xₐ ∈ Metric.ball (0 : ℂ) rBig := by
    have hball := haO.1.2
    change Transfer.cartesianDeltaSqrt a ∈ Metric.ball (0 : ℂ) rBig at hball
    simpa only [Xₐ] using hball
  have hXₐPrimitive : dist Xₐ 0 < rPrimitive := by
    exact (Metric.mem_ball.mp hXₐBall).trans_le hrBigPrimitive

  let C₀ : C(S, ℂ) → ℂ := fun g ↦
    A (a, g) + (1 / 2 : ℂ) * Complex.log Xₐ - H (g, Xₐ)
  have hC₀ : AnalyticOnNhd ℂ C₀
      (Metric.ball (0 : C(S, ℂ)) s) := by
    intro g hg
    have hAg : AnalyticAt ℂ (fun h : C(S, ℂ) ↦ A (a, h)) g := by
      exact (hA (a, g) ⟨haO.2, hg⟩).comp_of_eq
        (analyticAt_const.prod analyticAt_id) rfl
    have hInput : dist (g, Xₐ)
        ((0 : C(S, ℂ)), (0 : ℂ)) < rPrimitive := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨(Metric.mem_ball.mp hg).trans_le hsPrimitive,
        hXₐPrimitive⟩
    have hHg : AnalyticAt ℂ (fun h : C(S, ℂ) ↦ H (h, Xₐ)) g :=
      (hPrimitive hInput).1.comp_of_eq
        (analyticAt_id.prod analyticAt_const) rfl
    have hconst : AnalyticAt ℂ
        (fun _ : C(S, ℂ) ↦ (1 / 2 : ℂ) * Complex.log Xₐ) g :=
      analyticAt_const
    change AnalyticAt ℂ
      (fun h : C(S, ℂ) ↦
        A (a, h) + (1 / 2 : ℂ) * Complex.log Xₐ - H (h, Xₐ)) g
    exact (hAg.add hconst).sub hHg

  let F : ℂ × C(S, ℂ) → ℂ := fun q ↦
    -(1 / 2 : ℂ) * Complex.log (Transfer.cartesianDeltaSqrt q.1) +
      H (q.2, Transfer.cartesianDeltaSqrt q.1) + C₀ q.2
  let DFoldBig : Set (ℂ × C(S, ℂ)) :=
    FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rBig ×ˢ
      Metric.ball (0 : C(S, ℂ)) s
  let DFold : Set (ℂ × C(S, ℂ)) :=
    FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rSmall ×ˢ
      Metric.ball (0 : C(S, ℂ)) s
  have hFBig : AnalyticOnNhd ℂ F DFoldBig := by
    intro q hq
    have hX : AnalyticAt ℂ
        (fun p : ℂ × C(S, ℂ) ↦
          Transfer.cartesianDeltaSqrt p.1) q :=
      ((Transfer.analyticOnNhd_cartesianDeltaSqrt (m := (0 : ℝ))
        (by norm_num)) q.1 hq.1.1).comp_of_eq analyticAt_fst rfl
    have hXslit : Transfer.cartesianDeltaSqrt q.1 ∈ Complex.slitPlane :=
      ZA.cartesianDeltaSqrt_mem_slitPlane (m := (0 : ℝ))
        (by norm_num) hq.1.1
    have hLog : AnalyticAt ℂ
        (fun p : ℂ × C(S, ℂ) ↦
          Complex.log (Transfer.cartesianDeltaSqrt p.1)) q :=
      (analyticAt_clog hXslit).comp_of_eq hX rfl
    have hInput : dist
        (q.2, Transfer.cartesianDeltaSqrt q.1)
        ((0 : C(S, ℂ)), (0 : ℂ)) < rPrimitive := by
      rw [Prod.dist_eq, max_lt_iff]
      refine ⟨(Metric.mem_ball.mp hq.2).trans_le hsPrimitive, ?_⟩
      exact (Metric.mem_ball.mp hq.1.2).trans_le hrBigPrimitive
    have hHcomp : AnalyticAt ℂ
        (fun p : ℂ × C(S, ℂ) ↦
          H (p.2, Transfer.cartesianDeltaSqrt p.1)) q :=
      (hPrimitive hInput).1.comp_of_eq (analyticAt_snd.prod hX) rfl
    have hCcomp : AnalyticAt ℂ
        (fun p : ℂ × C(S, ℂ) ↦ C₀ p.2) q :=
      (hC₀ q.2 hq.2).comp_of_eq analyticAt_snd rfl
    have hSing : AnalyticAt ℂ
        (fun p : ℂ × C(S, ℂ) ↦
          -(1 / 2 : ℂ) *
            Complex.log (Transfer.cartesianDeltaSqrt p.1)) q :=
      analyticAt_const.mul hLog
    change AnalyticAt ℂ
      (fun p : ℂ × C(S, ℂ) ↦
        -(1 / 2 : ℂ) * Complex.log (Transfer.cartesianDeltaSqrt p.1) +
          H (p.2, Transfer.cartesianDeltaSqrt p.1) + C₀ p.2) q
    exact (hSing.add hHcomp).add hCcomp
  have hF : AnalyticOnNhd ℂ F DFold := by
    intro q hq
    apply hFBig q
    exact ⟨⟨hq.1.1,
      Metric.ball_subset_ball (le_of_lt hrSmallBig) hq.1.2⟩, hq.2⟩

  have hOverlap : Set.EqOn F A (DFold ∩ DAway) := by
    intro q hq
    let w : ℂ := q.1
    let g : C(S, ℂ) := q.2
    let O : Set ℂ :=
      FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rBig ∩
        Metric.thickening t K
    have hwOverlap : w ∈
        FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rSmall ∩
          Metric.thickening t K := ⟨hq.1.1, hq.2.1⟩
    have hg : g ∈ Metric.ball (0 : C(S, ℂ)) s := hq.1.2
    have haW : a ∈ connectedComponentIn O w := by
      simpa only [a, K, O, w, FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta,
        TreeNormalizedFoldActivity.localCartesianDelta] using hAnchorGeometry.2 w hwOverlap
    let W : Set ℂ := connectedComponentIn O w
    have hwBig : w ∈ O := by
      exact ⟨⟨hwOverlap.1.1,
        Metric.ball_subset_ball (le_of_lt hrSmallBig) hwOverlap.1.2⟩,
        hwOverlap.2⟩
    have hwW : w ∈ W := mem_connectedComponentIn hwBig
    have hOopen : IsOpen O :=
      (FiniteIrreducibleNormalizedFoldActivity.isOpen_localCartesianDelta (by norm_num)).inter
        Metric.isOpen_thickening
    have hWopen : IsOpen W := hOopen.connectedComponentIn
    have hWpre : IsPreconnected W := isPreconnected_connectedComponentIn
    have hFW : AnalyticOnNhd ℂ (fun z : ℂ ↦ F (z, g)) W := by
      intro z hz
      have hzO := connectedComponentIn_subset O w hz
      exact (hFBig (z, g) ⟨hzO.1, hg⟩).comp_of_eq
        (analyticAt_id.prod analyticAt_const) rfl
    have hAW : AnalyticOnNhd ℂ (fun z : ℂ ↦ A (z, g)) W := by
      intro z hz
      have hzO := connectedComponentIn_subset O w hz
      exact (hA (z, g) ⟨hzO.2, hg⟩).comp_of_eq
        (analyticAt_id.prod analyticAt_const) rfl
    have hderivEq : Set.EqOn
        (deriv (fun z : ℂ ↦ F (z, g)))
        (deriv (fun z : ℂ ↦ A (z, g))) W := by
      intro z hz
      have hzO := connectedComponentIn_subset O w hz
      let X : ℂ := Transfer.cartesianDeltaSqrt z
      have hXanalytic : AnalyticAt ℂ Transfer.cartesianDeltaSqrt z :=
        Transfer.analyticOnNhd_cartesianDeltaSqrt (m := (0 : ℝ))
          (by norm_num) z hzO.1.1
      have hXderiv : HasDerivAt Transfer.cartesianDeltaSqrt
          (deriv Transfer.cartesianDeltaSqrt z) z :=
        hXanalytic.differentiableAt.hasDerivAt
      have hXslit : X ∈ Complex.slitPlane := by
        exact ZA.cartesianDeltaSqrt_mem_slitPlane (m := (0 : ℝ))
          (by norm_num) hzO.1.1
      have hXne : X ≠ 0 :=
        (Complex.mem_slitPlane_iff_arg.mp hXslit).2
      have hInput : dist (g, X)
          ((0 : C(S, ℂ)), (0 : ℂ)) < rPrimitive := by
        rw [Prod.dist_eq, max_lt_iff]
        refine ⟨(Metric.mem_ball.mp hg).trans_le hsPrimitive, ?_⟩
        exact (Metric.mem_ball.mp hzO.1.2).trans_le hrBigPrimitive
      obtain ⟨hHfull, hProfileFull, hsplitX, hHvertical⟩ :=
        hPrimitive hInput
      have hlineDeriv : HasDerivAt
          (fun Y : ℂ ↦ (g, Y)) ((0 : C(S, ℂ)), (1 : ℂ)) X :=
        (hasDerivAt_const X g).prodMk (hasDerivAt_id X)
      have hHraw :=
        hHfull.hasStrictFDerivAt.hasFDerivAt.comp_hasDerivAt X hlineDeriv
      have hHslice : HasDerivAt (fun Y : ℂ ↦ H (g, Y))
          (B (g, X)) X := by
        have h := hHraw.congr_deriv hHvertical
        simpa only [Function.comp_def] using h
      have hLog : HasDerivAt Complex.log X⁻¹ X :=
        Complex.hasDerivAt_log hXslit
      have hPrimitiveX : HasDerivAt
          (fun Y : ℂ ↦ -(1 / 2 : ℂ) * Complex.log Y + H (g, Y))
          (SC.simpleCycleDerivativeContinuation M hM (g, X)) X := by
        exact ((hLog.const_mul (-(1 / 2 : ℂ))).add hHslice).congr_deriv
          (hsplitX hXne).symm
      have hFslice : HasDerivAt (fun y : ℂ ↦ F (y, g))
          (SC.simpleCycleDerivativeContinuation M hM (g, X) *
            deriv Transfer.cartesianDeltaSqrt z) z := by
        simpa only [F, X, Function.comp_apply] using
          (hPrimitiveX.comp z hXderiv).add_const (C₀ g)

      have hProfileRaw :=
        hProfileFull.hasStrictFDerivAt.hasFDerivAt.comp_hasDerivAt
          X hlineDeriv
      have hProfileSlice : HasDerivAt
          (fun Y : ℂ ↦ MPR.profile M hM (g, Y))
          (MCS.jointProfileVertical M hM (g, X)) X := by
        convert hProfileRaw using 1 <;> rfl
      have hzThetaDomain : (z, g) ∈
          FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rTheta ×ˢ
            Metric.ball (0 : C(S, ℂ)) sTheta := by
        exact ⟨⟨hzO.1.1,
          Metric.ball_subset_ball hrBigTheta hzO.1.2⟩,
          Metric.ball_subset_ball hsTheta' hg⟩
      have hThetaEq : Theta (z, g) = MPR.profile M hM (g, X) := by
        simpa only [FiniteIrreducibleNormalizedFoldActivity.normalizedFoldProfile,
          MPR.profile, X] using hThetaFold hzThetaDomain
      have hsub : ‖MPR.profile M hM (g, X)‖ < 1 := by
        rw [← hThetaEq]
        exact hAwayNorm (z, g) ⟨hzO.2, hg⟩
      have hDirectX : HasDerivAt
          (fun Y : ℂ ↦
            JS.profileSimpleCycleSeries M.bjrModel (MPR.profile M hM (g, Y)))
          (SC.simpleCycleDerivativeContinuation M hM (g, X)) X := by
        exact (PF.profileSimpleCycleSeries_comp_hasDerivAt_of_norm_lt_one
          M hM hProfileSlice hsub).congr_deriv
            (JS.profileSimpleCycleDerivative_actual_eq_continuation
              M hM (g, X))
      have hDirectW : HasDerivAt
          (fun y : ℂ ↦ JS.profileSimpleCycleSeries M.bjrModel
            (MPR.profile M hM
              (g, Transfer.cartesianDeltaSqrt y)))
          (SC.simpleCycleDerivativeContinuation M hM (g, X) *
            deriv Transfer.cartesianDeltaSqrt z) z := by
        simpa only [X, Function.comp_def] using hDirectX.comp z hXderiv
      have hEqCycle : (fun y : ℂ ↦ A (y, g)) =ᶠ[nhds z]
          (fun y : ℂ ↦ JS.profileSimpleCycleSeries M.bjrModel
            (MPR.profile M hM
              (g, Transfer.cartesianDeltaSqrt y))) := by
        filter_upwards [
          (FiniteIrreducibleNormalizedFoldActivity.isOpen_localCartesianDelta
            (η := (1 : ℝ)) (by norm_num)).mem_nhds hzO.1]
          with y hy
        have hyThetaDomain : (y, g) ∈
            FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rTheta ×ˢ
              Metric.ball (0 : C(S, ℂ)) sTheta := by
          exact ⟨⟨hy.1, Metric.ball_subset_ball hrBigTheta hy.2⟩,
            Metric.ball_subset_ball hsTheta' hg⟩
        have hyEq := hThetaFold hyThetaDomain
        change JS.profileSimpleCycleSeries M.bjrModel (Theta (y, g)) =
          JS.profileSimpleCycleSeries M.bjrModel
            (MPR.profile M hM (g, Transfer.cartesianDeltaSqrt y))
        congr 1
      have hAslice : HasDerivAt (fun y : ℂ ↦ A (y, g))
          (SC.simpleCycleDerivativeContinuation M hM (g, X) *
            deriv Transfer.cartesianDeltaSqrt z) z := by
        exact hDirectW.congr_of_eventuallyEq hEqCycle
      exact hFslice.deriv.trans hAslice.deriv.symm
    have hAnchorEq : F (a, g) = A (a, g) := by
      dsimp only [F, C₀, Xₐ]
      ring
    have hEqW : Set.EqOn (fun z : ℂ ↦ F (z, g))
        (fun z : ℂ ↦ A (z, g)) W :=
      hWopen.eqOn_of_deriv_eq hWpre hFW.differentiableOn
        hAW.differentiableOn hderivEq haW hAnchorEq
    exact hEqW hwW

  let G : ℂ × C(S, ℂ) → ℂ :=
    AnalyticTwoChartGluing.glueOn DFold F A
  have hDFoldOpen : IsOpen DFold :=
    (FiniteIrreducibleNormalizedFoldActivity.isOpen_localCartesianDelta (by norm_num)).prod
      Metric.isOpen_ball
  have hDAwayOpen : IsOpen DAway :=
    Metric.isOpen_thickening.prod Metric.isOpen_ball
  have hGunion : AnalyticOnNhd ℂ G (DFold ∪ DAway) :=
    AnalyticTwoChartGluing.analyticOnNhd_glueOn_union
      hDFoldOpen hDAwayOpen hF hA hOverlap
  have hTargetCover :
      Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s ⊆ DFold ∪ DAway := by
    intro q hq
    rcases hDeltaCover hq.1 with hwFold | hwAway
    · exact Or.inl ⟨hwFold, hq.2⟩
    · exact Or.inr ⟨hwAway, hq.2⟩
  have hG : AnalyticOnNhd ℂ G
      (Transfer.cartesianDelta eta 0 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s) :=
    fun q hq ↦ hGunion q (hTargetCover hq)
  have hGleft : Set.EqOn G F DFold :=
    AnalyticTwoChartGluing.glueOn_eqOn_left DFold F A
  have hGright : Set.EqOn G A DAway :=
    AnalyticTwoChartGluing.glueOn_eqOn_right_of_eqOn_inter hOverlap

  have hzeroK : (0 : ℂ) ∈ K := by
    dsimp only [K]
    constructor
    · simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
      norm_num
    · change delta ≤ dist (0 : ℂ) 1
      simpa only [dist_zero_left, norm_one] using hdeltaOne
  have hzeroAway : (0 : ℂ) ∈ Metric.thickening t K :=
    Metric.self_subset_thickening ht K hzeroK
  have hTaylor : ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
      HasFPowerSeriesAt (fun w : ℂ ↦ G (w, g))
        (Local.normalizedFieldUnicyclicFMS M hM g) 0 := by
    intro g hg
    have hAseries : HasFPowerSeriesAt (fun w : ℂ ↦ A (w, g))
        (Local.normalizedFieldUnicyclicFMS M hM g) 0 := by
      simpa only [A] using
        Local.normalizedFieldUnicyclicFMS_hasFPowerSeriesAt_of_global_profile
          M hM heta₀ hsTheta hTheta hData
            (Metric.ball_subset_ball hsTheta' hg)
    have hEq : (fun w : ℂ ↦ G (w, g)) =ᶠ[nhds 0]
        (fun w : ℂ ↦ A (w, g)) := by
      filter_upwards [Metric.isOpen_thickening.mem_nhds hzeroAway] with w hw
      exact hGright ⟨hw, hg⟩
    exact hAseries.congr hEq.symm

  have hHlocal : AnalyticOnNhd ℂ H
      (Metric.ball (0 : C(S, ℂ)) s ×ˢ
        Metric.ball (0 : ℂ) rSmall) := by
    intro q hq
    apply (hPrimitive ?_).1
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨(Metric.mem_ball.mp hq.1).trans_le hsPrimitive,
      (Metric.mem_ball.mp hq.2).trans_le hrSmallPrimitive⟩
  have hFormula : ∀ q ∈
      FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rSmall ×ˢ
        Metric.ball (0 : C(S, ℂ)) s,
      G q = -(1 / 2 : ℂ) *
          Complex.log (Transfer.cartesianDeltaSqrt q.1) +
        H (q.2, Transfer.cartesianDeltaSqrt q.1) + C₀ q.2 := by
    intro q hq
    rw [hGleft hq]
  exact ⟨eta, rSmall, s, H, C₀, G, heta, hrSmall, hs,
    hHlocal, hHaxis, hC₀, hG, hTaylor, hFormula⟩

end PerronWright.FiniteIrreducibleFieldUnicyclicGlobalContinuation
