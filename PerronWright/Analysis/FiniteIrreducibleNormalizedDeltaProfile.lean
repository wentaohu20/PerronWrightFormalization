import PerronWright.Analysis.FiniteIrreducibleClosedDiskFoldTerminal
import PerronWright.Analysis.NormalizedDeltaProfile
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# A uniform normalized Cartesian-Delta profile

The terminal fold/closed-disk theorem produces an analytic profile on the
union of two explicit charts.  This module packages that union into one
smaller Cartesian Delta product, which is the domain shape consumed by the
coefficient-transfer and singularity-assembly arguments.

No continuation, uniqueness, or coefficient interface is assumed here.
-/

open Filter Topology
open scoped Classical

noncomputable section

namespace PerronWright.FiniteIrreducibleNormalizedDeltaProfile

open PerronWright
open PerronWright.Transfer
open PerronWright.FiniteIrreducibleNormalizedFoldActivity
open PerronWright.TreeNormalizedClosedDiskGluing

/-- If the closed-disk cutoff is no larger than the squared fold radius,
then a sufficiently thin full Cartesian Delta-domain is covered by the
local fold chart and the open thickening of the closed-disk-away chart. -/
theorem exists_cartesianDelta_subset_fold_union_away
    {delta r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hdeltaFold : delta ≤ r ^ 2) :
    ∃ eta : ℝ, 0 < eta ∧
      cartesianDelta eta 0 ⊆
        localCartesianDelta 1 0 r ∪
          Metric.thickening s (closedUnitDiskAway delta) := by
  let K : Set ℂ := closedUnitDiskAway delta
  let O : Set ℂ :=
    Metric.ball (1 : ℂ) (r ^ 2) ∪ Metric.thickening s K
  have hOopen : IsOpen O := Metric.isOpen_ball.union Metric.isOpen_thickening
  have hclosedBallSub : Metric.closedBall (0 : ℂ) 1 ⊆ O := by
    intro w hw
    by_cases hnear : dist w 1 < r ^ 2
    · exact Or.inl hnear
    · apply Or.inr
      apply Metric.self_subset_thickening hs K
      refine ⟨hw, ?_⟩
      exact hdeltaFold.trans (le_of_not_gt hnear)
  obtain ⟨t, ht, htSub⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open
      hOopen hclosedBallSub
  let eta : ℝ := min t 1
  have heta : 0 < eta := lt_min ht (by norm_num)
  refine ⟨eta, heta, ?_⟩
  intro w hw
  have hwNorm : ‖w‖ < 1 + eta := hw.1
  have hwThick : w ∈ Metric.thickening t (Metric.closedBall (0 : ℂ) 1) := by
    rw [thickening_closedBall ht (by norm_num) (0 : ℂ)]
    rw [Metric.mem_ball, dist_zero_right]
    have hetaLe : eta ≤ t := min_le_left t 1
    linarith
  have hwO : w ∈ O := htSub hwThick
  rcases hwO with hnear | haway
  · apply Or.inl
    refine ⟨?_, ?_⟩
    · refine ⟨?_, hw.2⟩
      have hetaLe : eta ≤ 1 := min_le_right t 1
      linarith
    · change cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) r
      rw [Metric.mem_ball, dist_zero_right]
      have hsquare : ‖cartesianDeltaSqrt w‖ ^ 2 = ‖1 - w‖ := by
        rw [← norm_pow, cartesianDeltaSqrt_sq]
      have hdist : ‖1 - w‖ < r ^ 2 := by
        simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hnear
      nlinarith [norm_nonneg (cartesianDeltaSqrt w)]
  · exact Or.inr haway

/-- Product form of the two-chart cover. -/
theorem exists_cartesianDelta_product_subset_fold_union_away
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {delta r s epsilon : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hdeltaFold : delta ≤ r ^ 2) :
    ∃ eta : ℝ, 0 < eta ∧
      cartesianDelta eta 0 ×ˢ Metric.ball (0 : E) epsilon ⊆
        (localCartesianDelta 1 0 r ×ˢ Metric.ball (0 : E) epsilon) ∪
          (Metric.thickening s (closedUnitDiskAway delta) ×ˢ
            Metric.ball (0 : E) epsilon) := by
  obtain ⟨eta, heta, hsub⟩ :=
    exists_cartesianDelta_subset_fold_union_away hr hs hdeltaFold
  refine ⟨eta, heta, ?_⟩
  rintro ⟨w, g⟩ ⟨hw, hg⟩
  rcases hsub hw with hwFold | hwAway
  · exact Or.inl ⟨hwFold, hg⟩
  · exact Or.inr ⟨hwAway, hg⟩

/-- Restrict analytic and residual data from the terminal two-chart union to
one Cartesian Delta product. -/
theorem exists_uniform_normalized_cartesianDelta_profile
    {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
    [MeasurableSpace S] [BorelSpace S]
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {delta r s : ℝ} {Theta : ℂ × C(S, ℂ) → C(S, ℂ)}
    (hr : 0 < r) (hs : 0 < s) (hdeltaFold : delta ≤ r ^ 2)
    (hActivity : AnalyticOnNhd ℂ (activityMap M hM)
      ((localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∪
        (Metric.thickening s (closedUnitDiskAway delta) ×ˢ
          Metric.ball (0 : C(S, ℂ)) s)))
    (hTheta : AnalyticOnNhd ℂ Theta
      ((localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∪
        (Metric.thickening s (closedUnitDiskAway delta) ×ˢ
          Metric.ball (0 : C(S, ℂ)) s)))
    (hData : ∀ q ∈
      ((localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∪
        (Metric.thickening s (closedUnitDiskAway delta) ×ˢ
          Metric.ball (0 : C(S, ℂ)) s)),
      FiniteIrreducibleRadiusResponse.radius M hM q.2 ≠ 0 ∧
        TreeCritical.residual M.bjrModel (activityMap M hM q, Theta q) = 0) :
    ∃ eta : ℝ, 0 < eta ∧
      AnalyticOnNhd ℂ (activityMap M hM)
        (cartesianDelta eta 0 ×ˢ Metric.ball (0 : C(S, ℂ)) s) ∧
      AnalyticOnNhd ℂ Theta
        (cartesianDelta eta 0 ×ˢ Metric.ball (0 : C(S, ℂ)) s) ∧
      ∀ q ∈ cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        FiniteIrreducibleRadiusResponse.radius M hM q.2 ≠ 0 ∧
          TreeCritical.residual M.bjrModel (activityMap M hM q, Theta q) = 0 := by
  obtain ⟨eta, heta, hsub⟩ :=
    exists_cartesianDelta_product_subset_fold_union_away
      (E := C(S, ℂ)) hr hs hdeltaFold
  refine ⟨eta, heta, ?_, ?_, ?_⟩
  · exact fun q hq ↦ hActivity q (hsub hq)
  · exact fun q hq ↦ hTheta q (hsub hq)
  · exact fun q hq ↦ hData q (hsub hq)

/-- The zero-field slice of a unified normalized Delta profile is the actual
rooted-tree series throughout the open unit disk.  This follows from the
fold-lens identity and analytic uniqueness, so no separate agreement
hypothesis is added to the terminal interface. -/
theorem zeroField_eq_rootedTreeSeries_on_unitBall
    {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
    [MeasurableSpace S] [BorelSpace S]
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {eta r s : ℝ} {Theta : ℂ × C(S, ℂ) → C(S, ℂ)}
    (heta : 0 < eta) (hr : 0 < r) (hs : 0 < s)
    (hTheta : AnalyticOnNhd ℂ Theta
      (cartesianDelta eta 0 ×ˢ Metric.ball (0 : C(S, ℂ)) s))
    (hThetaFold : Set.EqOn Theta (normalizedFoldProfile M hM)
      (localCartesianDelta 1 0 r ×ˢ
        Metric.ball (0 : C(S, ℂ)) s)) :
    Set.EqOn (fun w : ℂ ↦ Theta (w, 0)) M.bjrModel.rootedTreeSeries
      (Metric.ball (0 : ℂ) 1) := by
  obtain ⟨ell, hell, hFoldLens⟩ :=
    exists_normalizedFoldProfile_eq_rootedTreeSeries_on_lens M hM
  let U : Set ℂ := Metric.ball (0 : ℂ) 1
  let f : ℂ → C(S, ℂ) := Theta ∘ fun w ↦ (id w, 0)
  let g : ℂ → C(S, ℂ) := M.bjrModel.rootedTreeSeries
  have hf : AnalyticOnNhd ℂ f U := by
    intro w hw
    have hwDelta : w ∈ cartesianDelta eta 0 :=
      unit_ball_subset_cartesianDelta heta hw
    have hpair : (w, (0 : C(S, ℂ))) ∈
        cartesianDelta eta 0 ×ˢ Metric.ball (0 : C(S, ℂ)) s :=
      ⟨hwDelta, Metric.mem_ball_self hs⟩
    simpa only [f, Function.comp_apply] using
      (hTheta (w, (0 : C(S, ℂ))) hpair).comp_of_eq
        (analyticAt_id.prod analyticAt_const) rfl
  have hg : AnalyticOnNhd ℂ g U := by
    intro w hw
    have hwUnit : w ∈ Metric.eball 0 (1 : ENNReal) := by
      rw [← ENNReal.coe_one, Metric.eball_coe]
      simpa only [NNReal.coe_one] using hw
    have hwRadius : w ∈
        Metric.eball 0 M.bjrModel.complexTypeRootedTreeFMS.radius :=
      Metric.eball_subset_eball
        M.bjrModel.one_le_complexTypeRootedTreeFMS_radius hwUnit
    simpa only [g] using M.bjrModel.rootedTreeSeries_analyticOnNhd w hwRadius
  have hUpre : IsPreconnected U := (convex_ball (0 : ℂ) 1).isPreconnected

  let a : ℝ := min (ell ^ 2) (min (r ^ 2) 1) / 2
  have ha : 0 < a := by
    dsimp only [a]
    exact half_pos (lt_min (pow_pos hell 2)
      (lt_min (pow_pos hr 2) zero_lt_one))
  have haEll : a < ell ^ 2 := by
    dsimp only [a]
    have hle := min_le_left (ell ^ 2) (min (r ^ 2) 1)
    nlinarith [pow_pos hell 2]
  have haR : a < r ^ 2 := by
    dsimp only [a]
    have hle := (min_le_right (ell ^ 2) (min (r ^ 2) 1)).trans
      (min_le_left (r ^ 2) 1)
    nlinarith [pow_pos hr 2]
  have haOne : a < 1 := by
    dsimp only [a]
    have hle := (min_le_right (ell ^ 2) (min (r ^ 2) 1)).trans
      (min_le_right (r ^ 2) 1)
    nlinarith
  let w0 : ℂ := (1 - a : ℝ)
  have hw0Norm : ‖w0‖ < 1 := by
    dsimp only [w0]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 1 - a)]
    linarith
  have hw0Ell : dist w0 1 < ell ^ 2 := by
    dsimp only [w0]
    rw [Complex.dist_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    norm_num [abs_of_pos ha]
    exact haEll
  have hw0R : dist w0 1 < r ^ 2 := by
    dsimp only [w0]
    rw [Complex.dist_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    norm_num [abs_of_pos ha]
    exact haR
  let V : Set ℂ :=
    Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (ell ^ 2) ∩
      Metric.ball (1 : ℂ) (r ^ 2)
  have hw0V : w0 ∈ V := by
    exact ⟨⟨by simpa only [Metric.mem_ball, dist_zero_right] using hw0Norm,
      hw0Ell⟩, hw0R⟩
  have hVopen : IsOpen V :=
    (Metric.isOpen_ball.inter Metric.isOpen_ball).inter Metric.isOpen_ball
  have hfgV : Set.EqOn f g V := by
    intro w hw
    have hwLocal : w ∈ localCartesianDelta 1 0 r := by
      refine ⟨unit_ball_subset_cartesianDelta (by norm_num) hw.1.1, ?_⟩
      change cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) r
      rw [Metric.mem_ball, dist_zero_right]
      have hsquare : ‖cartesianDeltaSqrt w‖ ^ 2 = ‖1 - w‖ := by
        rw [← norm_pow, cartesianDeltaSqrt_sq]
      have hdist : ‖1 - w‖ < r ^ 2 := by
        simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw.2
      nlinarith [norm_nonneg (cartesianDeltaSqrt w)]
    have hpairFold : (w, (0 : C(S, ℂ))) ∈
        localCartesianDelta 1 0 r ×ˢ Metric.ball (0 : C(S, ℂ)) s :=
      ⟨hwLocal, Metric.mem_ball_self hs⟩
    have hThetaEq := hThetaFold hpairFold
    have hFoldEq := hFoldLens ⟨hw.1.1, hw.1.2⟩
    exact hThetaEq.trans hFoldEq
  have hfgNhd : f =ᶠ[𝓝 w0] g :=
    Filter.mem_of_superset (hVopen.mem_nhds hw0V) hfgV
  change Set.EqOn f g U
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUpre
    (by simpa only [U, Metric.mem_ball, dist_zero_right] using hw0Norm) hfgNhd

/-- Unconditional uniform normalized Delta profile obtained directly from
the terminal fold/closed-disk gluing theorem.  The fold equality is retained
on the original local fold product for later singular expansions, and its
zero-field slice is the actual rooted-tree generating function. -/
theorem exists_uniform_normalized_cartesianDelta_profile_of_terminal
    {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
    [MeasurableSpace S] [BorelSpace S]
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ (eta r s : ℝ) (Theta : ℂ × C(S, ℂ) → C(S, ℂ)),
      0 < eta ∧ 0 < r ∧ 0 < s ∧
      AnalyticOnNhd ℂ (activityMap M hM)
        (cartesianDelta eta 0 ×ˢ Metric.ball (0 : C(S, ℂ)) s) ∧
      AnalyticOnNhd ℂ Theta
        (cartesianDelta eta 0 ×ˢ Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ q ∈ cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        FiniteIrreducibleRadiusResponse.radius M hM q.2 ≠ 0 ∧
          TreeCritical.residual M.bjrModel (activityMap M hM q, Theta q) = 0) ∧
      Set.EqOn Theta (normalizedFoldProfile M hM)
        (localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      Set.EqOn (fun w : ℂ ↦ Theta (w, 0)) M.bjrModel.rootedTreeSeries
        (Metric.ball (0 : ℂ) 1) := by
  obtain ⟨delta, r, rBig, s, epsilon, U, Psi, Theta,
      hdelta, hr, hrBig, hs, hepsilon, hmargin, hdeltaFold,
      hUopen, hKsub, hAwaySub, hFoldOpen, hAwayOpen,
      hActivity, hTheta, hData, hThetaFold, hThetaAway⟩ :=
    PerronWright.FiniteIrreducibleClosedDiskTerminal.exists_normalizedFold_closedDiskAway_glued_profile
      M hM
  obtain ⟨eta, heta, hActivityDelta, hThetaDelta, hDataDelta⟩ :=
    exists_uniform_normalized_cartesianDelta_profile M hM hr hs
      hdeltaFold hActivity hTheta hData
  have hZero := zeroField_eq_rootedTreeSeries_on_unitBall
    M hM heta hr hs hThetaDelta hThetaFold
  exact ⟨eta, r, s, Theta, heta, hr, hs, hActivityDelta,
    hThetaDelta, hDataDelta, hThetaFold, hZero⟩

end PerronWright.FiniteIrreducibleNormalizedDeltaProfile
