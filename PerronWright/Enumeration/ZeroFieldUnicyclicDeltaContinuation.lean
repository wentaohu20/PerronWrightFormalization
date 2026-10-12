import PerronWright.Enumeration.ZeroFieldUnicyclicActivitySingularity
import PerronWright.Enumeration.ProfileSimpleCyclePowerSeries
import PerronWright.Analysis.NormalizedDeltaProfile

/-!
# Global zero-field unicyclic continuation

This file begins the global gluing step for the zero-field unicyclic EGF.
The first two results are the reusable overlap interfaces: the genuine EGF
is analytic on the open unit disk, and every activity-coordinate local
continuation furnished by the fold construction agrees with it on the
whole complex lens, not merely on the positive physical ray.
-/

open Filter Topology PerronWright Set
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.ZeroFieldUnicyclicDeltaContinuation

namespace ZF

export PerronWright.ZeroFieldUnicyclicSingularity
  (zeroFieldUnicyclicEGF)

end ZF

namespace PS

export PerronWright.ProfileSimpleCyclePowerSeries
  (profileSimpleCycleSeries_analyticOnNhd_unitBall)

end PS

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The genuine zero-field unicyclic EGF is analytic throughout the open
unit disk.  This is a composition of the genuine rooted-tree Taylor sum
with the normally convergent profile simple-cycle series. -/
theorem zeroFieldUnicyclicEGF_analyticOnNhd_unitBall
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticOnNhd ℂ (ZF.zeroFieldUnicyclicEGF M)
      (Metric.ball (0 : ℂ) 1) := by
  intro w hw
  have hwUnit : w ∈ Metric.eball 0 (1 : ENNReal) := by
    rw [← ENNReal.coe_one, Metric.eball_coe]
    simpa only [NNReal.coe_one] using hw
  have hwRadius : w ∈
      Metric.eball 0 M.complexTypeRootedTreeFMS.radius :=
    Metric.eball_subset_eball
      M.one_le_complexTypeRootedTreeFMS_radius hwUnit
  have hroot : AnalyticAt ℂ M.rootedTreeSeries w :=
    M.rootedTreeSeries_analyticOnNhd w hwRadius
  have hnormw : ‖w‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hrootNorm : ‖M.rootedTreeSeries w‖ < 1 :=
    M.rootedTreeSeries_norm_lt_one_of_closedDisk_ne_one hM hnormw.le
      (fun hw1 => by subst w; norm_num at hnormw)
  have hcycle : AnalyticAt ℂ
      (PerronWright.JointSimpleCycleEGF.profileSimpleCycleSeries M)
      (M.rootedTreeSeries w) :=
    PS.profileSimpleCycleSeries_analyticOnNhd_unitBall M hM _
      (by simpa only [Metric.mem_ball, dist_zero_right] using hrootNorm)
  exact hcycle.comp_of_eq hroot rfl

/-- A local activity-coordinate continuation which agrees with the genuine
EGF on the positive physical ray agrees with it on the entire complex
lens.  This is the identity-theorem upgrade needed for two-chart gluing. -/
theorem localContinuation_eq_zeroFieldUnicyclicEGF_on_lens
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r))
    (hphysical : ∀ X : ℝ, 0 < X → X < r →
      ZF.zeroFieldUnicyclicEGF M (((1 - X ^ 2 : ℝ) : ℂ)) =
        F (((1 - X ^ 2 : ℝ) : ℂ))) :
    Set.EqOn F (ZF.zeroFieldUnicyclicEGF M)
      (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (r ^ 2)) := by
  let U : Set ℂ :=
    Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (r ^ 2)
  have hUlocal : U ⊆
      TreeNormalizedFoldActivity.localCartesianDelta 1 0 r := by
    intro w hw
    refine ⟨Transfer.unit_ball_subset_cartesianDelta (by norm_num) hw.1, ?_⟩
    change Transfer.cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) r
    rw [Metric.mem_ball, dist_zero_right]
    have hsquare : ‖Transfer.cartesianDeltaSqrt w‖ ^ 2 = ‖1 - w‖ := by
      rw [← norm_pow, Transfer.cartesianDeltaSqrt_sq]
    have hdist : ‖1 - w‖ < r ^ 2 := by
      simpa only [Metric.mem_ball, Complex.dist_eq, norm_sub_rev] using hw.2
    nlinarith [norm_nonneg (Transfer.cartesianDeltaSqrt w)]
  have hf : AnalyticOnNhd ℂ F U := fun w hw ↦ hF w (hUlocal hw)
  have hg : AnalyticOnNhd ℂ (ZF.zeroFieldUnicyclicEGF M) U :=
    (zeroFieldUnicyclicEGF_analyticOnNhd_unitBall M hM).mono
      (inter_subset_left)
  have hUpre : IsPreconnected U :=
    ((convex_ball (0 : ℂ) 1).inter
      (convex_ball (1 : ℂ) (r ^ 2))).isPreconnected

  have hbound : 0 < min (r ^ 2) 1 := lt_min (pow_pos hr 2) zero_lt_one
  obtain ⟨a, ha0, habound⟩ := exists_between hbound
  have har : a < r ^ 2 := habound.trans_le (min_le_left (r ^ 2) 1)
  have ha1 : a < 1 := habound.trans_le (min_le_right (r ^ 2) 1)
  let w₀ : ℝ := 1 - a
  have hw₀0 : 0 < w₀ := by dsimp only [w₀]; linarith
  have hw₀1 : w₀ < 1 := by dsimp only [w₀]; linarith
  have hw₀sub : w₀ - 1 = -a := by dsimp only [w₀]; ring
  have hw₀U : (w₀ : ℂ) ∈ U := by
    have hdist0 : dist (w₀ : ℂ) 0 = w₀ := by
      rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hw₀0]
    have hdist1 : dist (w₀ : ℂ) 1 = a := by
      rw [Complex.dist_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, hw₀sub, abs_neg,
        abs_of_pos ha0]
    exact ⟨by simpa only [Metric.mem_ball, hdist0] using hw₀1,
      by simpa only [Metric.mem_ball, hdist1] using har⟩

  let b : ℝ := max 0 (1 - r ^ 2)
  have hbw₀ : b < w₀ := by
    dsimp only [b, w₀]
    rw [max_lt_iff]
    exact ⟨by linarith, by linarith⟩
  have hw₀I : w₀ ∈ Set.Ioo b 1 := ⟨hbw₀, hw₀1⟩
  have hIevent : ∀ᶠ x : ℝ in 𝓝 w₀, x ∈ Set.Ioo b 1 :=
    isOpen_Ioo.mem_nhds hw₀I
  have hreal : ∃ᶠ x : ℝ in 𝓝[≠] w₀,
      F (x : ℂ) = ZF.zeroFieldUnicyclicEGF M (x : ℂ) := by
    apply Filter.Eventually.frequently
    filter_upwards [hIevent.filter_mono nhdsWithin_le_nhds] with x hx
    have hx0 : 0 < x := (le_max_left 0 (1 - r ^ 2)).trans_lt hx.1
    have hx1 : x < 1 := hx.2
    have hxr : 1 - x < r ^ 2 := by
      have hlow : 1 - r ^ 2 < x :=
        (le_max_right 0 (1 - r ^ 2)).trans_lt hx.1
      linarith
    let X : ℝ := Real.sqrt (1 - x)
    have hX0 : 0 < X := Real.sqrt_pos.2 (sub_pos.mpr hx1)
    have hXsq : X ^ 2 = 1 - x := by
      dsimp only [X]
      exact Real.sq_sqrt (sub_nonneg.mpr hx1.le)
    have hXr : X < r := by nlinarith [Real.sqrt_nonneg (1 - x)]
    have hone : 1 - X ^ 2 = x := by rw [hXsq]; ring
    simpa only [hone] using (hphysical X hX0 hXr).symm

  have hcomplex : ∃ᶠ z : ℂ in 𝓝[≠] (w₀ : ℂ),
      F z = ZF.zeroFieldUnicyclicEGF M z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hxs_tendsto, hxs_eq⟩ := hreal
    refine ⟨fun n ↦ (xs n : ℂ), ?_, fun n ↦ hxs_eq n⟩
    rw [tendsto_nhdsWithin_iff] at hxs_tendsto ⊢
    constructor
    · rw [tendsto_ofReal_iff]
      exact hxs_tendsto.1
    · simpa using hxs_tendsto.2

  change Set.EqOn F (ZF.zeroFieldUnicyclicEGF M) U
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hUpre hw₀U hcomplex

/-- The closed unit disk away from `1` lies in every positive-width
Cartesian Delta-domain. -/
theorem closedUnitDiskAway_subset_cartesianDelta
    {eta delta : ℝ} (heta : 0 < eta) (hdelta : 0 < delta) :
    TreeNormalizedClosedDiskGluing.closedUnitDiskAway delta ⊆
      Transfer.cartesianDelta eta 0 := by
  intro w hw
  have hnorm : ‖w‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1
  refine ⟨by linarith, ?_⟩
  rintro ⟨hre, him⟩
  have him0 : w.im = 0 := by
    have : |w.im| ≤ 0 := by
      simpa only [Complex.sub_im, Complex.one_im, sub_zero, zero_mul] using him
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
  have hre1 : 1 ≤ w.re := by
    simpa only [Complex.sub_re, Complex.one_re, sub_nonneg] using hre
  have hreNorm : w.re ≤ ‖w‖ := Complex.re_le_norm w
  have hnorm1 : ‖w‖ = 1 := le_antisymm hnorm (hre1.trans hreNorm)
  have hreEq : w.re = 1 := le_antisymm (hreNorm.trans_eq hnorm1) hre1
  have hw1 : w = 1 := Complex.ext hreEq (by simpa only [Complex.one_im] using him0)
  subst w
  have haway := hw.2
  change delta ≤ dist (1 : ℂ) 1 at haway
  rw [dist_self] at haway
  exact (not_le_of_gt hdelta) haway

/-- An analytic zero-field profile on a Cartesian Delta-domain which agrees
with the rooted-tree Taylor sum in the open unit disk also agrees with its
continuous boundary values at every closed-disk point different from the
critical activity. -/
theorem zeroFieldProfile_eq_rootedTreeSeries_on_closedUnitDiskAway
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {eta delta : ℝ} {theta : ℂ → C(S, ℂ)}
    (heta : 0 < eta) (hdelta : 0 < delta)
    (htheta : AnalyticOnNhd ℂ theta (Transfer.cartesianDelta eta 0))
    (hinside : Set.EqOn theta M.rootedTreeSeries
      (Metric.ball (0 : ℂ) 1)) :
    Set.EqOn theta M.rootedTreeSeries
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
  have hrootCont : ContinuousOn M.rootedTreeSeries (D ∩ C) := by
    apply (M.rootedTreeSeries_continuousOn_closedDisk hM).mono
    intro w hw
    change ‖w‖ ≤ 1
    simpa only [C, Metric.mem_closedBall, dist_zero_right] using hw.2
  have hEqDC : Set.EqOn theta M.rootedTreeSeries (D ∩ C) := by
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

private theorem cartesianDelta_mono_eta {eta₁ eta₂ m : ℝ}
    (h : eta₁ ≤ eta₂) :
    Transfer.cartesianDelta eta₁ m ⊆ Transfer.cartesianDelta eta₂ m := by
  intro w hw
  exact ⟨hw.1.trans_le (by linarith), hw.2⟩

/-- The genuine zero-field unicyclic EGF has a holomorphic continuation to
a full Cartesian Delta-domain.  The continuation agrees with the genuine
series on the whole open unit disk and retains the explicit logarithmic
expansion, with square-root-order analytic error, on a smaller fold chart.

The construction uses no global determinant: on the compact part of the
closed disk away from `1`, the uniformly subcritical profile cycle series
is the second chart, and analytic uniqueness glues it to the logarithmic
fold chart component by component. -/
theorem exists_zeroFieldUnicyclic_cartesianDelta_continuation
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (H₁ : ℂ) (E G : ℂ → ℂ) (eta r : ℝ),
      0 < eta ∧ 0 < r ∧
      AnalyticOnNhd ℂ E
        (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r) ∧
      AnalyticOnNhd ℂ G (Transfer.cartesianDelta eta 0) ∧
      Set.EqOn G (ZF.zeroFieldUnicyclicEGF M)
        (Metric.ball (0 : ℂ) 1) ∧
      (∀ w ∈ TreeNormalizedFoldActivity.localCartesianDelta 1 0 r,
        G w = -(1 / 4 : ℂ) * Complex.log (1 - w) + E w + H₁) ∧
      (fun w : ℂ ↦ E w) =O[𝓝 (1 : ℂ)]
        (fun w : ℂ ↦ Transfer.cartesianDeltaSqrt w) := by
  obtain ⟨H₁, E, F, rF, hrF, -, hE, hF, hFormula, hEO, hPhysical⟩ :=
    ZeroFieldUnicyclicActivitySingularity.exists_zeroFieldUnicyclic_activity_singularity_data
      M hM
  have hFLens := localContinuation_eq_zeroFieldUnicyclicEGF_on_lens
    M hM hrF hF hPhysical

  obtain ⟨eta₀, _rTheta, sTheta, Theta, heta₀, _hrTheta, hsTheta,
      -, hTheta, -, -, hThetaInside⟩ :=
    NormalizedDeltaProfile.exists_uniform_normalized_cartesianDelta_profile_of_terminal
      M hM
  let theta : ℂ → C(S, ℂ) := fun w ↦ Theta (w, 0)
  have htheta : AnalyticOnNhd ℂ theta
      (Transfer.cartesianDelta eta₀ 0) := by
    intro w hw
    have hpair : (w, (0 : C(S, ℂ))) ∈
        Transfer.cartesianDelta eta₀ 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) sTheta :=
      ⟨hw, Metric.mem_ball_self hsTheta⟩
    exact (hTheta (w, (0 : C(S, ℂ))) hpair).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  have hthetaInside : Set.EqOn theta M.rootedTreeSeries
      (Metric.ball (0 : ℂ) 1) := by
    simpa only [theta] using hThetaInside

  let rBig : ℝ := rF / 2
  let rSmall : ℝ := rBig / 2
  have hrBig : 0 < rBig := half_pos hrF
  have hrSmall : 0 < rSmall := half_pos hrBig
  have hrBigF : rBig ≤ rF := by dsimp only [rBig]; linarith
  have hrSmallBig : rSmall < rBig := by
    dsimp only [rSmall]
    linarith
  have hrSmallF : rSmall ≤ rF := (le_of_lt hrSmallBig).trans hrBigF

  let delta : ℝ := min 1 (rSmall ^ 2) / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact half_pos (lt_min zero_lt_one (pow_pos hrSmall 2))
  have hdeltaFold : delta ≤ rSmall ^ 2 := by
    dsimp only [delta]
    have hle := min_le_right (1 : ℝ) (rSmall ^ 2)
    nlinarith [pow_pos hrSmall 2]
  let K : Set ℂ :=
    TreeNormalizedClosedDiskGluing.closedUnitDiskAway delta
  have hthetaK : Set.EqOn theta M.rootedTreeSeries K := by
    simpa only [K] using
      (zeroFieldProfile_eq_rootedTreeSeries_on_closedUnitDiskAway
        M hM heta₀ hdelta htheta hthetaInside)

  let V : Set ℂ := Transfer.cartesianDelta eta₀ 0 ∩
    theta ⁻¹' Metric.ball (0 : C(S, ℂ)) 1
  have hVopen : IsOpen V := by
    exact htheta.continuousOn.isOpen_inter_preimage
      (Transfer.isOpen_cartesianDelta eta₀ 0) Metric.isOpen_ball
  have hKsubV : K ⊆ V := by
    intro w hw
    have hwD : w ∈ Transfer.cartesianDelta eta₀ 0 :=
      closedUnitDiskAway_subset_cartesianDelta heta₀ hdelta hw
    have hwne : w ≠ 1 := by
      intro hw1
      subst w
      have haway := hw.2
      change delta ≤ dist (1 : ℂ) 1 at haway
      rw [dist_self] at haway
      exact (not_le_of_gt hdelta) haway
    have hrootNorm : ‖M.rootedTreeSeries w‖ < 1 :=
      M.rootedTreeSeries_norm_lt_one_of_closedDisk_ne_one hM
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1)
        hwne
    refine ⟨hwD, ?_⟩
    change theta w ∈ Metric.ball (0 : C(S, ℂ)) 1
    rw [Metric.mem_ball, dist_zero_right, hthetaK hw]
    exact hrootNorm
  obtain ⟨t₀, ht₀, ht₀Sub⟩ :=
    (TreeNormalizedClosedDiskGluing.isCompact_closedUnitDiskAway delta).exists_thickening_subset_open
      hVopen hKsubV
  let gap : ℝ := (rBig ^ 2 - rSmall ^ 2) / 2
  have hgap : 0 < gap := by
    dsimp only [gap]
    nlinarith [pow_pos hrBig 2, pow_pos hrSmall 2]
  let t : ℝ := min t₀ gap
  have ht : 0 < t := lt_min ht₀ hgap
  have htGap : t ≤ gap := min_le_right t₀ gap
  have hmargin : rSmall ^ 2 + t < rBig ^ 2 := by
    dsimp only [gap] at htGap
    nlinarith
  have hAwaySubV : Metric.thickening t K ⊆ V := by
    intro w hw
    apply ht₀Sub
    obtain ⟨z, hzK, hwz⟩ := Metric.mem_thickening_iff.mp hw
    apply Metric.mem_thickening_iff.mpr
    exact ⟨z, hzK, hwz.trans_le (min_le_left t₀ gap)⟩

  obtain ⟨etaCover, hetaCover, hCover⟩ :=
    NormalizedDeltaProfile.exists_cartesianDelta_subset_fold_union_away
      hrSmall ht hdeltaFold
  let eta : ℝ := min etaCover eta₀
  have heta : 0 < eta := lt_min hetaCover heta₀
  have hDeltaCover : Transfer.cartesianDelta eta 0 ⊆
      TreeNormalizedFoldActivity.localCartesianDelta 1 0 rSmall ∪
        Metric.thickening t K := by
    intro w hw
    apply hCover
    exact cartesianDelta_mono_eta (min_le_left etaCover eta₀) hw
  let A : ℂ → ℂ := fun w ↦
    PerronWright.JointSimpleCycleEGF.profileSimpleCycleSeries M (theta w)
  have hA : AnalyticOnNhd ℂ A (Metric.thickening t K) := by
    intro w hw
    have hwV := hAwaySubV hw
    have hthetaAt : AnalyticAt ℂ theta w := htheta w hwV.1
    have hnorm : ‖theta w‖ < 1 := by
      have hwBall := hwV.2
      change theta w ∈ Metric.ball (0 : C(S, ℂ)) 1 at hwBall
      simpa only [Metric.mem_ball, dist_zero_right] using hwBall
    have hcycle := PS.profileSimpleCycleSeries_analyticOnNhd_unitBall
      M hM (theta w)
      (by simpa only [Metric.mem_ball, dist_zero_right] using hnorm)
    exact hcycle.comp_of_eq hthetaAt rfl
  have hFBig : AnalyticOnNhd ℂ F
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 rBig) := by
    intro w hw
    exact hF w ⟨hw.1,
      Metric.ball_subset_ball hrBigF hw.2⟩
  have hFSmall : AnalyticOnNhd ℂ F
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 rSmall) := by
    intro w hw
    exact hF w ⟨hw.1,
      Metric.ball_subset_ball hrSmallF hw.2⟩

  have hOverlap : Set.EqOn F A
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 rSmall ∩
        Metric.thickening t K) := by
    intro w hw
    let O : Set ℂ :=
      TreeNormalizedFoldActivity.localCartesianDelta 1 0 rBig ∩
        Metric.thickening t K
    have hOBig : w ∈ O := by
      refine ⟨⟨hw.1.1, ?_⟩, hw.2⟩
      exact Metric.ball_subset_ball (le_of_lt hrSmallBig) hw.1.2
    obtain ⟨w₀, hw₀Component, hw₀Lens⟩ :=
      TreeNormalizedClosedDiskGluing.localDelta_thickening_target_components_meet_lens
        hdelta ht hrSmall hrBig hmargin hrBigF w hw
    let W : Set ℂ := connectedComponentIn O w
    have hOopen : IsOpen O :=
      (TreeNormalizedFoldActivity.isOpen_localCartesianDelta (by norm_num)).inter
        Metric.isOpen_thickening
    have hWopen : IsOpen W := hOopen.connectedComponentIn
    have hWpre : IsPreconnected W := isPreconnected_connectedComponentIn
    have hwW : w ∈ W := mem_connectedComponentIn hOBig
    have hw₀W : w₀ ∈ W := hw₀Component
    have hFW : AnalyticOnNhd ℂ F W := by
      intro z hz
      exact hFBig z ((connectedComponentIn_subset O w hz).1)
    have hAW : AnalyticOnNhd ℂ A W := by
      intro z hz
      exact hA z ((connectedComponentIn_subset O w hz).2)
    have hEqNhd : F =ᶠ[𝓝 w₀] A := by
      have hNhd : W ∩ Metric.ball (0 : ℂ) 1 ∈ 𝓝 w₀ :=
        (hWopen.inter Metric.isOpen_ball).mem_nhds ⟨hw₀W, hw₀Lens.1⟩
      filter_upwards [hNhd] with z hz
      have hzO := connectedComponentIn_subset O w hz.1
      have hzLocalBig := hzO.1
      have hzDistBig : dist z 1 < rBig ^ 2 := by
        have hsqrt : ‖Transfer.cartesianDeltaSqrt z‖ < rBig := by
          have hzBall := hzLocalBig.2
          change Transfer.cartesianDeltaSqrt z ∈
            Metric.ball (0 : ℂ) rBig at hzBall
          simpa only [Metric.mem_ball, dist_zero_right] using hzBall
        have hsquare : ‖Transfer.cartesianDeltaSqrt z‖ ^ 2 = ‖1 - z‖ := by
          rw [← norm_pow, Transfer.cartesianDeltaSqrt_sq]
        rw [Complex.dist_eq, norm_sub_rev]
        rw [← hsquare]
        nlinarith [norm_nonneg (Transfer.cartesianDeltaSqrt z)]
      have hzLensF : z ∈ Metric.ball (0 : ℂ) 1 ∩
          Metric.ball (1 : ℂ) (rF ^ 2) := by
        refine ⟨hz.2, ?_⟩
        rw [Metric.mem_ball]
        exact hzDistBig.trans_le
          ((sq_le_sq₀ hrBig.le (hrBig.le.trans hrBigF)).mpr hrBigF)
      have hFEGF := hFLens hzLensF
      have hthetaEq := hthetaInside hz.2
      change F z =
        PerronWright.JointSimpleCycleEGF.profileSimpleCycleSeries M (theta z)
      rw [hFEGF, ZF.zeroFieldUnicyclicEGF, hthetaEq]
    have hEqW : Set.EqOn F A W :=
      hFW.eqOn_of_preconnected_of_eventuallyEq hAW hWpre hw₀W hEqNhd
    exact hEqW hwW

  let G : ℂ → ℂ :=
    AnalyticTwoChartGluing.glueOn
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 rSmall) F A
  have hGunion : AnalyticOnNhd ℂ G
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 rSmall ∪
        Metric.thickening t K) := by
    exact AnalyticTwoChartGluing.analyticOnNhd_glueOn_union
      (TreeNormalizedFoldActivity.isOpen_localCartesianDelta (by norm_num))
      Metric.isOpen_thickening hFSmall hA hOverlap
  have hGDelta : AnalyticOnNhd ℂ G
      (Transfer.cartesianDelta eta 0) :=
    fun w hw ↦ hGunion w (hDeltaCover hw)
  have hGleft : Set.EqOn G F
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 rSmall) :=
    AnalyticTwoChartGluing.glueOn_eqOn_left _ _ _
  have hGright : Set.EqOn G A (Metric.thickening t K) :=
    AnalyticTwoChartGluing.glueOn_eqOn_right_of_eqOn_inter hOverlap
  have hGinside : Set.EqOn G (ZF.zeroFieldUnicyclicEGF M)
      (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    have hwDelta : w ∈ Transfer.cartesianDelta eta 0 :=
      Transfer.unit_ball_subset_cartesianDelta heta hw
    rcases hDeltaCover hwDelta with hwLocal | hwAway
    · rw [hGleft hwLocal]
      apply hFLens
      refine ⟨hw, ?_⟩
      have hsqrt : ‖Transfer.cartesianDeltaSqrt w‖ < rSmall := by
        have hwBall := hwLocal.2
        change Transfer.cartesianDeltaSqrt w ∈
          Metric.ball (0 : ℂ) rSmall at hwBall
        simpa only [Metric.mem_ball, dist_zero_right] using hwBall
      have hsquare : ‖Transfer.cartesianDeltaSqrt w‖ ^ 2 = ‖1 - w‖ := by
        rw [← norm_pow, Transfer.cartesianDeltaSqrt_sq]
      rw [Metric.mem_ball, Complex.dist_eq, norm_sub_rev, ← hsquare]
      have hs : rSmall ^ 2 ≤ rF ^ 2 :=
        (sq_le_sq₀ hrSmall.le (hrSmall.le.trans hrSmallF)).mpr hrSmallF
      nlinarith [norm_nonneg (Transfer.cartesianDeltaSqrt w)]
    · rw [hGright hwAway]
      change PerronWright.JointSimpleCycleEGF.profileSimpleCycleSeries M
        (theta w) = ZF.zeroFieldUnicyclicEGF M w
      rw [hthetaInside hw]
      rfl
  have hESmall : AnalyticOnNhd ℂ E
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 rSmall) := by
    intro w hw
    exact hE w ⟨hw.1, Metric.ball_subset_ball hrSmallF hw.2⟩
  have hGFormula : ∀ w ∈
      TreeNormalizedFoldActivity.localCartesianDelta 1 0 rSmall,
      G w = -(1 / 4 : ℂ) * Complex.log (1 - w) + E w + H₁ := by
    intro w hw
    rw [hGleft hw]
    exact hFormula w ⟨hw.1, Metric.ball_subset_ball hrSmallF hw.2⟩
  exact ⟨H₁, E, G, eta, rSmall, heta, hrSmall, hESmall, hGDelta,
    hGinside, hGFormula, hEO⟩

end PerronWright.ZeroFieldUnicyclicDeltaContinuation
