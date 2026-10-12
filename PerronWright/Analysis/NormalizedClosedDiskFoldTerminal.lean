import PerronWright.Analysis.NormalizedClosedDiskFoldGluing

/-!
# Terminal normalized closed-disk/fold gluing theorem

This module packages the normalized closed-disk continuation, the fold chart,
and the relative overlap geometry into one unconditional existence theorem.
Both charts are explicitly shrunk before they are glued.  Analytic
continuation on their overlap is allowed to use a larger fold neighborhood
with a strict radius margin.

No connectedness assertion is made about the raw maximal overlap of the
original continuation domains.
-/

open Filter Topology
open scoped Classical

noncomputable section

namespace PerronWright.ClosedDiskTerminal

open PerronWright
open PerronWright.TreeNormalizedFoldActivity
open PerronWright.TreeNormalizedUnitAway
open PerronWright.AnalyticTwoChartGluing

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- A compact zero-field activity set contained in an open normalized chart
has a uniform product thickening.  The auxiliary scale `sigma` reserves a
strictly positive margin for the fold geometry. -/
private theorem exists_uniform_normalized_compact_thickening
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {K U : Set ℂ} {ε sigma : ℝ}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hε : 0 < ε) (hsigma : 0 < sigma)
    (hDopen : IsOpen (normalizedUnitAwayDomain M hM U ε)) :
    ∃ r : ℝ, 0 < r ∧ r < sigma ∧
      Metric.thickening r K ×ˢ Metric.ball (0 : C(S, ℂ)) r ⊆
        normalizedUnitAwayDomain M hM U ε := by
  let K₀ : Set (ℂ × C(S, ℂ)) := K ×ˢ {(0 : C(S, ℂ))}
  have hK₀compact : IsCompact K₀ := hK.prod isCompact_singleton
  have hK₀sub : K₀ ⊆ normalizedUnitAwayDomain M hM U ε := by
    rintro ⟨w, g⟩ ⟨hw, hg⟩
    have hg0 : g = 0 := by
      simpa only [Set.mem_singleton_iff] using hg
    subst g
    change activityMap M hM (w, 0) ∈
      U ×ˢ Metric.ball (0 : C(S, ℂ)) ε
    rw [activityMap_zeroField]
    exact ⟨hKU hw, Metric.mem_ball_self hε⟩
  obtain ⟨t, ht, htSub⟩ :=
    hK₀compact.exists_thickening_subset_open hDopen hK₀sub
  let r : ℝ := min t (sigma / 2)
  have hr : 0 < r := lt_min ht (half_pos hsigma)
  have hrSigma : r < sigma :=
    (min_le_right t (sigma / 2)).trans_lt (half_lt_self hsigma)
  refine ⟨r, hr, hrSigma, ?_⟩
  intro q hq
  apply htSub
  obtain ⟨w₀, hw₀, hdistw⟩ := Metric.mem_thickening_iff.mp hq.1
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(w₀, (0 : C(S, ℂ))), ⟨hw₀, Set.mem_singleton _⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨hdistw.trans_le (min_le_left t (sigma / 2)),
    (Metric.mem_ball.mp hq.2).trans_le (min_le_left t (sigma / 2))⟩

/-- There is a normalized analytic profile on the union of an explicitly
shrunken fold product and an explicitly shrunken closed-disk-away product.
The larger radius `rBig` is used only to propagate equality on the smaller
overlap, and `rSmall ^ 2 + s < rBig ^ 2` records the required spare margin.

The auxiliary `epsilon` records that the displayed away domain lies in the
original closed-disk continuation domain.  The glued profile itself is
defined solely on the two displayed shrunken domains. -/
theorem exists_normalizedFold_closedDiskAway_glued_profile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (delta rSmall rBig s epsilon : ℝ) (U : Set ℂ)
        (Psi Theta : ℂ × C(S, ℂ) → C(S, ℂ)),
      0 < delta ∧ 0 < rSmall ∧ 0 < rBig ∧ 0 < s ∧
      0 < epsilon ∧ rSmall ^ 2 + s < rBig ^ 2 ∧
      delta ≤ rSmall ^ 2 ∧
      let K :=
        PerronWright.TreeNormalizedClosedDiskGluing.closedUnitDiskAway delta
      let DFold := localCartesianDelta 1 0 rSmall ×ˢ
        Metric.ball (0 : C(S, ℂ)) s
      let DAway := Metric.thickening s K ×ˢ
        Metric.ball (0 : C(S, ℂ)) s
      IsOpen U ∧ K ⊆ U ∧
      DAway ⊆ normalizedUnitAwayDomain M hM U epsilon ∧
      IsOpen DFold ∧ IsOpen DAway ∧
      AnalyticOnNhd ℂ (activityMap M hM) (DFold ∪ DAway) ∧
      AnalyticOnNhd ℂ Theta (DFold ∪ DAway) ∧
      (∀ q ∈ DFold ∪ DAway,
        RadiusResponse.radius M hM q.2 ≠ 0 ∧
        TreeCritical.residual M (activityMap M hM q, Theta q) = 0) ∧
      Set.EqOn Theta (normalizedFoldProfile M hM) DFold ∧
      Set.EqOn Theta (normalizedUnitAwayProfile M hM Psi) DAway := by
  obtain ⟨ell, hell, hFoldLens⟩ :=
    exists_normalizedFoldProfile_eq_rootedTreeSeries_on_lens M hM
  obtain ⟨rFold, hrFold, -, -, hFoldAnalytic, hFoldData⟩ :=
    exists_normalizedFoldProfile_cartesianDelta_product
      M hM (η := 1) (m := 0) (by norm_num)

  /- The larger overlap radius is strictly inside both the available fold
  chart and the zero-field lens. -/
  let rBig : ℝ := min rFold ell / 2
  have hrBig : 0 < rBig := by
    dsimp only [rBig]
    exact half_pos (lt_min hrFold hell)
  have hrBigFold : rBig < rFold := by
    dsimp only [rBig]
    have hle := min_le_left rFold ell
    nlinarith
  have hrBigEll : rBig ≤ ell := by
    dsimp only [rBig]
    have hle := min_le_right rFold ell
    nlinarith

  /- Choose the closed-disk cutoff only after fixing the fold scale.  This
  makes the two explicitly shrunken charts have a genuine overlap. -/
  let delta : ℝ := min 1 (rBig ^ 2) / 4
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact div_pos (lt_min (by norm_num) (pow_pos hrBig 2)) (by norm_num)
  let K : Set ℂ :=
    PerronWright.TreeNormalizedClosedDiskGluing.closedUnitDiskAway delta

  obtain ⟨U, epsilon, Psi, hUopen, hKU, hepsilon, hClosedOpen,
      hActivity, hClosedAnalytic, hClosedData, hClosedInside,
      hClosedUniq⟩ :=
    PerronWright.TreeNormalizedClosedDiskGluing.exists_normalized_rootedTreeSeries_joint_analytic_continuation_closedDisk_away
        M hM hdelta

  /- The uniform thickening is chosen below the square-radius margin, the
  larger fold field radius, and the closed-disk field radius. -/
  let sigma : ℝ :=
    min (rBig ^ 2 / 4) (min (rBig / 2) (epsilon / 2))
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    exact lt_min (div_pos (pow_pos hrBig 2) (by norm_num))
      (lt_min (half_pos hrBig) (half_pos hepsilon))
  obtain ⟨s, hs, hsSigma, hAwaySub⟩ :=
    exists_uniform_normalized_compact_thickening
      M hM
      (K := K) (U := U) (ε := epsilon) (sigma := sigma)
      (PerronWright.TreeNormalizedClosedDiskGluing.isCompact_closedUnitDiskAway delta)
      hKU hepsilon hsigma hClosedOpen
  have hsSq : s < rBig ^ 2 / 4 := by
    exact hsSigma.trans_le (min_le_left _ _)
  have hsBigHalf : s < rBig / 2 := by
    exact hsSigma.trans_le
      ((min_le_right (rBig ^ 2 / 4)
        (min (rBig / 2) (epsilon / 2))).trans (min_le_left _ _))
  have hsEpsilonHalf : s < epsilon / 2 := by
    exact hsSigma.trans_le
      ((min_le_right (rBig ^ 2 / 4)
        (min (rBig / 2) (epsilon / 2))).trans (min_le_right _ _))
  have hsFold : s < rFold := by
    have : s < rBig := by linarith
    exact this.trans hrBigFold
  have hsEpsilon : s < epsilon := by linarith

  let rSmall : ℝ := rBig / 2
  have hrSmall : 0 < rSmall := half_pos hrBig
  have hdeltaSmall : delta ≤ rSmall ^ 2 := by
    dsimp only [delta, rSmall]
    have hle := min_le_right (1 : ℝ) (rBig ^ 2)
    nlinarith
  have hrSmallBig : rSmall < rBig := half_lt_self hrBig
  have hrSmallFold : rSmall < rFold := hrSmallBig.trans hrBigFold
  have hmargin : rSmall ^ 2 + s < rBig ^ 2 := by
    dsimp only [rSmall]
    nlinarith [pow_pos hrBig 2]

  let DFold : Set (ℂ × C(S, ℂ)) :=
    localCartesianDelta 1 0 rSmall ×ˢ
      Metric.ball (0 : C(S, ℂ)) s
  let DAway : Set (ℂ × C(S, ℂ)) :=
    Metric.thickening s K ×ˢ Metric.ball (0 : C(S, ℂ)) s
  let AComplex : Set ℂ :=
    localCartesianDelta 1 0 rSmall ∩ Metric.thickening s K
  let OComplex : Set ℂ :=
    localCartesianDelta 1 0 rBig ∩ Metric.thickening s K
  let A : Set (ℂ × C(S, ℂ)) :=
    AComplex ×ˢ Metric.ball (0 : C(S, ℂ)) s
  let O : Set (ℂ × C(S, ℂ)) :=
    OComplex ×ˢ Metric.ball (0 : C(S, ℂ)) s
  let Lens : Set ℂ :=
    Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (ell ^ 2)

  have hOComplexOpen : IsOpen OComplex := by
    exact (isOpen_localCartesianDelta (by norm_num)).inter
      Metric.isOpen_thickening
  have hComplexComponents : ∀ w ∈ AComplex, ∃ w₀ : ℂ,
      w₀ ∈ connectedComponentIn OComplex w ∧ w₀ ∈ Lens := by
    simpa only [AComplex, OComplex, Lens, K] using
      (PerronWright.TreeNormalizedClosedDiskGluing.localDelta_thickening_target_components_meet_lens
          (delta := delta) (s := s) (rSmall := rSmall)
          (rBig := rBig) (ell := ell)
          hdelta hs hrSmall hrBig hmargin hrBigEll)
  have hCover : ∀ q ∈ A,
      ∃ (V : Set (ℂ × C(S, ℂ))) (w₀ : ℂ),
        IsOpen V ∧ IsPreconnected V ∧ V ⊆ O ∧ q ∈ V ∧
          (w₀, (0 : C(S, ℂ))) ∈ V ∧ w₀ ∈ Lens := by
    intro q hq
    obtain ⟨w₀, hw₀Component, hw₀Lens⟩ :=
      hComplexComponents q.1 hq.1
    have hqO : q.1 ∈ OComplex :=
      connectedComponentIn_nonempty_iff.mp ⟨w₀, hw₀Component⟩
    refine ⟨connectedComponentIn OComplex q.1 ×ˢ
        Metric.ball (0 : C(S, ℂ)) s, w₀,
      hOComplexOpen.connectedComponentIn.prod Metric.isOpen_ball,
      isPreconnected_connectedComponentIn.prod
        (convex_ball (0 : C(S, ℂ)) s).isPreconnected,
      ?_, ⟨mem_connectedComponentIn hqO, hq.2⟩,
      ⟨hw₀Component, Metric.mem_ball_self hs⟩, hw₀Lens⟩
    exact Set.prod_mono (connectedComponentIn_subset OComplex q.1)
      Set.Subset.rfl

  let PsiClosed : ℂ × C(S, ℂ) → C(S, ℂ) :=
    normalizedUnitAwayProfile M hM Psi

  /- Analytic continuation is performed on `O`, whose fold radius is
  `rBig`.  Only the resulting equality on `A = DFold ∩ DAway` is retained. -/
  have hEqA : Set.EqOn (normalizedFoldProfile M hM) PsiClosed A := by
    intro q hq
    obtain ⟨V, w₀, hVopen, hVpre, hVsub, hqV, hw₀V, hw₀Lens⟩ :=
      hCover q hq
    have hVFold : V ⊆
        localCartesianDelta 1 0 rFold ×ˢ
          Metric.ball (0 : C(S, ℂ)) rFold := by
      intro p hp
      have hpO := hVsub hp
      refine ⟨⟨hpO.1.1.1, ?_⟩, ?_⟩
      · exact Metric.ball_subset_ball (le_of_lt hrBigFold) hpO.1.1.2
      · exact Metric.ball_subset_ball (le_of_lt hsFold) hpO.2
    have hVClosed : V ⊆ normalizedUnitAwayDomain M hM U epsilon := by
      intro p hp
      have hpO := hVsub hp
      exact hAwaySub ⟨hpO.1.2, hpO.2⟩
    have hFoldA : AnalyticOnNhd ℂ (normalizedFoldProfile M hM) V := by
      intro p hp
      exact hFoldAnalytic p (hVFold hp)
    have hClosedA : AnalyticOnNhd ℂ PsiClosed V := by
      intro p hp
      exact hClosedAnalytic p (hVClosed hp)
    let R : ((ℂ × C(S, ℂ)) × C(S, ℂ)) → C(S, ℂ) :=
      fun p => TreeCritical.residual M (activityMap M hM p.1, p.2)
    have hFoldRes : ∀ p ∈ V,
        R (p, normalizedFoldProfile M hM p) = 0 := by
      intro p hp
      exact (hFoldData p (hVFold hp)).2.1
    have hw₀Closed :
        (w₀, (0 : C(S, ℂ))) ∈ normalizedUnitAwayDomain M hM U epsilon :=
      hVClosed hw₀V
    have hw₀U : w₀ ∈ U := by
      change activityMap M hM (w₀, 0) ∈
        U ×ˢ Metric.ball (0 : C(S, ℂ)) epsilon at hw₀Closed
      rw [activityMap_zeroField] at hw₀Closed
      exact hw₀Closed.1
    have hw₀Norm : ‖w₀‖ < 1 := by
      simpa only [Lens, Metric.mem_ball, dist_zero_right] using hw₀Lens.1
    have hClosedSeed : PsiClosed (w₀, 0) = M.rootedTreeSeries w₀ := by
      simpa only [PsiClosed] using hClosedInside w₀ hw₀U hw₀Norm
    have hFoldSeed :
        normalizedFoldProfile M hM (w₀, 0) = M.rootedTreeSeries w₀ := by
      exact hFoldLens hw₀Lens
    have hSeed : PsiClosed (w₀, 0) =
        normalizedFoldProfile M hM (w₀, 0) :=
      hClosedSeed.trans hFoldSeed.symm
    have hClosedLocalUniq : ∀ᶠ p in
        nhds (((w₀, (0 : C(S, ℂ))), PsiClosed (w₀, 0))),
        R p = 0 ↔ PsiClosed p.1 = p.2 := by
      simpa only [R, PsiClosed] using hClosedUniq w₀ hw₀U
    have hClosedEqFold : Set.EqOn PsiClosed
        (normalizedFoldProfile M hM) V :=
      analytic_solutions_agree_on_open_preconnected_overlap_of_local_uniqueness
        R V hVopen hVpre PsiClosed (normalizedFoldProfile M hM)
        hClosedA hFoldA hFoldRes (w₀, 0) hw₀V hSeed hClosedLocalUniq
    exact (hClosedEqFold hqV).symm

  have hEqOverlap : Set.EqOn (normalizedFoldProfile M hM) PsiClosed
      (DFold ∩ DAway) := by
    intro q hq
    apply hEqA
    exact ⟨⟨hq.1.1, hq.2.1⟩, hq.1.2⟩

  let Theta : ℂ × C(S, ℂ) → C(S, ℂ) :=
    glueOn DFold (normalizedFoldProfile M hM) PsiClosed
  have hDFoldOpen : IsOpen DFold :=
    (isOpen_localCartesianDelta (by norm_num)).prod Metric.isOpen_ball
  have hDAwayOpen : IsOpen DAway :=
    Metric.isOpen_thickening.prod Metric.isOpen_ball
  have hFoldSmallA :
      AnalyticOnNhd ℂ (normalizedFoldProfile M hM) DFold := by
    intro q hq
    exact hFoldAnalytic q
      ⟨⟨hq.1.1,
          Metric.ball_subset_ball (le_of_lt hrSmallFold) hq.1.2⟩,
        Metric.ball_subset_ball (le_of_lt hsFold) hq.2⟩
  have hClosedSmallA : AnalyticOnNhd ℂ PsiClosed DAway := by
    intro q hq
    exact hClosedAnalytic q (hAwaySub hq)
  have hThetaA : AnalyticOnNhd ℂ Theta (DFold ∪ DAway) := by
    exact analyticOnNhd_glueOn_union hDFoldOpen hDAwayOpen
      hFoldSmallA hClosedSmallA hEqOverlap
  have hActivitySmall :
      AnalyticOnNhd ℂ (activityMap M hM) (DFold ∪ DAway) := by
    intro q hq
    apply hActivity q
    refine ⟨Set.mem_univ _, ?_⟩
    apply Metric.ball_subset_ball (le_of_lt hsEpsilon)
    rcases hq with hq | hq
    · exact hq.2
    · exact hq.2
  have hFoldSmallData : ∀ q ∈ DFold,
      RadiusResponse.radius M hM q.2 ≠ 0 ∧
      TreeCritical.residual M
        (activityMap M hM q, normalizedFoldProfile M hM q) = 0 := by
    intro q hq
    have hqFull : q ∈ localCartesianDelta 1 0 rFold ×ˢ
        Metric.ball (0 : C(S, ℂ)) rFold :=
      ⟨⟨hq.1.1,
          Metric.ball_subset_ball (le_of_lt hrSmallFold) hq.1.2⟩,
        Metric.ball_subset_ball (le_of_lt hsFold) hq.2⟩
    exact ⟨(hFoldData q hqFull).1, (hFoldData q hqFull).2.1⟩
  have hClosedSmallData : ∀ q ∈ DAway,
      RadiusResponse.radius M hM q.2 ≠ 0 ∧
      TreeCritical.residual M (activityMap M hM q, PsiClosed q) = 0 := by
    intro q hq
    exact hClosedData q (hAwaySub hq)
  have hThetaData : ∀ q ∈ DFold ∪ DAway,
      RadiusResponse.radius M hM q.2 ≠ 0 ∧
      TreeCritical.residual M (activityMap M hM q, Theta q) = 0 := by
    intro q hq
    constructor
    · rcases hq with hq | hq
      · exact (hFoldSmallData q hq).1
      · exact (hClosedSmallData q hq).1
    · exact glueOn_residual_eq_zero_on_union
        (U := DFold) (V := DAway)
        (f := normalizedFoldProfile M hM) (g := PsiClosed)
        (R := fun q y ↦ TreeCritical.residual M (activityMap M hM q, y))
        (fun q hq => (hFoldSmallData q hq).2)
        (fun q hq => (hClosedSmallData q hq).2) q hq
  have hThetaFold : Set.EqOn Theta (normalizedFoldProfile M hM) DFold :=
    glueOn_eqOn_left DFold (normalizedFoldProfile M hM) PsiClosed
  have hThetaAway : Set.EqOn Theta PsiClosed DAway :=
    glueOn_eqOn_right_of_eqOn_inter hEqOverlap

  refine ⟨delta, rSmall, rBig, s, epsilon, U, Psi, Theta,
    hdelta, hrSmall, hrBig, hs, hepsilon, hmargin, hdeltaSmall, ?_⟩
  dsimp only [K, DFold, DAway]
  exact ⟨hUopen, hKU, hAwaySub, hDFoldOpen, hDAwayOpen,
    hActivitySmall, hThetaA, hThetaData, hThetaFold, hThetaAway⟩

end PerronWright.ClosedDiskTerminal
