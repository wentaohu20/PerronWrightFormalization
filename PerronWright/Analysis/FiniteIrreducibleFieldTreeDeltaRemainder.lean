import PerronWright.Analysis.FiniteIrreducibleFieldTreeJointFoldExpansion
import PerronWright.Analysis.FiniteIrreducibleFieldTreeEGFMatching

/-!
# Joint-field tree expansion and a uniform Cartesian-Delta remainder

The global dissymmetry profile and the local joint fold germ are constructed
independently in the preceding files.  This file identifies them on the
chosen Cartesian-Delta square-root sheet.  Thus the *same* global function
has the local expansion

`C(g) + A2(g) (1-w) + A3(g) X(w)^3 + (1-w)^2 R(g,X(w))`.

After passing to a smaller positive-opening Cartesian Delta-domain, the
remainder after the first three displayed terms is bounded uniformly by
`B * |1-w|^2` on one genuine complex field ball.

The away-from-one estimate does **not** use compactness of the (generally
infinite-dimensional) field ball.  Instead, joint analyticity is restricted
to the compact zero-field spine `K x {0}`.  A thickening of that compact
spine supplies one common field radius and one common bound.  The near part
uses local boundedness of the genuine jointly analytic fold remainder `R`.
-/

open Filter Topology Set
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.FiniteIrreducibleFieldTreeDeltaRemainder

namespace Global

export PerronWright.FiniteIrreducibleFieldTreeEGFMatching
  (normalizedFieldTreeFMS
    exists_normalizedFieldTree_global_profile_with_TaylorSeries)

end Global

namespace Joint

export PerronWright.FiniteIrreducibleFieldTreeJointFoldExpansion
  (jointFoldTreeFunction exists_jointFoldTreeFunction_cubic_expansion)

end Joint

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- A compact collar containing the part of a positive-opening Cartesian
Delta-domain which stays a fixed distance from `1`. -/
private def cartesianDeltaAwayCompact (eta m delta : ℝ) : Set ℂ :=
  Metric.closedBall (0 : ℂ) (1 + eta) ∩
    {w : ℂ | delta ≤ dist w 1} ∩
      ({w : ℂ | (w - 1).re ≤ 0} ∪
        {w : ℂ | m * (w - 1).re ≤ |(w - 1).im|})

private theorem isCompact_cartesianDeltaAwayCompact
    (eta m delta : ℝ) :
    IsCompact (cartesianDeltaAwayCompact eta m delta) := by
  have haway : IsClosed {w : ℂ | delta ≤ dist w 1} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hleft : IsClosed {w : ℂ | (w - 1).re ≤ 0} :=
    isClosed_le (by fun_prop) continuous_const
  have hangular : IsClosed
      {w : ℂ | m * (w - 1).re ≤ |(w - 1).im|} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact ((isCompact_closedBall (0 : ℂ) (1 + eta)).inter_right
    haway).inter_right (hleft.union hangular)

private theorem cartesianDelta_away_subset_compact
    {eta m delta : ℝ} :
    {w : ℂ | w ∈ Transfer.cartesianDelta eta m ∧ delta ≤ dist w 1} ⊆
      cartesianDeltaAwayCompact eta m delta := by
  intro w hw
  refine ⟨⟨?_, hw.2⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1.1.le
  · by_cases hleft : (w - 1).re ≤ 0
    · exact Or.inl hleft
    · refine Or.inr ?_
      by_contra hangular
      apply hw.1.2
      exact ⟨(lt_of_not_ge hleft).le, (lt_of_not_ge hangular).le⟩

/-- Increasing the cone opening and shrinking the radial margin embeds a
Cartesian Delta-domain into the original slit domain. -/
private theorem cartesianDelta_subset_slit
    {eta eta₀ m : ℝ} (heta : eta ≤ eta₀) (hm : 0 ≤ m) :
    Transfer.cartesianDelta eta m ⊆
      Transfer.cartesianDelta eta₀ 0 := by
  intro w hw
  refine ⟨by linarith [hw.1], ?_⟩
  rintro ⟨hre, him⟩
  apply hw.2
  refine ⟨hre, ?_⟩
  have him0 : |(w - 1).im| = 0 := by
    have : |(w - 1).im| ≤ 0 := by simpa using him
    exact le_antisymm this (abs_nonneg _)
  rw [him0]
  exact mul_nonneg hm hre

/-- The compact collar of a strictly smaller positive-opening domain lies
inside the original slit Delta-domain. -/
private theorem cartesianDeltaAwayCompact_subset_slit
    {eta eta₀ m delta : ℝ} (heta : eta < eta₀)
    (hm : 0 < m) (hdelta : 0 < delta) :
    cartesianDeltaAwayCompact eta m delta ⊆
      Transfer.cartesianDelta eta₀ 0 := by
  intro w hw
  refine ⟨?_, ?_⟩
  · have hnorm : ‖w‖ ≤ 1 + eta := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1.1
    linarith
  · rintro ⟨hre, him⟩
    have himAbs : |(w - 1).im| = 0 := by
      have : |(w - 1).im| ≤ 0 := by simpa using him
      exact le_antisymm this (abs_nonneg _)
    have hreEq : (w - 1).re = 0 := by
      rcases hw.2 with hleft | hangular
      · exact le_antisymm hleft hre
      · have hprod : m * (w - 1).re ≤ 0 := by
          change m * (w - 1).re ≤ |(w - 1).im| at hangular
          rw [himAbs] at hangular
          exact hangular
        nlinarith
    have himEq : (w - 1).im = 0 := abs_eq_zero.mp himAbs
    have hw1 : w = 1 := by
      have : w - 1 = 0 := by
        apply Complex.ext
        · simpa using hreEq
        · simpa using himEq
      exact sub_eq_zero.mp this
    subst w
    have haway := hw.1.2
    change delta ≤ dist (1 : ℂ) 1 at haway
    rw [dist_self] at haway
    exact (not_le_of_gt hdelta) haway

/-- A continuous map on an open neighborhood of a compact zero-parameter
spine is uniformly bounded after shrinking the transverse parameter ball.

Only the spine `K x {0}` is compact.  This lemma deliberately makes no
compactness claim about `Metric.ball 0 epsilon` in `E`. -/
private theorem exists_uniform_bound_on_compact_spine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {K : Set ℂ} (hK : IsCompact K)
    {D : Set (ℂ × E)} (hDopen : IsOpen D)
    {F : ℂ × E → ℂ} (hF : ContinuousOn F D)
    (hspine : K ×ˢ {(0 : E)} ⊆ D) :
    ∃ epsilon B : ℝ, 0 < epsilon ∧ 0 < B ∧
      ∀ w ∈ K, ∀ g ∈ Metric.ball (0 : E) epsilon,
        ‖F (w, g)‖ ≤ B := by
  let K₀ : Set (ℂ × E) := K ×ˢ {(0 : E)}
  have hK₀ : IsCompact K₀ := hK.prod isCompact_singleton
  have hFK₀ : ContinuousOn F K₀ := hF.mono hspine
  obtain ⟨A, hA⟩ := bddAbove_def.mp
    (hK₀.bddAbove_image hFK₀.norm)
  let B : ℝ := max A 0 + 1
  have hB : 0 < B := by
    dsimp only [B]
    linarith [le_max_right A 0]
  let V : Set (ℂ × E) := D ∩ F ⁻¹' Metric.ball (0 : ℂ) B
  have hVopen : IsOpen V := by
    dsimp only [V]
    exact hF.isOpen_inter_preimage hDopen Metric.isOpen_ball
  have hK₀V : K₀ ⊆ V := by
    intro q hq
    refine ⟨hspine hq, ?_⟩
    have hnorm : ‖F q‖ ≤ A :=
      hA ‖F q‖ (mem_image_of_mem (fun z : ℂ × E ↦ ‖F z‖) hq)
    have hlt : ‖F q‖ < B := by
      dsimp only [B]
      linarith [le_max_left A 0]
    change dist (F q) 0 < B
    simpa only [dist_zero_right] using hlt
  obtain ⟨epsilon, hepsilon, hthick⟩ :=
    hK₀.exists_thickening_subset_open hVopen hK₀V
  refine ⟨epsilon, B, hepsilon, hB, ?_⟩
  intro w hw g hg
  have hqthick : (w, g) ∈ Metric.thickening epsilon K₀ := by
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(w, (0 : E)), ⟨hw, Set.mem_singleton _⟩, ?_⟩
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by simpa using hepsilon,
      by simpa only [Metric.mem_ball] using hg⟩
  have hqV := hthick hqthick
  have hball : F (w, g) ∈ Metric.ball (0 : ℂ) B := hqV.2
  simpa only [dist_zero_right] using (Metric.mem_ball.mp hball).le

/-- The local joint fold expansion belongs to the same global
Cartesian-Delta continuation whose Taylor series is the literal normalized
complex-field tree EGF. -/
theorem exists_normalizedFieldTree_global_joint_fold_expansion
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ (C A₂ A₃ : C(S, ℂ) → ℂ)
      (R : C(S, ℂ) × ℂ → ℂ)
      (G : ℂ × C(S, ℂ) → ℂ) (eta r s : ℝ),
      0 < eta ∧ 0 < r ∧ 0 < s ∧
      AnalyticAt ℂ C 0 ∧ AnalyticAt ℂ A₂ 0 ∧
      AnalyticAt ℂ A₃ 0 ∧ AnalyticAt ℂ R (0, 0) ∧
      A₂ 0 = -1 ∧
      A₃ 0 = 2 * (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) / 3 ∧
      AnalyticOnNhd ℂ G
        (Transfer.cartesianDelta eta 0 ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        HasFPowerSeriesAt (fun w : ℂ ↦ G (w, g))
          (Global.normalizedFieldTreeFMS M hM g) 0) ∧
      ∀ q ∈ FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        G q = C q.2 + A₂ q.2 * (1 - q.1) +
          A₃ q.2 * Transfer.cartesianDeltaSqrt q.1 ^ 3 +
          (1 - q.1) ^ 2 *
            R (q.2, Transfer.cartesianDeltaSqrt q.1) := by
  obtain ⟨eta, rG, sG, Theta, G, heta, hrG, hsG, hTheta, hG,
      hData, hThetaFold, hGdef, hGfold, hGinside, hderiv, hTaylor⟩ :=
    Global.exists_normalizedFieldTree_global_profile_with_TaylorSeries M hM
  obtain ⟨C, A₂, A₃, R, hC, hA₂, hA₃, hR,
      hA₂zero, hA₃zero, hExpansion⟩ :=
    Joint.exists_jointFoldTreeFunction_cubic_expansion M hM
  obtain ⟨rE, hrE, hExpansionBall⟩ :=
    Metric.mem_nhds_iff.mp hExpansion
  let r : ℝ := min rG rE
  let s : ℝ := min sG rE
  have hr : 0 < r := lt_min hrG hrE
  have hs : 0 < s := lt_min hsG hrE
  refine ⟨C, A₂, A₃, R, G, eta, r, s, heta, hr, hs,
    hC, hA₂, hA₃, hR, hA₂zero, hA₃zero, ?_, ?_, ?_⟩
  · intro q hq
    exact hG q ⟨hq.1,
      Metric.ball_subset_ball (min_le_left sG rE) hq.2⟩
  · intro g hg
    exact hTaylor g
      (Metric.ball_subset_ball (min_le_left sG rE) hg)
  · intro q hq
    let X : ℂ := Transfer.cartesianDeltaSqrt q.1
    have hqGlobal : q ∈
        FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 rG ×ˢ
          Metric.ball (0 : C(S, ℂ)) sG := by
      exact ⟨⟨hq.1.1,
          Metric.ball_subset_ball (min_le_left rG rE) hq.1.2⟩,
        Metric.ball_subset_ball (min_le_left sG rE) hq.2⟩
    have hpair : (q.2, X) ∈
        Metric.ball ((0 : C(S, ℂ)), (0 : ℂ)) rE := by
      rw [← ball_prod_same]
      exact ⟨Metric.ball_subset_ball (min_le_right sG rE) hq.2,
        Metric.ball_subset_ball (min_le_right rG rE) hq.1.2⟩
    have hlocal := hExpansionBall hpair
    have hsame : G q = Joint.jointFoldTreeFunction M hM (q.2, X) := by
      rw [hGfold hqGlobal]
      rfl
    rw [hsame, hlocal]
    have hXsq : X ^ 2 = 1 - q.1 :=
      Transfer.cartesianDeltaSqrt_sq q.1
    have hXfour : X ^ 4 = (1 - q.1) ^ 2 := by
      rw [show X ^ 4 = (X ^ 2) ^ 2 by ring, hXsq]
    rw [hXsq, hXfour]

/-- On one positive-opening Cartesian Delta-domain and one genuine complex
field ball, the remainder after the field-dependent affine and cubic fold
terms is uniformly `O(|1-w|^2)`.

The conclusion also retains the exact Taylor-series identification with the
literal normalized field-tree EGF. -/
theorem exists_normalizedFieldTree_cartesianDelta_transfer_data
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ (C A₂ A₃ : C(S, ℂ) → ℂ)
      (G H : ℂ × C(S, ℂ) → ℂ) (eta m s B : ℝ),
      0 < eta ∧ 0 < m ∧ m < 4 / 3 ∧ 0 < s ∧ 0 < B ∧
      AnalyticOnNhd ℂ C (Metric.ball (0 : C(S, ℂ)) s) ∧
      AnalyticOnNhd ℂ A₂ (Metric.ball (0 : C(S, ℂ)) s) ∧
      AnalyticOnNhd ℂ A₃ (Metric.ball (0 : C(S, ℂ)) s) ∧
      A₂ 0 = -1 ∧
      A₃ 0 = 2 * (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) / 3 ∧
      AnalyticOnNhd ℂ G
        (Transfer.cartesianDelta eta m ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      AnalyticOnNhd ℂ H
        (Transfer.cartesianDelta eta m ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ q : ℂ × C(S, ℂ),
        G q = C q.2 + A₂ q.2 * (1 - q.1) +
          A₃ q.2 * Transfer.cartesianDeltaSqrt q.1 ^ 3 + H q) ∧
      (∀ q ∈ Transfer.cartesianDelta eta m ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        ‖H q‖ ≤ B * ‖q.1 - 1‖ ^ (2 : ℝ)) ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        HasFPowerSeriesAt (fun w : ℂ ↦ G (w, g))
          (Global.normalizedFieldTreeFMS M hM g) 0 := by
  obtain ⟨C, A₂, A₃, R, G, eta₀, r₀, s₀,
      heta₀, hr₀, hs₀, hC, hA₂, hA₃, hR,
      hA₂zero, hA₃zero, hG, hTaylor, hLocal⟩ :=
    exists_normalizedFieldTree_global_joint_fold_expansion M hM

  obtain ⟨sC, hsC, hCball⟩ :=
    Metric.mem_nhds_iff.mp hC.eventually_analyticAt
  obtain ⟨sA₂, hsA₂, hA₂ball⟩ :=
    Metric.mem_nhds_iff.mp hA₂.eventually_analyticAt
  obtain ⟨sA₃, hsA₃, hA₃ball⟩ :=
    Metric.mem_nhds_iff.mp hA₃.eventually_analyticAt
  let sBase : ℝ := min s₀ (min sC (min sA₂ sA₃))
  have hsBase : 0 < sBase := by
    dsimp only [sBase]
    positivity
  have hsBase_s₀ : sBase ≤ s₀ := min_le_left s₀ _
  have hsBase_sC : sBase ≤ sC :=
    (min_le_right s₀ (min sC (min sA₂ sA₃))).trans
      (min_le_left sC (min sA₂ sA₃))
  have hsBase_sA₂ : sBase ≤ sA₂ :=
    (min_le_right s₀ (min sC (min sA₂ sA₃))).trans
      ((min_le_right sC (min sA₂ sA₃)).trans
        (min_le_left sA₂ sA₃))
  have hsBase_sA₃ : sBase ≤ sA₃ :=
    (min_le_right s₀ (min sC (min sA₂ sA₃))).trans
      ((min_le_right sC (min sA₂ sA₃)).trans
        (min_le_right sA₂ sA₃))

  let P : ℂ × C(S, ℂ) → ℂ := fun q ↦
    C q.2 + A₂ q.2 * (1 - q.1) +
      A₃ q.2 * Transfer.cartesianDeltaSqrt q.1 ^ 3
  let H : ℂ × C(S, ℂ) → ℂ := fun q ↦ G q - P q
  let D : Set (ℂ × C(S, ℂ)) :=
    Transfer.cartesianDelta eta₀ 0 ×ˢ
      Metric.ball (0 : C(S, ℂ)) sBase

  have hDopen : IsOpen D := by
    dsimp only [D]
    exact (Transfer.isOpen_cartesianDelta eta₀ 0).prod Metric.isOpen_ball
  have hP : AnalyticOnNhd ℂ P D := by
    intro q hq
    have hCg : AnalyticAt ℂ C q.2 :=
      hCball (Metric.ball_subset_ball hsBase_sC hq.2)
    have hA₂g : AnalyticAt ℂ A₂ q.2 :=
      hA₂ball (Metric.ball_subset_ball hsBase_sA₂ hq.2)
    have hA₃g : AnalyticAt ℂ A₃ q.2 :=
      hA₃ball (Metric.ball_subset_ball hsBase_sA₃ hq.2)
    have hX : AnalyticAt ℂ
        (fun p : ℂ × C(S, ℂ) ↦
          Transfer.cartesianDeltaSqrt p.1) q :=
      ((Transfer.analyticOnNhd_cartesianDeltaSqrt
        (m := (0 : ℝ)) (by norm_num) q.1 hq.1).comp_of_eq
          analyticAt_fst rfl)
    have hCg' := hCg.comp_of_eq analyticAt_snd rfl
    have hA₂g' := hA₂g.comp_of_eq analyticAt_snd rfl
    have hA₃g' := hA₃g.comp_of_eq analyticAt_snd rfl
    dsimp only [P]
    exact (hCg'.add
      (hA₂g'.mul (analyticAt_const.sub analyticAt_fst))).add
        (hA₃g'.mul (hX.pow 3))
  have hH : AnalyticOnNhd ℂ H D := by
    intro q hq
    exact (hG q ⟨hq.1,
      Metric.ball_subset_ball hsBase_s₀ hq.2⟩).sub (hP q hq)

  let Bnear : ℝ := ‖R (0, 0)‖ + 1
  have hBnear : 0 < Bnear := by
    dsimp only [Bnear]
    positivity
  have hRboundedNhd : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      ‖R q‖ ≤ Bnear := by
    have hclose : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        R q ∈ Metric.ball (R (0, 0)) 1 :=
      hR.continuousAt (Metric.ball_mem_nhds (R (0, 0)) zero_lt_one)
    filter_upwards [hclose] with q hq
    have htri : ‖R q‖ ≤ ‖R q - R (0, 0)‖ + ‖R (0, 0)‖ := by
      have := norm_add_le (R q - R (0, 0)) (R (0, 0))
      simpa only [sub_add_cancel] using this
    have hdist : ‖R q - R (0, 0)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hq
    exact htri.trans (by dsimp only [Bnear]; linarith)
  obtain ⟨rB, hrB, hRboundBall⟩ :=
    Metric.eventually_nhds_iff.mp hRboundedNhd

  let delta : ℝ := min (r₀ ^ 2) (rB ^ 2) / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hdeltar₀ : delta < r₀ ^ 2 := by
    dsimp only [delta]
    have := min_le_left (r₀ ^ 2) (rB ^ 2)
    nlinarith [sq_pos_of_pos hr₀]
  have hdeltarB : delta < rB ^ 2 := by
    dsimp only [delta]
    have := min_le_right (r₀ ^ 2) (rB ^ 2)
    nlinarith [sq_pos_of_pos hrB]

  let eta : ℝ := min (eta₀ / 2) (1 / 2)
  let m : ℝ := 1 / 2
  have heta : 0 < eta := by
    dsimp only [eta]
    exact lt_min (half_pos heta₀) (by norm_num)
  have heta_eta₀ : eta < eta₀ := by
    exact (min_le_left (eta₀ / 2) (1 / 2)).trans_lt
      (half_lt_self heta₀)
  have heta_one : eta ≤ 1 := by
    dsimp only [eta]
    linarith [min_le_right (eta₀ / 2) (1 / 2)]
  have hm : 0 < m := by norm_num [m]
  have hm43 : m < 4 / 3 := by norm_num [m]
  have hsmallSub : Transfer.cartesianDelta eta m ⊆
      Transfer.cartesianDelta eta₀ 0 :=
    cartesianDelta_subset_slit heta_eta₀.le hm.le
  have hsmallSubLocal : Transfer.cartesianDelta eta m ⊆
      Transfer.cartesianDelta 1 0 :=
    cartesianDelta_subset_slit heta_one hm.le

  let K : Set ℂ := cartesianDeltaAwayCompact eta m delta
  have hKcompact : IsCompact K := by
    simpa only [K] using
      isCompact_cartesianDeltaAwayCompact eta m delta
  have hKsub : K ⊆ Transfer.cartesianDelta eta₀ 0 := by
    simpa only [K] using
      (cartesianDeltaAwayCompact_subset_slit heta_eta₀ hm hdelta)
  have hKspine : K ×ˢ {(0 : C(S, ℂ))} ⊆ D := by
    rintro ⟨w, g⟩ ⟨hw, hg⟩
    have hg0 : g = 0 := by simpa only [Set.mem_singleton_iff] using hg
    subst g
    exact ⟨hKsub hw, Metric.mem_ball_self hsBase⟩
  obtain ⟨sAway, Bspine, hsAway, hBspine, hAwayNumerator⟩ :=
    exists_uniform_bound_on_compact_spine hKcompact hDopen
      hH.continuousOn hKspine

  let sNear : ℝ := min sBase rB
  let s : ℝ := min sNear sAway
  have hsNear : 0 < sNear := lt_min hsBase hrB
  have hs : 0 < s := lt_min hsNear hsAway

  let deltaSq : ℝ := delta ^ 2
  have hdeltaSq : 0 < deltaSq := sq_pos_of_pos hdelta
  let Baway : ℝ := Bspine / deltaSq
  have hBaway : 0 < Baway := div_pos hBspine hdeltaSq
  have hawayBound : ∀ q ∈ Transfer.cartesianDelta eta m ×ˢ
      Metric.ball (0 : C(S, ℂ)) s,
      delta ≤ dist q.1 1 →
      ‖H q‖ ≤ Baway * ‖q.1 - 1‖ ^ (2 : ℝ) := by
    intro q hq haway
    have hwK : q.1 ∈ K := by
      apply cartesianDelta_away_subset_compact
      exact ⟨hq.1, haway⟩
    have hgAway : q.2 ∈ Metric.ball (0 : C(S, ℂ)) sAway :=
      Metric.ball_subset_ball
        ((min_le_right sNear sAway)) hq.2
    have hnum : ‖H q‖ ≤ Bspine :=
      hAwayNumerator q.1 hwK q.2 hgAway
    have hnorm : delta ≤ ‖q.1 - 1‖ := by
      simpa only [Complex.dist_eq] using haway
    have hpow : deltaSq ≤ ‖q.1 - 1‖ ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      dsimp only [deltaSq]
      nlinarith [norm_nonneg (q.1 - 1)]
    calc
      ‖H q‖ ≤ Bspine := hnum
      _ = Baway * deltaSq := by
        dsimp only [Baway]
        field_simp [hdeltaSq.ne']
      _ ≤ Baway * ‖q.1 - 1‖ ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow hBaway.le

  have hnearBound : ∀ q ∈ Transfer.cartesianDelta eta m ×ˢ
      Metric.ball (0 : C(S, ℂ)) s,
      dist q.1 1 < delta →
      ‖H q‖ ≤ Bnear * ‖q.1 - 1‖ ^ (2 : ℝ) := by
    intro q hq hnear
    let X : ℂ := Transfer.cartesianDeltaSqrt q.1
    have hXsqNorm : ‖X‖ ^ 2 = ‖1 - q.1‖ := by
      rw [← norm_pow, Transfer.cartesianDeltaSqrt_sq]
    have hdist : ‖1 - q.1‖ < delta := by
      simpa only [Complex.dist_eq, norm_sub_rev] using hnear
    have hXr₀ : ‖X‖ < r₀ := by
      nlinarith [norm_nonneg X, sq_pos_of_pos hr₀, hdeltar₀]
    have hXrB : ‖X‖ < rB := by
      nlinarith [norm_nonneg X, sq_pos_of_pos hrB, hdeltarB]
    have hgBase : q.2 ∈ Metric.ball (0 : C(S, ℂ)) sBase :=
      Metric.ball_subset_ball
        ((min_le_left sNear sAway).trans (min_le_left sBase rB)) hq.2
    have hgLocal : q.2 ∈ Metric.ball (0 : C(S, ℂ)) s₀ :=
      Metric.ball_subset_ball (min_le_left s₀ _) hgBase
    have hwLocal : q.1 ∈
        FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r₀ := by
      refine ⟨hsmallSubLocal hq.1, ?_⟩
      change X ∈ Metric.ball (0 : ℂ) r₀
      simpa only [Metric.mem_ball, dist_zero_right] using hXr₀
    have hpair : (q.2, X) ∈
        Metric.ball ((0 : C(S, ℂ)), (0 : ℂ)) rB := by
      rw [← ball_prod_same]
      refine ⟨?_, ?_⟩
      · exact Metric.ball_subset_ball
          ((min_le_left sNear sAway).trans (min_le_right sBase rB)) hq.2
      · simpa only [Metric.mem_ball, dist_zero_right] using hXrB
    have hRX : ‖R (q.2, X)‖ ≤ Bnear := hRboundBall hpair
    have hHEq : H q = (1 - q.1) ^ 2 * R (q.2, X) := by
      have hloc := hLocal q ⟨hwLocal, hgLocal⟩
      dsimp only [H, P]
      rw [hloc]
      ring
    calc
      ‖H q‖ = ‖1 - q.1‖ ^ 2 * ‖R (q.2, X)‖ := by
        rw [hHEq, norm_mul, norm_pow]
      _ ≤ ‖1 - q.1‖ ^ 2 * Bnear :=
        mul_le_mul_of_nonneg_left hRX (sq_nonneg ‖1 - q.1‖)
      _ = Bnear * ‖q.1 - 1‖ ^ (2 : ℝ) := by
        rw [Real.rpow_two, norm_sub_rev]
        ring

  let B : ℝ := max 1 (max Bnear Baway)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  have hBnearB : Bnear ≤ B :=
    (le_max_left Bnear Baway).trans (le_max_right 1 (max Bnear Baway))
  have hBawayB : Baway ≤ B :=
    (le_max_right Bnear Baway).trans (le_max_right 1 (max Bnear Baway))
  have hglobalBound : ∀ q ∈ Transfer.cartesianDelta eta m ×ˢ
      Metric.ball (0 : C(S, ℂ)) s,
      ‖H q‖ ≤ B * ‖q.1 - 1‖ ^ (2 : ℝ) := by
    intro q hq
    by_cases hnear : dist q.1 1 < delta
    · exact (hnearBound q hq hnear).trans
        (mul_le_mul_of_nonneg_right hBnearB
          (Real.rpow_nonneg (norm_nonneg _) _))
    · exact (hawayBound q hq (le_of_not_gt hnear)).trans
        (mul_le_mul_of_nonneg_right hBawayB
          (Real.rpow_nonneg (norm_nonneg _) _))

  have hfieldBase : Metric.ball (0 : C(S, ℂ)) s ⊆
      Metric.ball (0 : C(S, ℂ)) sBase :=
    Metric.ball_subset_ball
      ((min_le_left sNear sAway).trans (min_le_left sBase rB))
  have hdomain : Transfer.cartesianDelta eta m ×ˢ
      Metric.ball (0 : C(S, ℂ)) s ⊆ D := by
    intro q hq
    exact ⟨hsmallSub hq.1, hfieldBase hq.2⟩
  refine ⟨C, A₂, A₃, G, H, eta, m, s, B,
    heta, hm, hm43, hs, hB, ?_, ?_, ?_, hA₂zero, hA₃zero,
    ?_, ?_, ?_, hglobalBound, ?_⟩
  · intro g hg
    exact hCball (Metric.ball_subset_ball hsBase_sC (hfieldBase hg))
  · intro g hg
    exact hA₂ball
      (Metric.ball_subset_ball hsBase_sA₂ (hfieldBase hg))
  · intro g hg
    exact hA₃ball
      (Metric.ball_subset_ball hsBase_sA₃ (hfieldBase hg))
  · intro q hq
    exact hG q ⟨hsmallSub hq.1,
      Metric.ball_subset_ball hsBase_s₀ (hfieldBase hq.2)⟩
  · exact hH.mono hdomain
  · intro q
    dsimp only [H, P]
    ring
  · intro g hg
    exact hTaylor g
      (Metric.ball_subset_ball hsBase_s₀ (hfieldBase hg))

end PerronWright.FiniteIrreducibleFieldTreeDeltaRemainder
