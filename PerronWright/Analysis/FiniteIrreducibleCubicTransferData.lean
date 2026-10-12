import PerronWright.Analysis.AnalyticVerticalTaylor
import PerronWright.Analysis.FiniteIrreducibleCubicGlobalContinuation
import PerronWright.Transfer.CartesianDeltaSqrtPower

/-!
# Uniform transfer data for the positive-surplus cubic part

The joint cubic continuation has a pole of order `3 * ell` in the fold
coordinate.  This file applies joint vertical Taylor expansion to its
canonical pole-removed numerator.  The finitely many Taylor coefficients
give the complete Puiseux polynomial, while the remaining global function
is uniformly of square-root order on one positive-opening Cartesian
Delta-domain and one genuine complex field ball.

The away-from-one estimate uses compactness only on the zero-field spine.
No compactness of an infinite-dimensional field ball is asserted.
-/

open Filter Topology PerronWright Set
open scoped Classical Topology BigOperators ENNReal NNReal

noncomputable section

namespace PerronWright.FiniteIrreducibleCubicTransferData

open PerronWright.GraphCore PerronWright.FiniteIrreducibleKernelAmplitude

namespace Global

export PerronWright.FiniteIrreducibleCubicGlobalContinuation
  (normalizedFieldCubicPartFMS
   normalizedFieldCubicPartFMS_coeff
   exists_complexFieldCubicPart_cartesianDelta_continuation)

end Global

namespace ZA

export PerronWright.ZeroFieldUnicyclicActivitySingularity
  (cartesianDeltaSqrt_mem_slitPlane
   norm_cartesianDeltaSqrt_eq_rpow)

end ZA

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The finite Puiseux polynomial obtained from the first `3 * ell`
vertical Taylor coefficients of the pole-removed numerator. -/
def positiveSurplusCubicPuiseuxPolynomial
    (ell : ℕ) (a : ℕ → C(S, ℂ) → ℂ)
    (q : ℂ × C(S, ℂ)) : ℂ :=
  ∑ j ∈ Finset.range (3 * ell),
    (Transfer.cartesianDeltaSqrt q.1 ^ (3 * ell - j))⁻¹ * a j q.2

private def cartesianDeltaAwayCompact
    (eta m delta : ℝ) : Set ℂ :=
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

private theorem inv_pow_sub_eq_inv_pow_mul_pow
    {X : ℂ} (hX : X ≠ 0) {j p : ℕ} (hj : j ≤ p) :
    (X ^ (p - j))⁻¹ = (X ^ p)⁻¹ * X ^ j := by
  simpa only [inv_pow] using (inv_pow_sub₀ (a := X) hX hj)

/-- On one positive-opening Cartesian Delta-domain, the actual cubic-part
continuation is its finite Puiseux polynomial, its analytic vertical-degree
`3 * ell` term, and a family-uniform square-root remainder. -/
theorem exists_normalizedFieldCubicPart_cartesianDelta_transfer_data
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ (a : ℕ → C(S, ℂ) → ℂ)
      (G R : ℂ × C(S, ℂ) → ℂ)
      (eta m s B : ℝ),
      0 < eta ∧ 0 < m ∧ m < 4 / 3 ∧ 0 < s ∧ 0 < B ∧
      (∀ j < 3 * ell + 1,
        AnalyticOnNhd ℂ (a j) (Metric.ball (0 : C(S, ℂ)) s)) ∧
      a 0 0 = positiveSurplusCubicEGFConstant ell *
        (Real.sqrt (M.beta hM) : ℂ) ^ ell ∧
      AnalyticOnNhd ℂ G
        (Transfer.cartesianDelta eta m ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      AnalyticOnNhd ℂ R
        (Transfer.cartesianDelta eta m ×ˢ
          Metric.ball (0 : C(S, ℂ)) s) ∧
      (∀ q : ℂ × C(S, ℂ),
        G q = positiveSurplusCubicPuiseuxPolynomial ell a q +
          a (3 * ell) q.2 + R q) ∧
      (∀ q ∈ Transfer.cartesianDelta eta m ×ˢ
          Metric.ball (0 : C(S, ℂ)) s,
        ‖R q‖ ≤ B * ‖q.1 - 1‖ ^ (1 / 2 : ℝ)) ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        HasFPowerSeriesAt (fun w : ℂ ↦ G (w, g))
          (Global.normalizedFieldCubicPartFMS M hM g ell) 0 := by
  obtain ⟨eta₀, r₀, s₀, G, heta₀, hr₀, hs₀, hN,
      hNbase, hG, hTaylor, hLocal⟩ :=
    Global.exists_complexFieldCubicPart_cartesianDelta_continuation
      M hM hell
  let N : C(S, ℂ) × ℂ → ℂ :=
    positiveSurplusCubicAdmissibleIntegratedAmplitude M hM ell
  have hNzero : AnalyticAt ℂ N (0, 0) :=
    hN (0, 0) ⟨Metric.mem_ball_self hs₀, Metric.mem_ball_self hr₀⟩
  obtain ⟨a, Q, ha, hQ, hTaylorVertical⟩ :=
    AnalyticVerticalTaylor.analytic_vertical_taylor hNzero (3 * ell + 1)

  have haEventually : ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      ∀ j : Fin (3 * ell + 1), AnalyticAt ℂ (a j) g := by
    rw [Filter.eventually_all]
    intro j
    exact (ha j j.2).eventually_analyticAt
  obtain ⟨rCoeff, hrCoeff, haBall⟩ :=
    Metric.eventually_nhds_iff.mp haEventually
  obtain ⟨rTaylor, hrTaylor, hTaylorBall⟩ :=
    Metric.eventually_nhds_iff.mp hTaylorVertical

  let Bnear : ℝ := ‖Q (0, 0)‖ + 1
  have hBnear : 0 < Bnear := by
    dsimp only [Bnear]
    positivity
  have hQboundedNhd : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      ‖Q q‖ ≤ Bnear := by
    have hclose : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        Q q ∈ Metric.ball (Q (0, 0)) 1 :=
      hQ.continuousAt (Metric.ball_mem_nhds (Q (0, 0)) zero_lt_one)
    filter_upwards [hclose] with q hq
    have htri : ‖Q q‖ ≤ ‖Q q - Q (0, 0)‖ + ‖Q (0, 0)‖ := by
      have := norm_add_le (Q q - Q (0, 0)) (Q (0, 0))
      simpa only [sub_add_cancel] using this
    have hdist : ‖Q q - Q (0, 0)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hq
    exact htri.trans (by dsimp only [Bnear]; linarith)
  obtain ⟨rBound, hrBound, hQboundBall⟩ :=
    Metric.eventually_nhds_iff.mp hQboundedNhd

  let p : ℕ := 3 * ell
  let sBase : ℝ := min s₀ rCoeff
  have hsBase : 0 < sBase := lt_min hs₀ hrCoeff
  have hsBaseS₀ : sBase ≤ s₀ := min_le_left s₀ rCoeff
  have hsBaseCoeff : sBase ≤ rCoeff := min_le_right s₀ rCoeff
  let P : ℂ × C(S, ℂ) → ℂ :=
    positiveSurplusCubicPuiseuxPolynomial ell a
  let R : ℂ × C(S, ℂ) → ℂ := fun q ↦
    G q - P q - a p q.2
  let D : Set (ℂ × C(S, ℂ)) :=
    Transfer.cartesianDelta eta₀ 0 ×ˢ
      Metric.ball (0 : C(S, ℂ)) sBase
  have hDopen : IsOpen D := by
    dsimp only [D]
    exact (Transfer.isOpen_cartesianDelta eta₀ 0).prod Metric.isOpen_ball
  have hP : AnalyticOnNhd ℂ P D := by
    intro q hq
    have hX : AnalyticAt ℂ
        (fun z : ℂ × C(S, ℂ) ↦
          Transfer.cartesianDeltaSqrt z.1) q :=
      ((Transfer.analyticOnNhd_cartesianDeltaSqrt (m := (0 : ℝ))
        (by norm_num)) q.1 hq.1).comp_of_eq analyticAt_fst rfl
    have hXslit : Transfer.cartesianDeltaSqrt q.1 ∈ Complex.slitPlane :=
      ZA.cartesianDeltaSqrt_mem_slitPlane (m := (0 : ℝ))
        (by norm_num) hq.1
    have hXne : Transfer.cartesianDeltaSqrt q.1 ≠ 0 :=
      (Complex.mem_slitPlane_iff_arg.mp hXslit).2
    have hsum : AnalyticAt ℂ
        (∑ j ∈ Finset.range (3 * ell),
          fun z : ℂ × C(S, ℂ) ↦
            (Transfer.cartesianDeltaSqrt z.1 ^ (3 * ell - j))⁻¹ *
              a j z.2) q := by
      apply Finset.analyticAt_sum
      intro j hj
      have hjlt : j < 3 * ell := Finset.mem_range.mp hj
      have haj : AnalyticAt ℂ (a j) q.2 :=
        haBall (Metric.ball_subset_ball hsBaseCoeff hq.2) ⟨j, by omega⟩
      have haj' : AnalyticAt ℂ (fun z : ℂ × C(S, ℂ) ↦ a j z.2) q :=
        haj.comp_of_eq analyticAt_snd rfl
      exact ((hX.pow (3 * ell - j)).inv
        (pow_ne_zero _ hXne)).mul haj'
    have hfun :
        (∑ j ∈ Finset.range (3 * ell),
          fun z : ℂ × C(S, ℂ) ↦
            (Transfer.cartesianDeltaSqrt z.1 ^ (3 * ell - j))⁻¹ *
              a j z.2) = P := by
      funext z
      dsimp only [P, positiveSurplusCubicPuiseuxPolynomial]
      exact Finset.sum_apply z _ _
    rw [← hfun]
    exact hsum
  have hap : AnalyticOnNhd ℂ (a p)
      (Metric.ball (0 : C(S, ℂ)) sBase) := by
    intro g hg
    exact haBall (Metric.ball_subset_ball hsBaseCoeff hg) ⟨p, by
      dsimp only [p]
      omega⟩
  have hR : AnalyticOnNhd ℂ R D := by
    intro q hq
    have hGq : AnalyticAt ℂ G q :=
      hG q ⟨hq.1, Metric.ball_subset_ball hsBaseS₀ hq.2⟩
    have hapq : AnalyticAt ℂ (fun z : ℂ × C(S, ℂ) ↦ a p z.2) q :=
      (hap q.2 hq.2).comp_of_eq analyticAt_snd rfl
    exact (hGq.sub (hP q hq)).sub hapq

  have hzeroTaylor := hTaylorVertical.self_of_nhds
  have hzeroSum :
      (∑ j ∈ Finset.range (3 * ell + 1),
          (0 : ℂ) ^ j • a j (0 : C(S, ℂ))) = a 0 0 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b hb hb0
      simp [hb0]
    · simp
  have haZero : a 0 0 =
      positiveSurplusCubicEGFConstant ell *
        (Real.sqrt (M.beta hM) : ℂ) ^ ell := by
    have hNe : 3 * ell + 1 ≠ 0 := by omega
    have hNzeroEq : N (0, 0) = a 0 0 := by
      simpa only [Prod.snd_zero, Prod.fst_zero, hzeroSum,
        zero_pow hNe, zero_smul, add_zero] using hzeroTaylor
    rw [← hNzeroEq]
    exact hNbase

  let rLocal : ℝ := min r₀ (min rTaylor rBound)
  have hrLocal : 0 < rLocal := lt_min hr₀ (lt_min hrTaylor hrBound)
  have hrLocalR₀ : rLocal ≤ r₀ := min_le_left r₀ _
  have hrLocalTaylor : rLocal ≤ rTaylor :=
    (min_le_right r₀ _).trans (min_le_left rTaylor rBound)
  have hrLocalBound : rLocal ≤ rBound :=
    (min_le_right r₀ _).trans (min_le_right rTaylor rBound)
  let sNear : ℝ := min sBase (min rTaylor rBound)
  have hsNear : 0 < sNear := lt_min hsBase (lt_min hrTaylor hrBound)
  have hsNearBase : sNear ≤ sBase := min_le_left sBase _
  have hsNearTaylor : sNear ≤ rTaylor :=
    (min_le_right sBase _).trans (min_le_left rTaylor rBound)
  have hsNearBound : sNear ≤ rBound :=
    (min_le_right sBase _).trans (min_le_right rTaylor rBound)

  let delta : ℝ := rLocal ^ 2 / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hdeltarLocal : delta < rLocal ^ 2 := by
    dsimp only [delta]
    nlinarith [sq_pos_of_pos hrLocal]
  let eta : ℝ := min (eta₀ / 2) (1 / 2)
  let m : ℝ := 1 / 2
  have heta : 0 < eta := by
    dsimp only [eta]
    exact lt_min (half_pos heta₀) (by norm_num)
  have hetaEta₀ : eta < eta₀ :=
    (min_le_left (eta₀ / 2) (1 / 2)).trans_lt
      (half_lt_self heta₀)
  have hetaOne : eta ≤ 1 := by
    dsimp only [eta]
    linarith [min_le_right (eta₀ / 2) (1 / 2)]
  have hm : 0 < m := by norm_num [m]
  have hm43 : m < 4 / 3 := by norm_num [m]
  have hsmallSub : Transfer.cartesianDelta eta m ⊆
      Transfer.cartesianDelta eta₀ 0 :=
    cartesianDelta_subset_slit hetaEta₀.le hm.le
  have hsmallSubLocal : Transfer.cartesianDelta eta m ⊆
      Transfer.cartesianDelta 1 0 :=
    cartesianDelta_subset_slit hetaOne hm.le

  let K : Set ℂ := cartesianDeltaAwayCompact eta m delta
  have hKcompact : IsCompact K := by
    simpa only [K] using
      isCompact_cartesianDeltaAwayCompact eta m delta
  have hKsub : K ⊆ Transfer.cartesianDelta eta₀ 0 := by
    simpa only [K] using
      (cartesianDeltaAwayCompact_subset_slit hetaEta₀ hm hdelta)
  have hKspine : K ×ˢ {(0 : C(S, ℂ))} ⊆ D := by
    rintro ⟨w, g⟩ ⟨hw, hg⟩
    have hg0 : g = 0 := by simpa only [Set.mem_singleton_iff] using hg
    subst g
    exact ⟨hKsub hw, Metric.mem_ball_self hsBase⟩
  obtain ⟨sAway, Bspine, hsAway, hBspine, hAwayR⟩ :=
    exists_uniform_bound_on_compact_spine hKcompact hDopen
      hR.continuousOn hKspine
  let s : ℝ := min sNear sAway
  have hs : 0 < s := lt_min hsNear hsAway
  have hsNear' : s ≤ sNear := min_le_left sNear sAway
  have hsAway' : s ≤ sAway := min_le_right sNear sAway
  have hsBase' : s ≤ sBase := hsNear'.trans hsNearBase

  let droot : ℝ := delta ^ (1 / 2 : ℝ)
  have hdroot : 0 < droot := by
    dsimp only [droot]
    exact Real.rpow_pos_of_pos hdelta _
  let Baway : ℝ := Bspine / droot
  have hBaway : 0 < Baway := div_pos hBspine hdroot
  have hawayBound : ∀ q ∈ Transfer.cartesianDelta eta m ×ˢ
      Metric.ball (0 : C(S, ℂ)) s,
      delta ≤ dist q.1 1 →
      ‖R q‖ ≤ Baway * ‖q.1 - 1‖ ^ (1 / 2 : ℝ) := by
    intro q hq haway
    have hwK : q.1 ∈ K := by
      apply cartesianDelta_away_subset_compact
      exact ⟨hq.1, haway⟩
    have hgAway : q.2 ∈ Metric.ball (0 : C(S, ℂ)) sAway :=
      Metric.ball_subset_ball hsAway' hq.2
    have hnum : ‖R q‖ ≤ Bspine := hAwayR q.1 hwK q.2 hgAway
    have hrootle : droot ≤ ‖q.1 - 1‖ ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow hdelta.le
      · simpa only [Complex.dist_eq] using haway
      · norm_num
    calc
      ‖R q‖ ≤ Bspine := hnum
      _ = Baway * droot := by
        dsimp only [Baway]
        field_simp [hdroot.ne']
      _ ≤ Baway * ‖q.1 - 1‖ ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hrootle hBaway.le

  have hnearBound : ∀ q ∈ Transfer.cartesianDelta eta m ×ˢ
      Metric.ball (0 : C(S, ℂ)) s,
      dist q.1 1 < delta →
      ‖R q‖ ≤ Bnear * ‖q.1 - 1‖ ^ (1 / 2 : ℝ) := by
    intro q hq hnear
    let X : ℂ := Transfer.cartesianDeltaSqrt q.1
    have hXsqNorm : ‖X‖ ^ 2 = ‖1 - q.1‖ := by
      rw [← norm_pow, Transfer.cartesianDeltaSqrt_sq]
    have hdist : ‖1 - q.1‖ < delta := by
      simpa only [Complex.dist_eq, norm_sub_rev] using hnear
    have hXLocal : ‖X‖ < rLocal := by
      nlinarith [hXsqNorm, hdist, norm_nonneg X,
        sq_pos_of_pos hrLocal, hdeltarLocal]
    have hXslit : X ∈ Complex.slitPlane :=
      ZA.cartesianDeltaSqrt_mem_slitPlane (m := m) hm.le hq.1
    have hXne : X ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp hXslit).2
    have hpairTaylor : (q.2, X) ∈
        Metric.ball ((0 : C(S, ℂ)), (0 : ℂ)) rTaylor := by
      rw [← ball_prod_same]
      refine ⟨?_, ?_⟩
      · exact Metric.ball_subset_ball
          (hsNear'.trans hsNearTaylor) hq.2
      · have : ‖X‖ < rTaylor := hXLocal.trans_le hrLocalTaylor
        simpa only [Metric.mem_ball, dist_zero_right] using this
    have hpairBound : (q.2, X) ∈
        Metric.ball ((0 : C(S, ℂ)), (0 : ℂ)) rBound := by
      rw [← ball_prod_same]
      refine ⟨?_, ?_⟩
      · exact Metric.ball_subset_ball
          (hsNear'.trans hsNearBound) hq.2
      · have : ‖X‖ < rBound := hXLocal.trans_le hrLocalBound
        simpa only [Metric.mem_ball, dist_zero_right] using this
    have hwLocal : q.1 ∈
        FiniteIrreducibleNormalizedFoldActivity.localCartesianDelta 1 0 r₀ := by
      refine ⟨hsmallSubLocal hq.1, ?_⟩
      change X ∈ Metric.ball (0 : ℂ) r₀
      have : ‖X‖ < r₀ := hXLocal.trans_le hrLocalR₀
      simpa only [Metric.mem_ball, dist_zero_right] using this
    have hGloc := hLocal q ⟨hwLocal,
      Metric.ball_subset_ball (hsBase'.trans hsBaseS₀) hq.2⟩
    have hTaylorLoc := hTaylorBall hpairTaylor
    simp only [smul_eq_mul] at hTaylorLoc
    let T : ℂ := ∑ j ∈ Finset.range p, X ^ j * a j q.2
    have hTaylorSplit : N (q.2, X) =
        T + X ^ p * a p q.2 + X ^ (p + 1) * Q (q.2, X) := by
      simpa only [p, T, Finset.sum_range_succ] using hTaylorLoc
    have hPform : P q = (X ^ p)⁻¹ * T := by
      dsimp only [P, positiveSurplusCubicPuiseuxPolynomial, T]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ p := by
        dsimp only [p]
        exact (Finset.mem_range.mp hj).le
      rw [inv_pow_sub_eq_inv_pow_mul_pow hXne hjle]
      ring
    have hRlocal : R q = X * Q (q.2, X) := by
      dsimp only [R]
      rw [hGloc, hPform]
      change (X ^ p)⁻¹ * N (q.2, X) - (X ^ p)⁻¹ * T -
        a p q.2 = X * Q (q.2, X)
      rw [hTaylorSplit]
      have hpne : X ^ p ≠ 0 := pow_ne_zero _ hXne
      rw [pow_succ]
      (field_simp [hpne]; ring)
    have hQbd : ‖Q (q.2, X)‖ ≤ Bnear := hQboundBall hpairBound
    calc
      ‖R q‖ = ‖X‖ * ‖Q (q.2, X)‖ := by
        rw [hRlocal, norm_mul]
      _ ≤ ‖X‖ * Bnear :=
        mul_le_mul_of_nonneg_left hQbd (norm_nonneg X)
      _ = Bnear * ‖q.1 - 1‖ ^ (1 / 2 : ℝ) := by
        rw [ZA.norm_cartesianDeltaSqrt_eq_rpow, norm_sub_rev]
        ring

  let B : ℝ := max 1 (max Bnear Baway)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  have hBnearB : Bnear ≤ B :=
    (le_max_left Bnear Baway).trans (le_max_right 1 (max Bnear Baway))
  have hBawayB : Baway ≤ B :=
    (le_max_right Bnear Baway).trans (le_max_right 1 (max Bnear Baway))
  have hglobalBound : ∀ q ∈ Transfer.cartesianDelta eta m ×ˢ
      Metric.ball (0 : C(S, ℂ)) s,
      ‖R q‖ ≤ B * ‖q.1 - 1‖ ^ (1 / 2 : ℝ) := by
    intro q hq
    by_cases hnear : dist q.1 1 < delta
    · exact (hnearBound q hq hnear).trans
        (mul_le_mul_of_nonneg_right hBnearB
          (Real.rpow_nonneg (norm_nonneg _) _))
    · exact (hawayBound q hq (le_of_not_gt hnear)).trans
        (mul_le_mul_of_nonneg_right hBawayB
          (Real.rpow_nonneg (norm_nonneg _) _))

  have hfieldSub : Metric.ball (0 : C(S, ℂ)) s ⊆
      Metric.ball (0 : C(S, ℂ)) sBase :=
    Metric.ball_subset_ball hsBase'
  have hdomain : Transfer.cartesianDelta eta m ×ˢ
      Metric.ball (0 : C(S, ℂ)) s ⊆ D := by
    intro q hq
    exact ⟨hsmallSub hq.1, hfieldSub hq.2⟩
  refine ⟨a, G, R, eta, m, s, B,
    heta, hm, hm43, hs, hB, ?_, haZero, ?_, ?_, ?_,
    hglobalBound, ?_⟩
  · intro j hj g hg
    exact haBall (Metric.ball_subset_ball
      (hsBase'.trans hsBaseCoeff) hg) ⟨j, hj⟩
  · exact hG.mono (fun q hq ↦ ⟨hsmallSub hq.1,
      Metric.ball_subset_ball (hsBase'.trans hsBaseS₀) hq.2⟩)
  · exact hR.mono hdomain
  · intro q
    dsimp only [R, P, p]
    ring
  · intro g hg
    exact hTaylor g
      (Metric.ball_subset_ball (hsBase'.trans hsBaseS₀) hg)

end PerronWright.FiniteIrreducibleCubicTransferData
