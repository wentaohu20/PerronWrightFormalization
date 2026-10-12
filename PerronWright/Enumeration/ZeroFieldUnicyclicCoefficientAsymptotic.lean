import PerronWright.Enumeration.ZeroFieldUnicyclicDeltaContinuation
import PerronWright.Transfer.CartesianTransfer
import PerronWright.Transfer.LogarithmicCoefficient

/-!
# Zero-field unicyclic coefficient asymptotics

This file globalizes the square-root remainder obtained from the local
fold chart.  The only shrinking is geometric: a Cartesian Delta-domain
with positive cone opening has compact closure away from the critical
activity inside the previously constructed slit Delta-domain.  Compactness
therefore upgrades the local `O(sqrt (1-w))` estimate to a uniform bound on
the smaller full Delta-domain.  The existing Cartesian transfer theorem
then gives the `O(n^(-3/2))` coefficient remainder.
-/

open Filter Topology PerronWright Set Asymptotics
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.ZeroFieldUnicyclicCoefficientAsymptotic

namespace DC

export PerronWright.ZeroFieldUnicyclicDeltaContinuation
  (exists_zeroFieldUnicyclic_cartesianDelta_continuation)

end DC

namespace ZF

export PerronWright.ZeroFieldUnicyclicSingularity
  (zeroFieldUnicyclicEGF)

end ZF

variable {S : Type*} [MetricSpace S] [CompactSpace S]
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

/-- Shrinking the radial margin and increasing the cone opening embeds a
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

/-- The compact collar of a strictly smaller positive-opening domain is
contained in the original slit Delta-domain. -/
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

private theorem taylorCoefficient_eq_banachTaylorCoefficient
    (F : ℂ → ℂ) (n : ℕ) :
    Transfer.taylorCoefficient F n =
      Transfer.banachTaylorCoefficient F n := by
  simp only [Transfer.taylorCoefficient,
    Transfer.banachTaylorCoefficient, smul_eq_mul, div_eq_mul_inv]
  ring

private theorem taylorCoefficient_const_mul
    (c : ℂ) (F : ℂ → ℂ) (n : ℕ) :
    Transfer.taylorCoefficient (fun w ↦ c * F w) n =
      c * Transfer.taylorCoefficient F n := by
  simp only [Transfer.taylorCoefficient,
    iteratedDeriv_const_mul_field, mul_div_assoc]

private theorem taylorCoefficient_add
    {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hG : AnalyticAt ℂ G 0) (n : ℕ) :
    Transfer.taylorCoefficient (fun w ↦ F w + G w) n =
      Transfer.taylorCoefficient F n +
        Transfer.taylorCoefficient G n := by
  simp only [Transfer.taylorCoefficient,
    iteratedDeriv_fun_add hF.contDiffAt hG.contDiffAt, add_div]

private theorem taylorCoefficient_const_of_pos
    (c : ℂ) {n : ℕ} (hn : 0 < n) :
    Transfer.taylorCoefficient (fun _ : ℂ ↦ c) n = 0 := by
  simp only [Transfer.taylorCoefficient, iteratedDeriv_const,
    if_neg hn.ne', zero_div]

/-- The global zero-field continuation can be chosen on a positive-opening
Cartesian Delta-domain with a uniform square-root remainder bound. -/
theorem exists_zeroFieldUnicyclic_cartesianDelta_transfer_data
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (H₁ : ℂ) (G R : ℂ → ℂ) (eta m C : ℝ),
      0 < eta ∧ 0 < m ∧ m < 4 / 3 ∧ 0 < C ∧
      AnalyticOnNhd ℂ G (Transfer.cartesianDelta eta m) ∧
      AnalyticOnNhd ℂ R (Transfer.cartesianDelta eta m) ∧
      Set.EqOn G (ZF.zeroFieldUnicyclicEGF M)
        (Metric.ball (0 : ℂ) 1) ∧
      (∀ w : ℂ,
        G w = (1 / 4 : ℂ) * (-Complex.log (1 - w)) + R w + H₁) ∧
      ∀ w ∈ Transfer.cartesianDelta eta m,
        ‖R w‖ ≤ C * ‖w - 1‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨H₁, E, G, eta₀, r, heta₀, hr, hE, hG, hGinside,
      hGformula, hEO⟩ :=
    DC.exists_zeroFieldUnicyclic_cartesianDelta_continuation M hM
  let L : ℂ → ℂ := fun w ↦
    (1 / 4 : ℂ) * (-Complex.log (1 - w))
  let R : ℂ → ℂ := fun w ↦ G w - (L w + H₁)

  have hL : AnalyticOnNhd ℂ L
      (Transfer.cartesianDelta eta₀ 0) := by
    intro w hw
    have hslit : 1 - w ∈ Complex.slitPlane :=
      Transfer.one_sub_mem_slitPlane_of_mem_cartesianDelta
        (m := (0 : ℝ)) (by norm_num) hw
    have hlog : AnalyticAt ℂ (fun z : ℂ ↦ Complex.log (1 - z)) w :=
      (analyticAt_const.sub analyticAt_id).clog hslit
    exact analyticAt_const.mul hlog.neg
  have hR : AnalyticOnNhd ℂ R
      (Transfer.cartesianDelta eta₀ 0) := by
    intro w hw
    exact (hG w hw).sub ((hL w hw).add analyticAt_const)

  obtain ⟨c, hc⟩ := hEO.bound
  obtain ⟨delta₀, hdelta₀, hlocalBound⟩ :=
    Metric.eventually_nhds_iff.mp hc
  let delta : ℝ := min delta₀ (r ^ 2) / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact half_pos (lt_min hdelta₀ (pow_pos hr 2))
  have hdelta_le : delta ≤ delta₀ := by
    dsimp only [delta]
    have := min_le_left delta₀ (r ^ 2)
    nlinarith [hdelta₀]
  have hdelta_r : delta < r ^ 2 := by
    dsimp only [delta]
    have := min_le_right delta₀ (r ^ 2)
    nlinarith [pow_pos hr 2]

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
  have hsmallSubLocalOuter : Transfer.cartesianDelta eta m ⊆
      Transfer.cartesianDelta 1 0 :=
    cartesianDelta_subset_slit heta_one hm.le
  have hGsmall : AnalyticOnNhd ℂ G
      (Transfer.cartesianDelta eta m) := hG.mono hsmallSub
  have hRsmall : AnalyticOnNhd ℂ R
      (Transfer.cartesianDelta eta m) := hR.mono hsmallSub

  let K : Set ℂ := cartesianDeltaAwayCompact eta m delta
  have hKcompact : IsCompact K := by
    simpa only [K] using
      isCompact_cartesianDeltaAwayCompact eta m delta
  have hKsub : K ⊆ Transfer.cartesianDelta eta₀ 0 := by
    simpa only [K] using
      (cartesianDeltaAwayCompact_subset_slit heta_eta₀ hm hdelta)
  have hRcontinuous : ContinuousOn R K :=
    hR.continuousOn.mono hKsub
  obtain ⟨B, hB⟩ := bddAbove_def.mp
    (hKcompact.bddAbove_image hRcontinuous.norm)
  have hRcompactBound : ∀ w ∈ K, ‖R w‖ ≤ max B 0 := by
    intro w hw
    exact (hB ‖R w‖ (mem_image_of_mem (fun z : ℂ ↦ ‖R z‖) hw)).trans
      (le_max_left B 0)

  let droot : ℝ := delta ^ (1 / 2 : ℝ)
  have hdroot : 0 < droot := by
    dsimp only [droot]
    exact Real.rpow_pos_of_pos hdelta _
  let Caway : ℝ := max B 0 / droot
  have hCaway : 0 ≤ Caway := by
    exact div_nonneg (le_max_right B 0) hdroot.le
  have hawayBound : ∀ w ∈ Transfer.cartesianDelta eta m,
      delta ≤ dist w 1 →
      ‖R w‖ ≤ Caway * ‖w - 1‖ ^ (1 / 2 : ℝ) := by
    intro w hw haway
    have hwK : w ∈ K := by
      apply cartesianDelta_away_subset_compact
      exact ⟨hw, haway⟩
    have hrootle : droot ≤ ‖w - 1‖ ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow hdelta.le
      · simpa only [Complex.dist_eq] using haway
      · norm_num
    calc
      ‖R w‖ ≤ max B 0 := hRcompactBound w hwK
      _ = Caway * droot := by
        dsimp only [Caway]
        field_simp [hdroot.ne']
      _ ≤ Caway * ‖w - 1‖ ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hrootle hCaway

  let C : ℝ := max 1 (max c Caway)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  have hcC : c ≤ C :=
    (le_max_left c Caway).trans (le_max_right 1 (max c Caway))
  have hCawayC : Caway ≤ C :=
    (le_max_right c Caway).trans (le_max_right 1 (max c Caway))
  have hglobalBound : ∀ w ∈ Transfer.cartesianDelta eta m,
      ‖R w‖ ≤ C * ‖w - 1‖ ^ (1 / 2 : ℝ) := by
    intro w hw
    by_cases hnear : dist w 1 < delta
    · have hwLocal : w ∈
          TreeNormalizedFoldActivity.localCartesianDelta 1 0 r := by
        refine ⟨hsmallSubLocalOuter hw, ?_⟩
        change Transfer.cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) r
        rw [Metric.mem_ball, dist_zero_right]
        have hsquare : ‖Transfer.cartesianDeltaSqrt w‖ ^ 2 =
            ‖1 - w‖ := by
          rw [← norm_pow, Transfer.cartesianDeltaSqrt_sq]
        have hdist : ‖1 - w‖ < delta := by
          simpa only [Complex.dist_eq, norm_sub_rev] using hnear
        nlinarith [norm_nonneg (Transfer.cartesianDeltaSqrt w)]
      have hwBall : w ∈ Metric.ball (1 : ℂ) delta₀ := by
        rw [Metric.mem_ball]
        exact hnear.trans_le hdelta_le
      have hRE : R w = E w := by
        dsimp only [R, L]
        rw [hGformula w hwLocal]
        ring
      have hlocal : ‖R w‖ ≤ c * ‖Transfer.cartesianDeltaSqrt w‖ := by
        rw [hRE]
        exact hlocalBound (by
          simpa only [Metric.mem_ball] using hwBall)
      calc
        ‖R w‖ ≤ c * ‖Transfer.cartesianDeltaSqrt w‖ := hlocal
        _ ≤ C * ‖Transfer.cartesianDeltaSqrt w‖ :=
          mul_le_mul_of_nonneg_right hcC (norm_nonneg _)
        _ = C * ‖w - 1‖ ^ (1 / 2 : ℝ) := by
          rw [ZeroFieldUnicyclicActivitySingularity.norm_cartesianDeltaSqrt_eq_rpow,
            norm_sub_rev]
    · exact (hawayBound w hw (le_of_not_gt hnear)).trans
        (mul_le_mul_of_nonneg_right hCawayC
          (Real.rpow_nonneg (norm_nonneg _) _))

  refine ⟨H₁, G, R, eta, m, C, heta, hm, hm43, hC,
    hGsmall, hRsmall, hGinside, ?_, hglobalBound⟩
  intro w
  dsimp only [R, L]
  ring

/-- The Taylor coefficients of the genuine zero-field unicyclic EGF have
the Wright logarithmic leading term and a square-root transfer error. -/
theorem zeroFieldUnicyclic_taylorCoefficient_error_isBigO
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fun n : ℕ ↦
      Transfer.taylorCoefficient (ZF.zeroFieldUnicyclicEGF M) n -
        (1 / 4 : ℂ) * Transfer.logarithmicCoefficient n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨H₁, G, R, eta, m, C, heta, hm, hm43, hC,
      hG, hR, hGinside, hFormula, hRbound⟩ :=
    exists_zeroFieldUnicyclic_cartesianDelta_transfer_data M hM

  let Q : ℂ → ℂ := fun w ↦ ((C : ℂ)⁻¹) * R w
  have hQ : AnalyticOnNhd ℂ Q
      (Transfer.cartesianDelta eta m) := by
    intro w hw
    exact analyticAt_const.mul (hR w hw)
  have hQpower : ∀ w ∈ Transfer.cartesianDelta eta m,
      ‖Q w‖ ≤ ‖w - 1‖ ^ (1 / 2 : ℝ) := by
    intro w hw
    have hCnorm : ‖((C : ℂ)⁻¹)‖ = C⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    calc
      ‖Q w‖ = C⁻¹ * ‖R w‖ := by
        dsimp only [Q]
        rw [norm_mul, hCnorm]
      _ ≤ C⁻¹ * (C * ‖w - 1‖ ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hRbound w hw) (inv_nonneg.mpr hC.le)
      _ = ‖w - 1‖ ^ (1 / 2 : ℝ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]

  let Mcontour : ℝ := min (eta / 2) 1
  have hMcontour : 0 < Mcontour := by
    dsimp only [Mcontour]
    exact lt_min (half_pos heta) zero_lt_one
  have hMcontourOne : Mcontour ≤ 1 := min_le_right _ _
  have hMcontourEta : Mcontour < eta :=
    (min_le_left (eta / 2) 1).trans_lt (half_lt_self heta)
  have hQcoeff :=
    (Transfer.banachCartesianTaylorCoefficient_transfer
      (F := Q) (M := Mcontour) (eta := eta) (m := m)
      (a := (1 / 2 : ℝ)) hMcontour hMcontourOne hMcontourEta
      hm.le hm43 (by norm_num) hQ.differentiableOn hQpower).2
  have hQcoeffRate :
      (fun n : ℕ ↦ Transfer.banachTaylorCoefficient Q n) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    simpa only [show -((1 / 2 : ℝ) + 1) = -(3 / 2 : ℝ) by
      norm_num] using hQcoeff

  have hCoeffScale : ∀ n : ℕ,
      Transfer.banachTaylorCoefficient R n =
        (C : ℂ) * Transfer.banachTaylorCoefficient Q n := by
    intro n
    simp only [Transfer.banachTaylorCoefficient, Q,
      iteratedDeriv_const_mul_field, smul_eq_mul]
    field_simp [hC.ne']
  have hRcoeffBanach :
      (fun n : ℕ ↦ Transfer.banachTaylorCoefficient R n) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    have hscaled := hQcoeffRate.const_mul_left (C : ℂ)
    apply hscaled.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards with n
    exact (hCoeffScale n).symm
  have hRcoeff :
      (fun n : ℕ ↦ Transfer.taylorCoefficient R n) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    simpa only [taylorCoefficient_eq_banachTaylorCoefficient] using
      hRcoeffBanach

  have hzeroDelta : (0 : ℂ) ∈ Transfer.cartesianDelta eta m :=
    Transfer.unit_ball_subset_cartesianDelta heta
      (by simpa only [Metric.mem_ball, dist_zero_right, norm_zero] using
        (zero_lt_one : (0 : ℝ) < 1))
  have hG0 : AnalyticAt ℂ G 0 := hG 0 hzeroDelta
  have hL0 : AnalyticAt ℂ
      (fun w : ℂ ↦ (1 / 4 : ℂ) * (-Complex.log (1 - w))) 0 := by
    have hslit : (1 : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (by norm_num)
    have hlog : AnalyticAt ℂ (fun w : ℂ ↦ Complex.log (1 - w)) 0 :=
      (analyticAt_const.sub analyticAt_id).clog (by
        simpa only [Pi.sub_apply, id_eq, sub_zero] using hslit)
    exact analyticAt_const.mul hlog.neg
  have hLcoeff : ∀ n : ℕ,
      Transfer.taylorCoefficient
          (fun w : ℂ ↦ (1 / 4 : ℂ) * (-Complex.log (1 - w))) n =
        (1 / 4 : ℂ) * Transfer.logarithmicCoefficient n := by
    intro n
    rw [taylorCoefficient_const_mul,
      Transfer.taylorCoefficient_neg_log_one_sub]
  have hEqNhd : G =ᶠ[𝓝 (0 : ℂ)] ZF.zeroFieldUnicyclicEGF M :=
    hGinside.eventuallyEq_of_mem
      (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hCoeffGenuine : ∀ n : ℕ,
      Transfer.taylorCoefficient G n =
        Transfer.taylorCoefficient (ZF.zeroFieldUnicyclicEGF M) n := by
    intro n
    unfold Transfer.taylorCoefficient
    rw [hEqNhd.iteratedDeriv_eq n]

  apply hRcoeff.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : 0 < n := by omega
  have hconstCoeff :
      Transfer.taylorCoefficient (fun _ : ℂ ↦ H₁) n = 0 := by
    exact taylorCoefficient_const_of_pos H₁ hn0
  have hsumCoeff :
      Transfer.taylorCoefficient
          (fun w : ℂ ↦
            (1 / 4 : ℂ) * (-Complex.log (1 - w)) + H₁) n =
        (1 / 4 : ℂ) * Transfer.logarithmicCoefficient n := by
    rw [taylorCoefficient_add hL0 analyticAt_const n,
      hLcoeff n, hconstCoeff, add_zero]
  have hRcoeffFormula :
      Transfer.taylorCoefficient R n =
        Transfer.taylorCoefficient G n -
          (1 / 4 : ℂ) * Transfer.logarithmicCoefficient n := by
    have hConst : AnalyticAt ℂ (fun _ : ℂ ↦ H₁) 0 := analyticAt_const
    have hsub := Transfer.taylorCoefficient_sub
      (F := G)
      (G := fun w : ℂ ↦
        (1 / 4 : ℂ) * (-Complex.log (1 - w)) + H₁)
      hG0 (hL0.add hConst) n
    have hfun : (fun w : ℂ ↦
        G w - ((1 / 4 : ℂ) * (-Complex.log (1 - w)) + H₁)) = R := by
      funext w
      rw [hFormula w]
      ring
    rw [hfun, hsumCoeff] at hsub
    exact hsub
  rw [← hCoeffGenuine n, ← hRcoeffFormula]

/-- Explicit `1/(4n)` form of the zero-field unicyclic coefficient
asymptotic.  The convention `0⁻¹ = 0` makes the statement valid as a
sequence on all natural indices; the estimate is, of course, at infinity. -/
theorem zeroFieldUnicyclic_taylorCoefficient_explicit_error_isBigO
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fun n : ℕ ↦
      Transfer.taylorCoefficient (ZF.zeroFieldUnicyclicEGF M) n -
        (1 / 4 : ℂ) * (n : ℂ)⁻¹) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  simpa only [Transfer.logarithmicCoefficient] using
    zeroFieldUnicyclic_taylorCoefficient_error_isBigO M hM

end PerronWright.ZeroFieldUnicyclicCoefficientAsymptotic
