import PerronWright.Enumeration.ZeroFieldTreeGlobalContinuation
import PerronWright.Transfer.CartesianTransfer
import PerronWright.Transfer.NegativeHalf

/-!
# Zero-field tree coefficient asymptotics

The global continuation constructed in
`ZeroFieldTreeGlobalContinuation` has the local fold expansion

`C - (1-w) + (2 gamma / 3) X(w)^3 + (1-w)^2 R(X(w))`,

where `R` is analytic at the origin in the genuine fold coordinate and
`X(w) = sqrt (1-w)`.  This file turns that local analytic remainder into a
uniform bound on a smaller positive-opening Cartesian Delta-domain.  The
near part follows from local boundedness of `R`; the away part follows from
compactness.  Thus no global remainder estimate is assumed as an interface.

Cartesian transfer gives an `O(n⁻³)` coefficient remainder.  Since
`X(w)^3 = (1-w)^(3/2)`, the exact leading coefficient is
`(2 gamma / 3) * coefficient (-3/2) n`, whose equivalent is
`gamma / (2 sqrt pi) * n^(-5/2)`.
-/

open Filter Topology PerronWright Set Asymptotics
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.ZeroFieldTreeCoefficientAsymptotic

namespace GC

export PerronWright.ZeroFieldTreeGlobalContinuation
  (exists_zeroFieldTree_cartesianDelta_continuation)

end GC

namespace ZF

export PerronWright.ZeroFieldTreeEGFMatching
  (zeroFieldTreeSeries)

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

/-- The canonical fold cube is the principal `(1-w)^(3/2)` singularity. -/
theorem cartesianDeltaSqrt_cube_eq_cpow (w : ℂ) :
    Transfer.cartesianDeltaSqrt w ^ 3 =
      (1 - w) ^ ((3 / 2 : ℝ) : ℂ) := by
  unfold Transfer.cartesianDeltaSqrt Complex.sqrt
  rw [← Complex.cpow_mul_nat]
  congr 1
  norm_num

/-- Exact Taylor coefficient of the canonical fold cube. -/
theorem taylorCoefficient_cartesianDeltaSqrt_cube (n : ℕ) :
    Transfer.taylorCoefficient
        (fun w : ℂ ↦ Transfer.cartesianDeltaSqrt w ^ 3) n =
      (Transfer.coefficient (-(3 / 2)) n : ℂ) := by
  have hfun :
      (fun w : ℂ ↦ Transfer.cartesianDeltaSqrt w ^ 3) =
        (fun w : ℂ ↦ (1 - w) ^ (-((-(3 / 2 : ℝ)) : ℂ))) := by
    funext w
    rw [cartesianDeltaSqrt_cube_eq_cpow]
    congr 1
    norm_num
  rw [hfun]
  convert Transfer.taylorCoefficient_pure (-(3 / 2)) n using 1
  norm_num

private theorem taylorCoefficient_affine_eq_zero
    (C : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    Transfer.taylorCoefficient (fun w : ℂ ↦ C - (1 - w)) n = 0 := by
  have hfun : (fun w : ℂ ↦ C - (1 - w)) =
      (fun w : ℂ ↦ (C - 1) + w) := by
    funext w
    ring
  rw [hfun]
  rw [Transfer.taylorCoefficient,
    iteratedDeriv_const_add (by omega : 0 < n) (C - 1)]
  simp only [iteratedDeriv_fun_id_zero,
    if_neg (by omega : n ≠ 1), zero_div]

/-- The global continuation can be restricted to a positive-opening
Cartesian Delta-domain on which its remainder after the affine and cubic
terms is uniformly `O(|1-w|²)`.  The estimate is proved here from the local
analytic fold remainder and compactness away from `1`. -/
theorem exists_zeroFieldTree_cartesianDelta_transfer_data
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (C₀ : ℂ) (G H : ℂ → ℂ) (eta m B : ℝ),
      0 < eta ∧ 0 < m ∧ m < 4 / 3 ∧ 0 < B ∧
      AnalyticOnNhd ℂ G (Transfer.cartesianDelta eta m) ∧
      AnalyticOnNhd ℂ H (Transfer.cartesianDelta eta m) ∧
      Set.EqOn G (ZF.zeroFieldTreeSeries M)
        (Metric.ball (0 : ℂ) 1) ∧
      (∀ w : ℂ,
        G w = C₀ - (1 - w) +
          (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
            Transfer.cartesianDeltaSqrt w ^ 3 + H w) ∧
      ∀ w ∈ Transfer.cartesianDelta eta m,
        ‖H w‖ ≤ B * ‖w - 1‖ ^ (2 : ℝ) := by
  obtain ⟨C₀, R, G, eta₀, r, heta₀, hr, hRa, hG, hGinside,
      hGlocal⟩ :=
    GC.exists_zeroFieldTree_cartesianDelta_continuation M hM
  let A : ℂ := 2 * (FoldCoefficients.gamma M hM : ℂ) / 3
  let P : ℂ → ℂ := fun w ↦ C₀ - (1 - w)
  let L : ℂ → ℂ := fun w ↦
    A * Transfer.cartesianDeltaSqrt w ^ 3
  let H : ℂ → ℂ := fun w ↦ G w - (P w + L w)

  have hP : AnalyticOnNhd ℂ P
      (Transfer.cartesianDelta eta₀ 0) := by
    intro w _hw
    dsimp only [P]
    fun_prop
  have hL : AnalyticOnNhd ℂ L
      (Transfer.cartesianDelta eta₀ 0) := by
    intro w hw
    dsimp only [L]
    exact analyticAt_const.mul
      ((Transfer.analyticOnNhd_cartesianDeltaSqrt
        (m := (0 : ℝ)) (by norm_num) w hw).pow 3)
  have hH : AnalyticOnNhd ℂ H
      (Transfer.cartesianDelta eta₀ 0) := by
    intro w hw
    exact (hG w hw).sub ((hP w hw).add (hL w hw))

  let Bnear : ℝ := ‖R 0‖ + 1
  have hBnear : 0 < Bnear := by
    dsimp only [Bnear]
    positivity
  have hRboundedNhd : ∀ᶠ X : ℂ in 𝓝 0, ‖R X‖ ≤ Bnear := by
    have hclose : ∀ᶠ X : ℂ in 𝓝 0, R X ∈ Metric.ball (R 0) 1 :=
      hRa.continuousAt (Metric.ball_mem_nhds (R 0) zero_lt_one)
    filter_upwards [hclose] with X hX
    have htri : ‖R X‖ ≤ ‖R X - R 0‖ + ‖R 0‖ := by
      have := norm_add_le (R X - R 0) (R 0)
      simpa only [sub_add_cancel] using this
    have hdist : ‖R X - R 0‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hX
    exact htri.trans (by dsimp only [Bnear]; linarith)
  obtain ⟨rB, hrB, hRboundBall⟩ :=
    Metric.eventually_nhds_iff.mp hRboundedNhd

  let delta : ℝ := min (r ^ 2) (rB ^ 2) / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hdeltar : delta < r ^ 2 := by
    dsimp only [delta]
    have := min_le_left (r ^ 2) (rB ^ 2)
    nlinarith [sq_pos_of_pos hr]
  have hdeltarB : delta < rB ^ 2 := by
    dsimp only [delta]
    have := min_le_right (r ^ 2) (rB ^ 2)
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
  have hsmallSubLocalOuter : Transfer.cartesianDelta eta m ⊆
      Transfer.cartesianDelta 1 0 :=
    cartesianDelta_subset_slit heta_one hm.le
  have hGsmall : AnalyticOnNhd ℂ G
      (Transfer.cartesianDelta eta m) := hG.mono hsmallSub
  have hHsmall : AnalyticOnNhd ℂ H
      (Transfer.cartesianDelta eta m) := hH.mono hsmallSub

  let K : Set ℂ := cartesianDeltaAwayCompact eta m delta
  have hKcompact : IsCompact K := by
    simpa only [K] using
      isCompact_cartesianDeltaAwayCompact eta m delta
  have hKsub : K ⊆ Transfer.cartesianDelta eta₀ 0 := by
    simpa only [K] using
      (cartesianDeltaAwayCompact_subset_slit heta_eta₀ hm hdelta)
  have hHcontinuous : ContinuousOn H K :=
    hH.continuousOn.mono hKsub
  obtain ⟨D, hD⟩ := bddAbove_def.mp
    (hKcompact.bddAbove_image hHcontinuous.norm)
  have hHcompactBound : ∀ w ∈ K, ‖H w‖ ≤ max D 0 := by
    intro w hw
    exact (hD ‖H w‖ (mem_image_of_mem (fun z : ℂ ↦ ‖H z‖) hw)).trans
      (le_max_left D 0)

  let deltaSq : ℝ := delta ^ 2
  have hdeltaSq : 0 < deltaSq := sq_pos_of_pos hdelta
  let Baway : ℝ := max D 0 / deltaSq
  have hBaway : 0 ≤ Baway :=
    div_nonneg (le_max_right D 0) hdeltaSq.le
  have hawayBound : ∀ w ∈ Transfer.cartesianDelta eta m,
      delta ≤ dist w 1 →
      ‖H w‖ ≤ Baway * ‖w - 1‖ ^ (2 : ℝ) := by
    intro w hw haway
    have hwK : w ∈ K := by
      apply cartesianDelta_away_subset_compact
      exact ⟨hw, haway⟩
    have hnorm : delta ≤ ‖w - 1‖ := by
      simpa only [Complex.dist_eq] using haway
    have hpow : deltaSq ≤ ‖w - 1‖ ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      dsimp only [deltaSq]
      nlinarith [norm_nonneg (w - 1)]
    calc
      ‖H w‖ ≤ max D 0 := hHcompactBound w hwK
      _ = Baway * deltaSq := by
        dsimp only [Baway]
        field_simp [hdeltaSq.ne']
      _ ≤ Baway * ‖w - 1‖ ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow hBaway

  have hnearBound : ∀ w ∈ Transfer.cartesianDelta eta m,
      dist w 1 < delta →
      ‖H w‖ ≤ Bnear * ‖w - 1‖ ^ (2 : ℝ) := by
    intro w hw hnear
    let X : ℂ := Transfer.cartesianDeltaSqrt w
    have hXsq : ‖X‖ ^ 2 = ‖1 - w‖ := by
      rw [← norm_pow, Transfer.cartesianDeltaSqrt_sq]
    have hdist : ‖1 - w‖ < delta := by
      simpa only [Complex.dist_eq, norm_sub_rev] using hnear
    have hXr : ‖X‖ < r := by
      nlinarith [norm_nonneg X, sq_pos_of_pos hr, hdeltar]
    have hXrB : ‖X‖ < rB := by
      nlinarith [norm_nonneg X, sq_pos_of_pos hrB, hdeltarB]
    have hwLocal : w ∈
        TreeNormalizedFoldActivity.localCartesianDelta 1 0 r := by
      refine ⟨hsmallSubLocalOuter hw, ?_⟩
      change Transfer.cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) r
      simpa only [Metric.mem_ball, dist_zero_right] using hXr
    have hRX : ‖R X‖ ≤ Bnear := by
      apply hRboundBall
      simpa only [Metric.mem_ball, dist_zero_right] using hXrB
    have hHEq : H w = (1 - w) ^ 2 * R X := by
      dsimp only [H, P, L, A]
      rw [hGlocal w hwLocal]
      ring
    calc
      ‖H w‖ = ‖1 - w‖ ^ 2 * ‖R X‖ := by
        rw [hHEq, norm_mul, norm_pow]
      _ ≤ ‖1 - w‖ ^ 2 * Bnear :=
        mul_le_mul_of_nonneg_left hRX (sq_nonneg ‖1 - w‖)
      _ = Bnear * ‖w - 1‖ ^ (2 : ℝ) := by
        rw [Real.rpow_two, norm_sub_rev]
        ring

  let B : ℝ := max 1 (max Bnear Baway)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  have hBnearB : Bnear ≤ B :=
    (le_max_left Bnear Baway).trans (le_max_right 1 (max Bnear Baway))
  have hBawayB : Baway ≤ B :=
    (le_max_right Bnear Baway).trans (le_max_right 1 (max Bnear Baway))
  have hglobalBound : ∀ w ∈ Transfer.cartesianDelta eta m,
      ‖H w‖ ≤ B * ‖w - 1‖ ^ (2 : ℝ) := by
    intro w hw
    by_cases hnear : dist w 1 < delta
    · exact (hnearBound w hw hnear).trans
        (mul_le_mul_of_nonneg_right hBnearB
          (Real.rpow_nonneg (norm_nonneg _) _))
    · exact (hawayBound w hw (le_of_not_gt hnear)).trans
        (mul_le_mul_of_nonneg_right hBawayB
          (Real.rpow_nonneg (norm_nonneg _) _))

  refine ⟨C₀, G, H, eta, m, B, heta, hm, hm43, hB,
    hGsmall, hHsmall, hGinside, ?_, hglobalBound⟩
  intro w
  dsimp only [H, P, L, A]
  ring

/-- The genuine zero-field tree EGF has the exact cubic fold coefficient,
with an `O(n⁻³)` Taylor-coefficient remainder. -/
theorem zeroFieldTree_taylorCoefficient_error_isBigO
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fun n : ℕ ↦
      Transfer.taylorCoefficient (ZF.zeroFieldTreeSeries M) n -
        (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
          (Transfer.coefficient (-(3 / 2)) n : ℂ)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 : ℝ))) := by
  obtain ⟨C₀, G, H, eta, m, B, heta, hm, hm43, hB,
      hG, hH, hGinside, hFormula, hHbound⟩ :=
    exists_zeroFieldTree_cartesianDelta_transfer_data M hM

  let Q : ℂ → ℂ := fun w ↦ ((B : ℂ)⁻¹) * H w
  have hQ : AnalyticOnNhd ℂ Q
      (Transfer.cartesianDelta eta m) := by
    intro w hw
    exact analyticAt_const.mul (hH w hw)
  have hQpower : ∀ w ∈ Transfer.cartesianDelta eta m,
      ‖Q w‖ ≤ ‖w - 1‖ ^ (2 : ℝ) := by
    intro w hw
    have hBnorm : ‖((B : ℂ)⁻¹)‖ = B⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    calc
      ‖Q w‖ = B⁻¹ * ‖H w‖ := by
        dsimp only [Q]
        rw [norm_mul, hBnorm]
      _ ≤ B⁻¹ * (B * ‖w - 1‖ ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hHbound w hw) (inv_nonneg.mpr hB.le)
      _ = ‖w - 1‖ ^ (2 : ℝ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul]

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
      (a := (2 : ℝ)) hMcontour hMcontourOne hMcontourEta
      hm.le hm43 (by norm_num) hQ.differentiableOn hQpower).2
  have hQcoeffRate :
      (fun n : ℕ ↦ Transfer.banachTaylorCoefficient Q n) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-(3 : ℝ))) := by
    simpa only [show -((2 : ℝ) + 1) = -(3 : ℝ) by norm_num] using hQcoeff
  have hCoeffScale : ∀ n : ℕ,
      Transfer.banachTaylorCoefficient H n =
        (B : ℂ) * Transfer.banachTaylorCoefficient Q n := by
    intro n
    simp only [Transfer.banachTaylorCoefficient, Q,
      iteratedDeriv_const_mul_field, smul_eq_mul]
    field_simp [hB.ne']
  have hHcoeffBanach :
      (fun n : ℕ ↦ Transfer.banachTaylorCoefficient H n) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-(3 : ℝ))) := by
    have hscaled := hQcoeffRate.const_mul_left (B : ℂ)
    apply hscaled.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards with n
    exact (hCoeffScale n).symm
  have hHcoeff :
      (fun n : ℕ ↦ Transfer.taylorCoefficient H n) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-(3 : ℝ))) := by
    simpa only [taylorCoefficient_eq_banachTaylorCoefficient] using
      hHcoeffBanach

  have hzeroDelta : (0 : ℂ) ∈ Transfer.cartesianDelta eta m :=
    Transfer.unit_ball_subset_cartesianDelta heta
      (by simpa only [Metric.mem_ball, dist_zero_right, norm_zero] using
        (zero_lt_one : (0 : ℝ) < 1))
  have hG0 : AnalyticAt ℂ G 0 := hG 0 hzeroDelta
  have hP0 : AnalyticAt ℂ (fun w : ℂ ↦ C₀ - (1 - w)) 0 := by
    fun_prop
  have hX0 : AnalyticAt ℂ Transfer.cartesianDeltaSqrt 0 :=
    Transfer.analyticOnNhd_cartesianDeltaSqrt
      (m := m) hm.le 0 hzeroDelta
  have hL0 : AnalyticAt ℂ
      (fun w : ℂ ↦
        (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
          Transfer.cartesianDeltaSqrt w ^ 3) 0 :=
    analyticAt_const.mul (hX0.pow 3)
  have hEqNhd : G =ᶠ[𝓝 (0 : ℂ)] ZF.zeroFieldTreeSeries M :=
    hGinside.eventuallyEq_of_mem
      (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  have hCoeffGenuine : ∀ n : ℕ,
      Transfer.taylorCoefficient G n =
        Transfer.taylorCoefficient (ZF.zeroFieldTreeSeries M) n := by
    intro n
    unfold Transfer.taylorCoefficient
    rw [hEqNhd.iteratedDeriv_eq n]
  have hLcoeff : ∀ n : ℕ,
      Transfer.taylorCoefficient
          (fun w : ℂ ↦
            (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
              Transfer.cartesianDeltaSqrt w ^ 3) n =
        (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
          (Transfer.coefficient (-(3 / 2)) n : ℂ) := by
    intro n
    rw [taylorCoefficient_const_mul,
      taylorCoefficient_cartesianDeltaSqrt_cube]

  apply hHcoeff.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
  have hsumCoeff :
      Transfer.taylorCoefficient
          (fun w : ℂ ↦ C₀ - (1 - w) +
            (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
              Transfer.cartesianDeltaSqrt w ^ 3) n =
        (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
          (Transfer.coefficient (-(3 / 2)) n : ℂ) := by
    rw [taylorCoefficient_add hP0 hL0 n,
      taylorCoefficient_affine_eq_zero C₀ hn, hLcoeff n, zero_add]
  have hHcoeffFormula :
      Transfer.taylorCoefficient H n =
        Transfer.taylorCoefficient G n -
          (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
            (Transfer.coefficient (-(3 / 2)) n : ℂ) := by
    have hsub := Transfer.taylorCoefficient_sub
      (F := G)
      (G := fun w : ℂ ↦ C₀ - (1 - w) +
        (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
          Transfer.cartesianDeltaSqrt w ^ 3)
      hG0 (hP0.add hL0) n
    have hfun : (fun w : ℂ ↦
        G w - (C₀ - (1 - w) +
          (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
            Transfer.cartesianDeltaSqrt w ^ 3)) = H := by
      funext w
      rw [hFormula w]
      ring
    rw [hfun, hsumCoeff] at hsub
    exact hsub
  rw [← hCoeffGenuine n, ← hHcoeffFormula]

/-- The `O(n⁻³)` remainder is little-oh of the natural tree scale
`n^(-5/2)`.  This is the form needed to read off the Wright constant from
the exact singular coefficient. -/
theorem zeroFieldTree_taylorCoefficient_error_isLittleO
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fun n : ℕ ↦
      Transfer.taylorCoefficient (ZF.zeroFieldTreeSeries M) n -
        (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
          (Transfer.coefficient (-(3 / 2)) n : ℂ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hpower :
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 : ℝ))) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
    apply isLittleO_of_tendsto
    · intro n hzero
      by_cases hn : n = 0
      · subst n
        norm_num
      · have hnpos : (0 : ℝ) < n := by
          exact_mod_cast Nat.pos_of_ne_zero hn
        exfalso
        exact (Real.rpow_pos_of_pos hnpos (-(5 / 2 : ℝ))).ne' hzero
    · have hlim : Tendsto
          (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ)))
          atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
          tendsto_natCast_atTop_atTop
      apply hlim.congr'
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [← Real.rpow_sub hnpos]
      congr 1
      norm_num
  exact (zeroFieldTree_taylorCoefficient_error_isBigO M hM).trans_isLittleO
    hpower

/-- The exact singular coefficient in the preceding theorem has Wright's
tree constant `gamma / (2 sqrt pi)` at scale `n^(-5/2)`. -/
theorem zeroFieldTree_leadingCoefficient_isEquivalent
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fun n : ℕ ↦
      (2 * (FoldCoefficients.gamma M hM : ℝ) / 3) *
        Transfer.coefficient (-(3 / 2)) n) ~[atTop]
      (fun n : ℕ ↦
        FoldCoefficients.gamma M hM /
          (2 * Real.sqrt Real.pi) *
            (n : ℝ) ^ (-(5 / 2 : ℝ))) := by
  have hconst :
      (fun _ : ℕ ↦ 2 * FoldCoefficients.gamma M hM / 3) ~[atTop]
        (fun _ : ℕ ↦ 2 * FoldCoefficients.gamma M hM / 3) :=
    IsEquivalent.refl
  have h := hconst.mul
    Transfer.coefficient_neg_three_halves_isEquivalent
  convert h using 1
  · ext n
    simp only [Pi.mul_apply]
  · ext n
    simp only [Pi.mul_apply]
    ring_nf

end PerronWright.ZeroFieldTreeCoefficientAsymptotic
