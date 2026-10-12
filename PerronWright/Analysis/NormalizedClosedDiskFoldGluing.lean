import PerronWright.Analysis.RootedTreeClosedDiskGlobal
import PerronWright.Analysis.NormalizedUnitAway
import PerronWright.Analysis.TreeJointOverlapUniqueness
import PerronWright.Analysis.AnalyticTwoChartGluing
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.Convex.PathConnected

/-!
# Closed-disk continuation and fold-chart gluing geometry

This module constructs the normalized closed-disk chart away from the
critical activity and proves the component geometry needed to compare it
with a smaller fold chart through a larger ambient overlap.  In particular,
it does not assert connectedness of the raw maximal overlap.
-/

open Filter Topology
open scoped Classical ComplexConjugate

noncomputable section

namespace PerronWright.TreeNormalizedClosedDiskGluing

open PerronWright
open PerronWright.TreeNormalizedFoldActivity
open PerronWright.TreeNormalizedUnitAway

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The compact part of the closed unit disk kept a positive distance from
the critical activity `1`. -/
def closedUnitDiskAway (δ : ℝ) : Set ℂ :=
  Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | δ ≤ dist w 1}

theorem isCompact_closedUnitDiskAway (δ : ℝ) :
    IsCompact (closedUnitDiskAway δ) := by
  have haway : IsClosed {w : ℂ | δ ≤ dist w 1} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  exact (isCompact_closedBall (0 : ℂ) 1).inter_right haway

/-- The production closed-disk chart, pulled back to normalized activity,
with exactly the interfaces used by the fold-overlap argument. -/
theorem exists_normalized_rootedTreeSeries_joint_analytic_continuation_closedDisk_away
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (U : Set ℂ) (ε : ℝ)
        (Ψ : ℂ × C(S, ℂ) → C(S, ℂ)),
      IsOpen U ∧
      closedUnitDiskAway δ ⊆ U ∧
      0 < ε ∧
      IsOpen (normalizedUnitAwayDomain M hM U ε) ∧
      AnalyticOnNhd ℂ (activityMap M hM)
        (Set.univ ×ˢ Metric.ball (0 : C(S, ℂ)) ε) ∧
      AnalyticOnNhd ℂ (normalizedUnitAwayProfile M hM Ψ)
        (normalizedUnitAwayDomain M hM U ε) ∧
      (∀ q ∈ normalizedUnitAwayDomain M hM U ε,
        RadiusResponse.radius M hM q.2 ≠ 0 ∧
        TreeCritical.residual M
          (activityMap M hM q, normalizedUnitAwayProfile M hM Ψ q) = 0) ∧
      (∀ w ∈ U, ‖w‖ < 1 →
        normalizedUnitAwayProfile M hM Ψ (w, 0) =
          M.rootedTreeSeries w) ∧
      ∀ w ∈ U,
        ∀ᶠ p in nhds
          (((w, (0 : C(S, ℂ))), normalizedUnitAwayProfile M hM Ψ (w, 0))),
          TreeCritical.residual M (activityMap M hM p.1, p.2) = 0 ↔
            normalizedUnitAwayProfile M hM Ψ p.1 = p.2 := by
  have hKdisk : closedUnitDiskAway δ ⊆ Metric.closedBall (0 : ℂ) 1 :=
    fun _ hw => hw.1
  have hnotone : (1 : ℂ) ∉ closedUnitDiskAway δ := by
    intro hOne
    have haway := hOne.2
    change δ ≤ dist (1 : ℂ) 1 at haway
    rw [dist_self] at haway
    exact (not_le_of_gt hδ) haway
  obtain ⟨U, εClosed, Ψ, hU, hKU, hεClosed, hΨ, hres,
      hinside, huniq⟩ :=
    M.exists_rootedTreeSeries_joint_analytic_continuation_near_compact_closedDisk
      hM (isCompact_closedUnitDiskAway δ) hKdisk hnotone
  obtain ⟨εActivity, hεActivity, hActivity, hRadiusNe⟩ :=
    exists_activityMap_analytic_field_ball M hM
  let ε : ℝ := min εClosed εActivity
  have hε : 0 < ε := lt_min hεClosed hεActivity
  have hActivity' : AnalyticOnNhd ℂ (activityMap M hM)
      (Set.univ ×ˢ Metric.ball (0 : C(S, ℂ)) ε) := by
    intro q hq
    exact hActivity q ⟨Set.mem_univ _,
      Metric.ball_subset_ball (min_le_right εClosed εActivity) hq.2⟩
  have hΨ' : AnalyticOnNhd ℂ Ψ
      (U ×ˢ Metric.ball (0 : C(S, ℂ)) ε) := by
    intro q hq
    exact hΨ q ⟨hq.1,
      Metric.ball_subset_ball (min_le_left εClosed εActivity) hq.2⟩
  have hDopen := isOpen_normalizedUnitAwayDomain M hM hU hActivity'
  have hProfile := normalizedUnitAwayProfile_analytic M hM hActivity' hΨ'
  refine ⟨U, ε, Ψ, hU, hKU, hε, hDopen, hActivity', hProfile,
    ?_, ?_, ?_⟩
  · intro q hq
    have htarget : activityMap M hM q ∈
        U ×ˢ Metric.ball (0 : C(S, ℂ)) ε := hq
    have hg : q.2 ∈ Metric.ball (0 : C(S, ℂ)) ε := by
      simpa only [activityMap] using htarget.2
    refine ⟨hRadiusNe q.2
      (Metric.ball_subset_ball (min_le_right εClosed εActivity) hg), ?_⟩
    exact hres (activityMap M hM q)
      ⟨htarget.1,
        Metric.ball_subset_ball (min_le_left εClosed εActivity) htarget.2⟩
  · intro w hwU hwNorm
    simpa only [normalizedUnitAwayProfile, activityMap_zeroField] using
      hinside w hwU hwNorm
  · intro w hwU
    have h0 : (0 : C(S, ℂ)) ∈ Metric.ball 0 ε :=
      Metric.mem_ball_self hε
    exact normalizedUnitAwayProfile_local_residual_uniqueness M hM Ψ w
      (hActivity' (w, 0) ⟨Set.mem_univ _, h0⟩).continuousAt
      (huniq w hwU)


/-!
## One-variable overlap geometry

The strict fold-radius margin is enough to prove the required component
statement by two straight segments.  No classification of plane domains or
of their connected components is used below.
-/

private theorem closedUnitDiskAway_conj {delta : ℝ} {z : ℂ}
    (hz : z ∈ closedUnitDiskAway delta) :
    conj z ∈ closedUnitDiskAway delta := by
  refine ⟨?_, ?_⟩
  · simpa only [Metric.mem_closedBall, Complex.dist_eq,
      sub_zero, Complex.norm_conj] using hz.1
  · calc
      delta ≤ dist z 1 := hz.2
      _ = dist (conj z) (conj 1) :=
        (Complex.dist_conj_conj z 1).symm
      _ = dist (conj z) 1 := by rw [map_one]

private theorem dist_conj_le_of_im_mul_nonpos {w z : ℂ}
    (him : w.im * z.im ≤ 0) :
    dist w (conj z) ≤ dist w z := by
  rw [Complex.dist_eq, Complex.dist_eq,
    ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  nlinarith

private theorem exists_same_halfPlane_witness
    {delta : ℝ} {w z : ℂ}
    (hz : z ∈ closedUnitDiskAway delta) :
    ∃ z' : ℂ,
      z' ∈ closedUnitDiskAway delta ∧
      dist w z' ≤ dist w z ∧
      ((0 ≤ w.im ∧ 0 ≤ z'.im) ∨ (w.im ≤ 0 ∧ z'.im ≤ 0)) := by
  by_cases hw : 0 ≤ w.im
  · by_cases hzIm : 0 ≤ z.im
    · exact ⟨z, hz, le_rfl, Or.inl ⟨hw, hzIm⟩⟩
    · refine ⟨conj z, closedUnitDiskAway_conj hz, ?_, Or.inl ⟨hw, ?_⟩⟩
      · apply dist_conj_le_of_im_mul_nonpos
        exact mul_nonpos_of_nonneg_of_nonpos hw (le_of_not_ge hzIm)
      · simpa only [Complex.conj_im] using neg_nonneg.mpr (le_of_not_ge hzIm)
  · have hw' : w.im ≤ 0 := le_of_not_ge hw
    by_cases hzIm : z.im ≤ 0
    · exact ⟨z, hz, le_rfl, Or.inr ⟨hw', hzIm⟩⟩
    · refine ⟨conj z, closedUnitDiskAway_conj hz, ?_, Or.inr ⟨hw', ?_⟩⟩
      · apply dist_conj_le_of_im_mul_nonpos
        exact mul_nonpos_of_nonpos_of_nonneg hw' (le_of_not_ge hzIm)
      · simpa only [Complex.conj_im] using neg_nonpos.mpr (le_of_not_ge hzIm)

private theorem closedUnitDiskAway_subset_cartesianDelta
    {delta : ℝ} (hdelta : 0 < delta) :
    closedUnitDiskAway delta ⊆ Transfer.cartesianDelta 1 0 := by
  intro z hz
  have hnorm : ‖z‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz.1
  refine ⟨by linarith, ?_⟩
  rintro ⟨hre, him⟩
  have him0 : z.im = 0 := by
    simp only [Complex.sub_im, Complex.one_im, sub_zero, zero_mul] at him
    exact abs_eq_zero.mp (le_antisymm him (abs_nonneg _))
  have hreLower : 1 ≤ z.re := by
    simpa only [Complex.sub_re, Complex.one_re, sub_nonneg] using hre
  have hreUpper : z.re ≤ 1 := (Complex.re_le_norm z).trans hnorm
  have hzOne : z = 1 := by
    apply Complex.ext
    · simpa only [Complex.one_re] using le_antisymm hreUpper hreLower
    · simpa only [Complex.one_im] using him0
  have haway : delta ≤ dist z 1 := hz.2
  rw [hzOne, dist_self] at haway
  exact (not_le_of_gt hdelta) haway

private theorem re_lt_one_of_mem_cartesianDelta_of_im_eq_zero
    {z : ℂ} (hz : z ∈ Transfer.cartesianDelta 1 0)
    (him : z.im = 0) : z.re < 1 := by
  by_contra hre
  apply hz.2
  refine ⟨?_, ?_⟩
  · simpa only [Complex.sub_re, Complex.one_re, sub_nonneg] using le_of_not_gt hre
  · simp only [Complex.sub_im, Complex.one_im, sub_zero, him, abs_zero,
      zero_mul, le_rfl]

private theorem segment_subset_cartesianDelta_of_same_halfPlane
    {w z : ℂ}
    (hw : w ∈ Transfer.cartesianDelta 1 0)
    (hz : z ∈ Transfer.cartesianDelta 1 0)
    (hside : (0 ≤ w.im ∧ 0 ≤ z.im) ∨
      (w.im ≤ 0 ∧ z.im ≤ 0)) :
    segment ℝ w z ⊆ Transfer.cartesianDelta 1 0 := by
  intro q hq
  rcases hq with ⟨a, b, ha, hb, hab, rfl⟩
  have hwBall : w ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right]
    have hwNorm := hw.1
    norm_num at hwNorm
    exact hwNorm
  have hzBall : z ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right]
    have hzNorm := hz.1
    norm_num at hzNorm
    exact hzNorm
  have houter := (convex_ball (0 : ℂ) 2).segment_subset hwBall hzBall
    ⟨a, b, ha, hb, hab, rfl⟩
  have houterNorm : ‖a • w + b • z‖ < 2 := by
    simpa only [Metric.mem_ball, dist_zero_right] using houter
  refine ⟨by norm_num at houterNorm ⊢; exact houterNorm, ?_⟩
  rintro ⟨hre, him⟩
  have himEq : a * w.im + b * z.im = 0 := by
    have habs : |a * w.im + b * z.im| ≤ 0 := by
      simpa only [Complex.sub_im, Complex.one_im, sub_zero,
        Complex.add_im, Complex.smul_im, zero_mul, smul_eq_mul] using him
    exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
  have hwRe : w.im = 0 → w.re < 1 :=
    re_lt_one_of_mem_cartesianDelta_of_im_eq_zero hw
  have hzRe : z.im = 0 → z.re < 1 :=
    re_lt_one_of_mem_cartesianDelta_of_im_eq_zero hz
  have hreal : a * w.re + b * z.re < 1 := by
    rcases ha.eq_or_lt with rfl | haPos
    · have hbOne : b = 1 := by linarith
      simpa only [zero_mul, zero_add, hbOne, one_mul] using hzRe (by
        rcases hside with hside | hside <;> nlinarith)
    · rcases hb.eq_or_lt with rfl | hbPos
      · have haOne : a = 1 := by linarith
        simpa only [zero_mul, add_zero, haOne, one_mul] using hwRe (by
          rcases hside with hside | hside <;> nlinarith)
      · have haw : a * w.im = 0 := by
          rcases hside with hside | hside <;> nlinarith
        have hbz : b * z.im = 0 := by
          rcases hside with hside | hside <;> nlinarith
        have hwIm : w.im = 0 := (mul_eq_zero.mp haw).resolve_left haPos.ne'
        have hzIm : z.im = 0 := (mul_eq_zero.mp hbz).resolve_left hbPos.ne'
        nlinarith [hwRe hwIm, hzRe hzIm]
  have hre' : 1 ≤ a * w.re + b * z.re := by
    simpa only [Complex.sub_re, Complex.one_re, Complex.add_re,
      Complex.smul_re, smul_eq_mul, sub_nonneg] using hre
  exact (not_le_of_gt hreal) hre'

private theorem dist_one_lt_sq_of_mem_localCartesianDelta
    {r : ℝ} {w : ℂ} (hr : 0 < r)
    (hw : w ∈ localCartesianDelta 1 0 r) :
    dist w 1 < r ^ 2 := by
  have hsqrt : ‖Transfer.cartesianDeltaSqrt w‖ < r := by
    have hball := hw.2
    change Transfer.cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) r at hball
    simpa only [Metric.mem_ball, dist_zero_right] using hball
  have hsquare : ‖Transfer.cartesianDeltaSqrt w‖ ^ 2 = ‖1 - w‖ := by
    rw [← norm_pow, Transfer.cartesianDeltaSqrt_sq]
  rw [Complex.dist_eq, norm_sub_rev]
  nlinarith [norm_nonneg (Transfer.cartesianDeltaSqrt w)]

private theorem mem_localCartesianDelta_of_mem_cartesianDelta_of_dist_one_lt_sq
    {r : ℝ} {w : ℂ} (hr : 0 < r)
    (hwDelta : w ∈ Transfer.cartesianDelta 1 0)
    (hwDist : dist w 1 < r ^ 2) :
    w ∈ localCartesianDelta 1 0 r := by
  refine ⟨hwDelta, ?_⟩
  have hsquare : ‖Transfer.cartesianDeltaSqrt w‖ ^ 2 = ‖1 - w‖ := by
    rw [← norm_pow, Transfer.cartesianDeltaSqrt_sq]
  have hnorm : ‖Transfer.cartesianDeltaSqrt w‖ ^ 2 < r ^ 2 := by
    rw [hsquare]
    simpa only [Complex.dist_eq, norm_sub_rev] using hwDist
  change dist (Transfer.cartesianDeltaSqrt w) 0 < r
  simpa only [dist_zero_right] using
    (sq_lt_sq₀ (norm_nonneg (Transfer.cartesianDeltaSqrt w)) hr.le).mp hnorm

private theorem norm_one_sub_le_one_iff (u : ℂ) :
    ‖1 - u‖ ≤ 1 ↔ ‖u‖ ^ 2 ≤ 2 * u.re := by
  have hsq : ‖1 - u‖ ^ 2 = 1 + ‖u‖ ^ 2 - 2 * u.re := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hsq]
  norm_num

/-- The part of the closed unit disk lying between two circles about `1`
is joined to the same real anchor.  The normalized-chord part of the path
keeps its distance from `1` equal to `delta`, so the deleted inner disk is
never crossed. -/
private theorem joinedIn_closedUnitDiskAway_cap_real_anchor
    {delta R : ℝ} (hdelta : 0 < delta)
    (hdeltaTwo : delta ≤ 2) (hdeltaR : delta < R)
    {z : ℂ} (hzK : z ∈ closedUnitDiskAway delta)
    (hzR : z ∈ Metric.ball (1 : ℂ) R) :
    JoinedIn
      (closedUnitDiskAway delta ∩ Metric.ball (1 : ℂ) R)
      z (((1 - delta : ℝ) : ℂ)) := by
  let u : ℂ := 1 - z
  let rho : ℝ := ‖u‖
  let c : ℝ := delta / rho
  let v : ℂ := c • u
  let d : ℂ := (delta : ℂ)
  let C : Set ℂ := {x | delta ≤ ‖x‖ ∧ ‖x‖ < R ∧ ‖1 - x‖ ≤ 1}
  let phi : ℂ → ℂ := fun x ↦ 1 - x

  have hzNorm : ‖z‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hzK.1
  have huNorm : ‖u‖ = dist z 1 := by
    rw [Complex.dist_eq]
    simp only [u, norm_sub_rev]
  have hdeltaRho : delta ≤ rho := by
    have haway := hzK.2
    change delta ≤ dist z 1 at haway
    simpa only [rho, huNorm] using haway
  have hRhoPos : 0 < rho := hdelta.trans_le hdeltaRho
  have hRhoR : rho < R := by
    simpa only [rho, huNorm, Metric.mem_ball] using hzR
  have hcPos : 0 < c := div_pos hdelta hRhoPos
  have hcLe : c ≤ 1 := (div_le_one hRhoPos).2 hdeltaRho
  have hcRho : c * rho = delta := by
    dsimp only [c]
    exact div_mul_cancel₀ delta hRhoPos.ne'
  have huDisk : ‖1 - u‖ ≤ 1 := by
    simpa only [u, sub_sub_cancel] using hzNorm
  have huC : u ∈ C := ⟨hdeltaRho, hRhoR, huDisk⟩
  have hvNorm : ‖v‖ = delta := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos hcPos]
    simpa only [rho] using hcRho

  have hRadial : JoinedIn C u v := by
    apply JoinedIn.of_segment_subset
    rintro q ⟨a, b, ha, hb, hab, rfl⟩
    let lam : ℝ := a + b * c
    have hlam0 : 0 ≤ lam := by dsimp [lam]; positivity
    have hlamc : c ≤ lam := by
      dsimp [lam]
      nlinarith [hab, mul_nonneg ha (sub_nonneg.mpr hcLe)]
    have hlam1 : lam ≤ 1 := by
      dsimp [lam]
      nlinarith [hab, mul_nonneg hb (sub_nonneg.mpr hcLe)]
    have heq : a • u + b • v = lam • u := by
      dsimp only [v, lam]
      module
    rw [heq]
    have hnorm : ‖lam • u‖ = lam * rho := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0, rho]
    refine ⟨?_, ?_, ?_⟩
    · rw [hnorm, ← hcRho]
      exact mul_le_mul_of_nonneg_right hlamc hRhoPos.le
    · rw [hnorm]
      exact (mul_le_of_le_one_left hRhoPos.le hlam1).trans_lt hRhoR
    · calc
        ‖1 - lam • u‖ =
            ‖(1 - lam) • (1 : ℂ) + lam • (1 - u)‖ := by
              congr 1
              module
        _ ≤ ‖(1 - lam) • (1 : ℂ)‖ + ‖lam • (1 - u)‖ :=
          norm_add_le _ _
        _ = (1 - lam) + lam * ‖1 - u‖ := by
              simp only [norm_smul, norm_one,
                Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlam1),
                abs_of_nonneg hlam0, mul_one]
        _ ≤ (1 - lam) + lam * 1 := by gcongr
        _ = 1 := by ring

  have hvC : v ∈ C := hRadial.target_mem
  have hvDiskSq : delta ^ 2 ≤ 2 * v.re := by
    rw [← hvNorm]
    exact (norm_one_sub_le_one_iff v).mp hvC.2.2
  have hvRe : 0 < v.re := by nlinarith [sq_pos_of_pos hdelta]
  have hdC : d ∈ C := by
    have hdNorm : ‖d‖ = delta := by
      simp only [d, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdelta]
    refine ⟨by rw [hdNorm], by simpa only [hdNorm], ?_⟩
    apply (norm_one_sub_le_one_iff d).2
    simp only [d, Complex.ofReal_re, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hdelta]
    nlinarith

  let y : ℝ → ℂ := fun t ↦ (1 - t) • v + t • d
  let p : ℝ → ℂ := fun t ↦ (delta / ‖y t‖) • y t
  have hyRe : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (y t).re := by
    intro t ht
    dsimp only [y]
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul,
      d, Complex.ofReal_re]
    by_cases htOne : t = 1
    · subst t
      simpa using hdelta
    · have htLt : t < 1 := lt_of_le_of_ne ht.2 htOne
      have hleft : 0 < (1 - t) * v.re :=
        mul_pos (sub_pos.mpr htLt) hvRe
      have hright : 0 ≤ t * delta := mul_nonneg ht.1 hdelta.le
      linarith
  have hyNe : ∀ t ∈ Set.Icc (0 : ℝ) 1, y t ≠ 0 := by
    intro t ht hzero
    have hpos := hyRe t ht
    rw [hzero, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hyNorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖y t‖ ≤ delta := by
    intro t ht
    calc
      ‖y t‖ ≤ ‖(1 - t) • v‖ + ‖t • d‖ := norm_add_le _ _
      _ = (1 - t) * delta + t * delta := by
        have hdNorm : ‖d‖ = delta := by
          simp only [d, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdelta]
        rw [norm_smul, hvNorm, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr ht.2), norm_smul, hdNorm,
          Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ = delta := by ring
  have hpMem : ∀ t ∈ Set.Icc (0 : ℝ) 1, p t ∈ C := by
    intro t ht
    have hyPos : 0 < ‖y t‖ := norm_pos_iff.mpr (hyNe t ht)
    have hkPos : 0 < delta / ‖y t‖ := div_pos hdelta hyPos
    have hkOne : 1 ≤ delta / ‖y t‖ :=
      (le_div_iff₀ hyPos).2 (by simpa only [one_mul] using hyNorm t ht)
    have hpNorm : ‖p t‖ = delta := by
      simp only [p, norm_smul, Real.norm_eq_abs, abs_of_pos hkPos]
      exact div_mul_cancel₀ delta hyPos.ne'
    have hyDiskSq : delta ^ 2 ≤ 2 * (y t).re := by
      have hdSq : delta ^ 2 ≤ 2 * delta := by nlinarith
      dsimp only [y]
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul,
        d, Complex.ofReal_re]
      have hleft := mul_le_mul_of_nonneg_left hvDiskSq
        (sub_nonneg.mpr ht.2)
      have hright := mul_le_mul_of_nonneg_left hdSq ht.1
      nlinarith
    have hpDiskSq : ‖p t‖ ^ 2 ≤ 2 * (p t).re := by
      rw [hpNorm]
      have hscale : (y t).re ≤ (delta / ‖y t‖) * (y t).re := by
        nlinarith [hyRe t ht]
      have hpRe : (p t).re = (delta / ‖y t‖) * (y t).re := by
        simp only [p, Complex.smul_re, smul_eq_mul]
      rw [hpRe]
      exact hyDiskSq.trans (mul_le_mul_of_nonneg_left hscale (by norm_num))
    exact ⟨by rw [hpNorm], by rw [hpNorm]; exact hdeltaR,
      (norm_one_sub_le_one_iff (p t)).2 hpDiskSq⟩
  have hpCont : ContinuousOn p (Set.Icc (0 : ℝ) 1) := by
    have hyCont : Continuous y := by fun_prop
    exact ((continuousOn_const.div hyCont.norm.continuousOn
      (fun t ht ↦ norm_ne_zero_iff.mpr (hyNe t ht))).smul
        hyCont.continuousOn)
  have hpZero : p 0 = v := by
    simp only [p, y, zero_smul, sub_zero, one_smul, add_zero, hvNorm,
      div_self hdelta.ne', one_smul]
  have hpOne : p 1 = d := by
    have hdNorm : ‖d‖ = delta := by
      simp only [d, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdelta]
    simp only [p, y, one_smul, sub_self, zero_smul, zero_add, hdNorm,
      div_self hdelta.ne']
  have hArc : JoinedIn C v d :=
    JoinedIn.ofLine hpCont hpZero hpOne (by
      rintro _ ⟨t, ht, rfl⟩
      exact hpMem t ht)
  have hUC : JoinedIn C u d := hRadial.trans hArc

  have hPhiCont : Continuous phi := by fun_prop
  have hImageSub : phi '' C ⊆
      closedUnitDiskAway delta ∩ Metric.ball (1 : ℂ) R := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [phi, Metric.mem_closedBall, dist_zero_right] using hx.2.2
    · change delta ≤ dist (phi x) 1
      simpa only [phi, Complex.dist_eq, sub_sub_cancel_left,
        norm_neg] using hx.1
    · simpa only [phi, Metric.mem_ball, Complex.dist_eq,
        sub_sub_cancel_left, norm_neg] using hx.2.1
  have hMapped : JoinedIn (phi '' C) (phi u) (phi d) :=
    hUC.map hPhiCont
  have hFinal := hMapped.mono hImageSub
  simpa only [phi, u, d, sub_sub_cancel, Complex.ofReal_sub,
    Complex.ofReal_one] using hFinal

/-- Every component of the smaller fold/thickening overlap meets the same
real anchor `1 - delta` inside the larger overlap.  This fixed-anchor form
is the one needed to normalize additive constants in scalar primitives;
it uses only one-variable geometry and no compactness of the field ball. -/
theorem localDelta_thickening_target_components_contain_real_anchor
    {delta s rSmall rBig : ℝ}
    (hdelta : 0 < delta) (hdeltaTwo : delta ≤ 2) (hs : 0 < s)
    (hrSmall : 0 < rSmall) (hrBig : 0 < rBig)
    (hmargin : rSmall ^ 2 + s < rBig ^ 2)
    (hdeltaSmall : delta ≤ rSmall ^ 2) :
    let a : ℂ := ((1 - delta : ℝ) : ℂ)
    a ∈ localCartesianDelta 1 0 rBig ∩
        Metric.thickening s (closedUnitDiskAway delta) ∧
    ∀ w ∈ localCartesianDelta 1 0 rSmall ∩
        Metric.thickening s (closedUnitDiskAway delta),
      a ∈ connectedComponentIn
        (localCartesianDelta 1 0 rBig ∩
          Metric.thickening s (closedUnitDiskAway delta)) w := by
  let a : ℂ := ((1 - delta : ℝ) : ℂ)
  change a ∈ localCartesianDelta 1 0 rBig ∩
      Metric.thickening s (closedUnitDiskAway delta) ∧
    ∀ w ∈ localCartesianDelta 1 0 rSmall ∩
        Metric.thickening s (closedUnitDiskAway delta),
      a ∈ connectedComponentIn
        (localCartesianDelta 1 0 rBig ∩
          Metric.thickening s (closedUnitDiskAway delta)) w
  have hSmallBigSq : rSmall ^ 2 < rBig ^ 2 := by linarith
  have hdeltaBig : delta < rBig ^ 2 := hdeltaSmall.trans_lt hSmallBigSq
  have haNorm : ‖a‖ ≤ 1 := by
    dsimp only [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have haDist : dist a 1 = delta := by
    rw [Complex.dist_eq]
    dsimp only [a]
    push_cast
    rw [show ((1 - delta : ℂ) - 1) = (-delta : ℂ) by ring,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdelta]
  have haK : a ∈ closedUnitDiskAway delta := by
    refine ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using haNorm, ?_⟩
    change delta ≤ dist a 1
    rw [haDist]
  have haDelta : a ∈ Transfer.cartesianDelta 1 0 :=
    closedUnitDiskAway_subset_cartesianDelta hdelta haK
  have haLocal : a ∈ localCartesianDelta 1 0 rBig :=
    mem_localCartesianDelta_of_mem_cartesianDelta_of_dist_one_lt_sq
      hrBig haDelta (by simpa only [haDist] using hdeltaBig)
  have haThick : a ∈ Metric.thickening s (closedUnitDiskAway delta) :=
    Metric.self_subset_thickening hs _ haK
  refine ⟨⟨haLocal, haThick⟩, ?_⟩
  intro w hw
  obtain ⟨z, hzK, hwz⟩ := Metric.mem_thickening_iff.mp hw.2
  obtain ⟨z', hz'K, hz'dist, hside⟩ :=
    exists_same_halfPlane_witness (w := w) hzK
  have hwz' : dist w z' < s := hz'dist.trans_lt hwz
  have hwDistSmall : dist w 1 < rSmall ^ 2 :=
    dist_one_lt_sq_of_mem_localCartesianDelta hrSmall hw.1
  have hz'DistBig : dist z' 1 < rBig ^ 2 := by
    calc
      dist z' 1 ≤ dist z' w + dist w 1 := dist_triangle _ _ _
      _ < s + rSmall ^ 2 := by rw [dist_comm z' w]; linarith
      _ < rBig ^ 2 := by linarith
  have hz'Delta : z' ∈ Transfer.cartesianDelta 1 0 :=
    closedUnitDiskAway_subset_cartesianDelta hdelta hz'K
  let O : Set ℂ := localCartesianDelta 1 0 rBig ∩
    Metric.thickening s (closedUnitDiskAway delta)
  have hBallThick : Metric.ball z' s ⊆
      Metric.thickening s (closedUnitDiskAway delta) := by
    intro q hq
    exact Metric.mem_thickening_iff.mpr ⟨z', hz'K, hq⟩
  have hsegWZ : segment ℝ w z' ⊆ O := by
    intro q hq
    have hqDelta := segment_subset_cartesianDelta_of_same_halfPlane
      hw.1.1 hz'Delta hside hq
    have hqFoldBall := (convex_ball (1 : ℂ) (rBig ^ 2)).segment_subset
      (hwDistSmall.trans hSmallBigSq) hz'DistBig hq
    have hqFold :=
      mem_localCartesianDelta_of_mem_cartesianDelta_of_dist_one_lt_sq
        hrBig hqDelta hqFoldBall
    have hqThick := hBallThick
      ((convex_ball z' s).segment_subset
        (by simpa only [Metric.mem_ball] using hwz')
        (Metric.mem_ball_self hs) hq)
    exact ⟨hqFold, hqThick⟩
  have hWZ : JoinedIn O w z' := JoinedIn.of_segment_subset hsegWZ
  have hZAInCap : JoinedIn
      (closedUnitDiskAway delta ∩ Metric.ball (1 : ℂ) (rBig ^ 2))
      z' a := by
    simpa only [a] using
      (joinedIn_closedUnitDiskAway_cap_real_anchor
        hdelta hdeltaTwo hdeltaBig hz'K
        (by simpa only [Metric.mem_ball] using hz'DistBig))
  have hCapSubO :
      closedUnitDiskAway delta ∩ Metric.ball (1 : ℂ) (rBig ^ 2) ⊆ O := by
    intro q hq
    have hqDelta : q ∈ Transfer.cartesianDelta 1 0 :=
      closedUnitDiskAway_subset_cartesianDelta hdelta hq.1
    have hqLocal : q ∈ localCartesianDelta 1 0 rBig :=
      mem_localCartesianDelta_of_mem_cartesianDelta_of_dist_one_lt_sq
        hrBig hqDelta (by simpa only [Metric.mem_ball] using hq.2)
    exact ⟨hqLocal, Metric.self_subset_thickening hs _ hq.1⟩
  have hZA : JoinedIn O z' a := hZAInCap.mono hCapSubO
  have hjoin : JoinedIn O w a := hWZ.trans hZA
  obtain ⟨gamma, hgamma⟩ := hjoin
  have hwRange : w ∈ Set.range gamma := ⟨0, by simp⟩
  have haRange : a ∈ Set.range gamma := ⟨1, by simp⟩
  have hRangeSub : Set.range gamma ⊆ O := Set.range_subset_iff.mpr hgamma
  exact (isPreconnected_range gamma.continuous).subset_connectedComponentIn
    hwRange hRangeSub haRange

/-- Every point in the smaller fold/thickening overlap belongs, in the
larger overlap, to a component meeting the zero-field lens.  The strict
margin is used twice: first to move from the target point to a nearby point
of the compact closed-disk set, and then to move that point slightly into
the open unit disk. -/
theorem localDelta_thickening_target_components_meet_lens
    {delta s rSmall rBig ell : ℝ}
    (hdelta : 0 < delta) (hs : 0 < s)
    (hrSmall : 0 < rSmall) (hrBig : 0 < rBig)
    (hmargin : rSmall ^ 2 + s < rBig ^ 2)
    (hBigEll : rBig ≤ ell) :
    ∀ w ∈ localCartesianDelta 1 0 rSmall ∩
        Metric.thickening s (closedUnitDiskAway delta),
      ∃ w₀ : ℂ,
        w₀ ∈ connectedComponentIn
          (localCartesianDelta 1 0 rBig ∩
            Metric.thickening s (closedUnitDiskAway delta)) w ∧
        w₀ ∈ Metric.ball (0 : ℂ) 1 ∩
          Metric.ball (1 : ℂ) (ell ^ 2) := by
  intro w hw
  obtain ⟨z, hzK, hwz⟩ := Metric.mem_thickening_iff.mp hw.2
  obtain ⟨z', hz'K, hz'dist, hside⟩ :=
    exists_same_halfPlane_witness (w := w) hzK
  have hwz' : dist w z' < s := hz'dist.trans_lt hwz
  have hwDistSmall : dist w 1 < rSmall ^ 2 :=
    dist_one_lt_sq_of_mem_localCartesianDelta hrSmall hw.1
  have hz'DistBig : dist z' 1 < rBig ^ 2 := by
    calc
      dist z' 1 ≤ dist z' w + dist w 1 := dist_triangle _ _ _
      _ < s + rSmall ^ 2 := by rw [dist_comm z' w]; linarith
      _ < rBig ^ 2 := by linarith
  have hBigSqEll : rBig ^ 2 ≤ ell ^ 2 := by
    have hell : 0 < ell := hrBig.trans_le hBigEll
    nlinarith
  have hzNorm : ‖z'‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz'K.1
  let a : ℝ := min (1 / 2)
    (min ((s - dist w z') / 2) ((rBig ^ 2 - dist z' 1) / 2))
  have ha : 0 < a := by
    dsimp only [a]
    exact lt_min (by norm_num) (lt_min (half_pos (sub_pos.mpr hwz'))
      (half_pos (sub_pos.mpr hz'DistBig)))
  have haHalf : a ≤ 1 / 2 := min_le_left _ _
  have haOne : a < 1 := by linarith
  have haThick : a < s - dist w z' := by
    have hle : a ≤ (s - dist w z') / 2 :=
      (min_le_right (1 / 2)
        (min ((s - dist w z') / 2)
          ((rBig ^ 2 - dist z' 1) / 2))).trans
        (min_le_left _ _)
    linarith
  have haFold : a < rBig ^ 2 - dist z' 1 := by
    have hle : a ≤ (rBig ^ 2 - dist z' 1) / 2 :=
      (min_le_right (1 / 2)
        (min ((s - dist w z') / 2)
          ((rBig ^ 2 - dist z' 1) / 2))).trans
        (min_le_right _ _)
    linarith
  let w₀ : ℂ := ((1 - a : ℝ) : ℂ) * z'
  have hw₀z : dist w₀ z' = a * ‖z'‖ := by
    rw [Complex.dist_eq]
    have heq : w₀ - z' = ((-a : ℝ) : ℂ) * z' := by
      dsimp only [w₀]
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_neg, abs_of_pos ha]
  have hw₀z_le : dist w₀ z' ≤ a := by
    rw [hw₀z]
    nlinarith [norm_nonneg z']
  have hw₀Norm : ‖w₀‖ < 1 := by
    dsimp only [w₀]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr haOne)]
    nlinarith [norm_nonneg z']
  have hw₀DistBig : dist w₀ 1 < rBig ^ 2 := by
    calc
      dist w₀ 1 ≤ dist w₀ z' + dist z' 1 := dist_triangle _ _ _
      _ ≤ a + dist z' 1 := by linarith
      _ < rBig ^ 2 := by linarith
  have hw₀Ball : w₀ ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hw₀Norm
  have hw₀Lens : w₀ ∈ Metric.ball (0 : ℂ) 1 ∩
      Metric.ball (1 : ℂ) (ell ^ 2) := by
    exact ⟨hw₀Ball, hw₀DistBig.trans_le hBigSqEll⟩
  have hwBig : w ∈ localCartesianDelta 1 0 rBig := by
    apply mem_localCartesianDelta_of_mem_cartesianDelta_of_dist_one_lt_sq hrBig
      hw.1.1
    exact hwDistSmall.trans (by nlinarith)
  have hz'Delta : z' ∈ Transfer.cartesianDelta 1 0 :=
    closedUnitDiskAway_subset_cartesianDelta hdelta hz'K
  have hz'Big : z' ∈ localCartesianDelta 1 0 rBig :=
    mem_localCartesianDelta_of_mem_cartesianDelta_of_dist_one_lt_sq
      hrBig hz'Delta hz'DistBig
  have hw₀Delta : w₀ ∈ Transfer.cartesianDelta 1 0 :=
    Transfer.unit_ball_subset_cartesianDelta (by norm_num) hw₀Ball
  have hw₀Big : w₀ ∈ localCartesianDelta 1 0 rBig :=
    mem_localCartesianDelta_of_mem_cartesianDelta_of_dist_one_lt_sq
      hrBig hw₀Delta hw₀DistBig
  let O : Set ℂ := localCartesianDelta 1 0 rBig ∩
    Metric.thickening s (closedUnitDiskAway delta)
  have hBallThick : Metric.ball z' s ⊆
      Metric.thickening s (closedUnitDiskAway delta) := by
    intro q hq
    exact Metric.mem_thickening_iff.mpr ⟨z', hz'K, hq⟩
  have hsegWZ : segment ℝ w z' ⊆ O := by
    intro q hq
    have hqDelta := segment_subset_cartesianDelta_of_same_halfPlane
      hw.1.1 hz'Delta hside hq
    have hqFoldBall := (convex_ball (1 : ℂ) (rBig ^ 2)).segment_subset
      (by exact hwDistSmall.trans (by nlinarith)) hz'DistBig hq
    have hqFold :=
      mem_localCartesianDelta_of_mem_cartesianDelta_of_dist_one_lt_sq
        hrBig hqDelta hqFoldBall
    have hqThick := hBallThick
      ((convex_ball z' s).segment_subset
        (by simpa only [Metric.mem_ball] using hwz')
        (Metric.mem_ball_self hs) hq)
    exact ⟨hqFold, hqThick⟩
  have hz'w₀Side :
      (0 ≤ z'.im ∧ 0 ≤ w₀.im) ∨
        (z'.im ≤ 0 ∧ w₀.im ≤ 0) := by
    rcases hside with hside | hside
    · left
      refine ⟨hside.2, ?_⟩
      dsimp only [w₀]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      exact mul_nonneg (sub_nonneg.mpr haOne.le) hside.2
    · right
      refine ⟨hside.2, ?_⟩
      dsimp only [w₀]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr haOne.le) hside.2
  have hsegZW₀ : segment ℝ z' w₀ ⊆ O := by
    intro q hq
    have hqDelta := segment_subset_cartesianDelta_of_same_halfPlane
      hz'Delta hw₀Delta hz'w₀Side hq
    have hqFoldBall := (convex_ball (1 : ℂ) (rBig ^ 2)).segment_subset
      hz'DistBig hw₀DistBig hq
    have hqFold :=
      mem_localCartesianDelta_of_mem_cartesianDelta_of_dist_one_lt_sq
        hrBig hqDelta hqFoldBall
    have hw₀InBall : w₀ ∈ Metric.ball z' s := by
      rw [Metric.mem_ball]
      exact hw₀z_le.trans_lt (by
        nlinarith [show 0 ≤ dist w z' from dist_nonneg])
    have hqThick := hBallThick
      ((convex_ball z' s).segment_subset (Metric.mem_ball_self hs)
        hw₀InBall hq)
    exact ⟨hqFold, hqThick⟩
  have hjoin : JoinedIn O w w₀ :=
    (JoinedIn.of_segment_subset hsegWZ).trans
      (JoinedIn.of_segment_subset hsegZW₀)
  obtain ⟨gamma, hgamma⟩ := hjoin
  have hwRange : w ∈ Set.range gamma := ⟨0, by simp⟩
  have hw₀Range : w₀ ∈ Set.range gamma := ⟨1, by simp⟩
  have hRangeSub : Set.range gamma ⊆ O := Set.range_subset_iff.mpr hgamma
  have hw₀Component : w₀ ∈ connectedComponentIn O w :=
    (isPreconnected_range gamma.continuous).subset_connectedComponentIn
      hwRange hRangeSub hw₀Range
  exact ⟨w₀, hw₀Component, hw₀Lens⟩

end PerronWright.TreeNormalizedClosedDiskGluing
