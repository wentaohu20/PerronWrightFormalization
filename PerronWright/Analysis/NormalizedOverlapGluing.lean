import PerronWright.Analysis.NormalizedFoldActivity
import PerronWright.Analysis.NormalizedUnitAway
import PerronWright.Analysis.TreeJointOverlapUniqueness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Gluing the normalized fold and unit-away profiles

This scratch file constructs a genuine joint overlap rather than assuming
one.  A nontrivial point `zeta = exp (i theta)` is chosen on the unit circle
arbitrarily close to `1`, and is then moved a small radial distance into the
open unit disc.  The resulting complex seed lies both in the fold lens and
in the uniform unit-away thickening.  Openness then supplies one explicit
product of a complex ball and a field ball on which generic complex-seed
uniqueness glues the two normalized profiles.
-/

open Filter Topology
open scoped Classical ComplexOrder ENNReal NNReal

noncomputable section

namespace PerronWright.TreeNormalizedOverlapGluing

open PerronWright
open PerronWright.TreeNormalizedFoldActivity
open PerronWright.TreeNormalizedUnitAway

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The normalized fold and unit-away continuations agree on a nonempty open
preconnected product contained in both of their proved domains.  In
particular, the seed used below is genuinely complex and lies strictly inside
the unit disc; no overlap geometry is added as a hypothesis. -/
theorem exists_normalizedFold_unitAway_common_product
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (rFold : ℝ) (U : Set ℂ) (ε : ℝ)
        (Ψ : ℂ × C(S, ℂ) → C(S, ℂ)) (w₀ : ℂ) (s : ℝ),
      0 < rFold ∧ 0 < ε ∧ 0 < s ∧ ‖w₀‖ < 1 ∧
      (Metric.ball w₀ s ×ˢ Metric.ball (0 : C(S, ℂ)) s).Nonempty ∧
      IsOpen (Metric.ball w₀ s ×ˢ Metric.ball (0 : C(S, ℂ)) s) ∧
      IsPreconnected
        (Metric.ball w₀ s ×ˢ Metric.ball (0 : C(S, ℂ)) s) ∧
      Metric.ball w₀ s ×ˢ Metric.ball (0 : C(S, ℂ)) s ⊆
        localCartesianDelta 1 0 rFold ×ˢ
          Metric.ball (0 : C(S, ℂ)) rFold ∧
      Metric.ball w₀ s ×ˢ Metric.ball (0 : C(S, ℂ)) s ⊆
        normalizedUnitAwayDomain M hM U ε ∧
      Set.EqOn
        (normalizedFoldProfile M hM)
        (normalizedUnitAwayProfile M hM Ψ)
        (Metric.ball w₀ s ×ˢ Metric.ball (0 : C(S, ℂ)) s) := by
  obtain ⟨rLens, hrLens, hLens⟩ :=
    exists_normalizedFoldProfile_eq_rootedTreeSeries_on_lens M hM
  obtain ⟨rFold, hrFold, hFoldOpen, -, hFoldAnalytic, hFoldData⟩ :=
    exists_normalizedFoldProfile_cartesianDelta_product
      M hM (η := 1) (m := 0) (by norm_num)

  -- A scale which fits simultaneously in the lens of the zero-field
  -- identity and in the actual fold chart used below.
  let L : ℝ := min (rLens ^ 2) (rFold ^ 2)
  have hL : 0 < L := lt_min (pow_pos hrLens 2) (pow_pos hrFold 2)
  let θ : ℝ := min L Real.pi / 8
  have hθ : 0 < θ := by
    dsimp only [θ]
    exact div_pos (lt_min hL Real.pi_pos) (by norm_num)
  have hθL : θ < L / 4 := by
    dsimp only [θ]
    have hle := min_le_left L Real.pi
    nlinarith
  have hθpi : θ < Real.pi := by
    dsimp only [θ]
    have hle := min_le_right L Real.pi
    nlinarith [Real.pi_pos]

  -- The nontrivial unit-circle point which creates the overlap.  Its
  -- distance from `1` can be made smaller than both fold scales.
  let ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hζnorm : ‖ζ‖ = 1 := by
    simpa only [ζ] using Complex.norm_exp_ofReal_mul_I θ
  have hζsphere : ζ ∈ Metric.sphere (0 : ℂ) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, hζnorm]
  have hζne : ζ ≠ 1 := by
    have hζim : ζ.im = Real.sin θ := by
      simp [ζ, Complex.exp_mul_I, ← Complex.ofReal_sin]
    intro hEq
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ hθpi
    have hsin0 : Real.sin θ = 0 := by
      rw [← hζim, hEq]
      exact Complex.one_im
    exact hsin.ne' hsin0
  have hζdist : dist ζ 1 ≤ θ := by
    rw [Complex.dist_eq]
    calc
      ‖ζ - 1‖ = ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ := by
        dsimp only [ζ]
        rw [mul_comm]
      _ ≤ ‖θ‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = θ := by
        rw [Real.norm_eq_abs, abs_of_pos hθ]
  have hζclose : dist ζ 1 < L / 4 := hζdist.trans_lt hθL

  -- The cutoff is defined from the constructed point, so membership in the
  -- compact unit arc is automatic while positivity uses `ζ != 1` genuinely.
  let δ : ℝ := dist ζ 1 / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact half_pos (dist_pos.mpr hζne)
  have hζArc : ζ ∈ normalizedUnitArc δ := by
    refine ⟨hζsphere, ?_⟩
    dsimp only [δ]
    exact half_le_self dist_nonneg

  obtain ⟨U, ε, Ψ, hUopen, hArc, hε, hUnitOpen, -,
      hUnitAnalytic, -, hUnitInside, hUnitUniqRaw⟩ :=
    exists_normalized_rootedTreeSeries_joint_analytic_continuation_unit_away
      M hM hδ
  obtain ⟨rUnit, hrUnit, -, hThick⟩ :=
    exists_uniform_normalized_unitArc_thickening
      M hM hδ hε hArc hUnitOpen

  -- Move `ζ` radially inward by `a`.  The three cutoffs make the movement
  -- fit the unit-away thickness, the two fold scales, and the open unit disc.
  let a : ℝ := min (rUnit / 2) (min (L / 8) (1 / 2))
  have ha : 0 < a := by
    dsimp only [a]
    exact lt_min (half_pos hrUnit)
      (lt_min (by positivity) (by norm_num))
  have harUnit : a < rUnit := by
    calc
      a ≤ rUnit / 2 := min_le_left _ _
      _ < rUnit := half_lt_self hrUnit
  have haL : a < L / 4 := by
    have hle : a ≤ L / 8 :=
      (min_le_right (rUnit / 2) (min (L / 8) (1 / 2))).trans
        (min_le_left (L / 8) (1 / 2))
    nlinarith
  have ha1 : a < 1 := by
    have hle : a ≤ 1 / 2 :=
      (min_le_right (rUnit / 2) (min (L / 8) (1 / 2))).trans
        (min_le_right (L / 8) (1 / 2))
    norm_num at hle ⊢
    linarith

  let w₀ : ℂ := ((1 - a : ℝ) : ℂ) * ζ
  have hw₀ζ : dist w₀ ζ = a := by
    rw [Complex.dist_eq]
    have heq : w₀ - ζ = ((-a : ℝ) : ℂ) * ζ := by
      dsimp only [w₀]
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_neg, abs_of_pos ha, hζnorm, mul_one]
  have hw₀norm_eq : ‖w₀‖ = 1 - a := by
    dsimp only [w₀]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr ha1), hζnorm, mul_one]
  have hw₀norm : ‖w₀‖ < 1 := by
    rw [hw₀norm_eq]
    linarith
  have hw₀close : dist w₀ 1 < L := by
    calc
      dist w₀ 1 ≤ dist w₀ ζ + dist ζ 1 := dist_triangle _ _ _
      _ = a + dist ζ 1 := by rw [hw₀ζ]
      _ < L / 4 + L / 4 := add_lt_add haL hζclose
      _ < L := by linarith

  have hw₀Ball0 : w₀ ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hw₀norm
  have hw₀Lens : w₀ ∈
      Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (rLens ^ 2) := by
    refine ⟨hw₀Ball0, ?_⟩
    rw [Metric.mem_ball]
    exact hw₀close.trans_le (min_le_left (rLens ^ 2) (rFold ^ 2))

  have hw₀LocalFold : w₀ ∈ localCartesianDelta 1 0 rFold := by
    refine ⟨Transfer.unit_ball_subset_cartesianDelta (by norm_num) hw₀Ball0, ?_⟩
    have hnorm : ‖1 - w₀‖ < rFold ^ 2 := by
      have hdist : dist w₀ 1 < rFold ^ 2 :=
        hw₀close.trans_le (min_le_right (rLens ^ 2) (rFold ^ 2))
      simpa only [Complex.dist_eq, norm_sub_rev] using hdist
    have hsquare : ‖Transfer.cartesianDeltaSqrt w₀‖ ^ 2 = ‖1 - w₀‖ := by
      rw [← norm_pow, Transfer.cartesianDeltaSqrt_sq]
    have hsqrt : ‖Transfer.cartesianDeltaSqrt w₀‖ < rFold := by
      nlinarith [norm_nonneg (Transfer.cartesianDeltaSqrt w₀)]
    change Transfer.cartesianDeltaSqrt w₀ ∈ Metric.ball (0 : ℂ) rFold
    simpa only [Metric.mem_ball, dist_zero_right] using hsqrt

  let q₀ : ℂ × C(S, ℂ) := (w₀, 0)
  let DFold : Set (ℂ × C(S, ℂ)) :=
    localCartesianDelta 1 0 rFold ×ˢ
      Metric.ball (0 : C(S, ℂ)) rFold
  let DUnit : Set (ℂ × C(S, ℂ)) :=
    normalizedUnitAwayDomain M hM U ε
  have hq₀Fold : q₀ ∈ DFold := by
    exact ⟨hw₀LocalFold, Metric.mem_ball_self hrFold⟩
  have hw₀Thick : w₀ ∈ Metric.thickening rUnit (normalizedUnitArc δ) := by
    apply Metric.mem_thickening_iff.mpr
    exact ⟨ζ, hζArc, by simpa only [hw₀ζ] using harUnit⟩
  have hq₀Unit : q₀ ∈ DUnit := by
    exact hThick ⟨hw₀Thick, Metric.mem_ball_self hrUnit⟩

  -- Both domains are open at the same genuinely complex seed.  One product
  -- ball is therefore contained in their intersection.
  have hCommonNhd : DFold ∩ DUnit ∈ 𝓝 q₀ :=
    (hFoldOpen.inter hUnitOpen).mem_nhds ⟨hq₀Fold, hq₀Unit⟩
  obtain ⟨s, hs, hsSub⟩ := Metric.mem_nhds_iff.mp hCommonNhd
  let V : Set (ℂ × C(S, ℂ)) :=
    Metric.ball w₀ s ×ˢ Metric.ball (0 : C(S, ℂ)) s
  have hVeq : V = Metric.ball q₀ s := by
    simpa only [V, q₀] using
      (ball_prod_same w₀ (0 : C(S, ℂ)) s)
  have hVSubCommon : V ⊆ DFold ∩ DUnit := by
    rw [hVeq]
    exact hsSub
  have hVFold : V ⊆ DFold := fun q hq => (hVSubCommon hq).1
  have hVUnit : V ⊆ DUnit := fun q hq => (hVSubCommon hq).2
  have hVopen : IsOpen V :=
    Metric.isOpen_ball.prod Metric.isOpen_ball
  have hVpre : IsPreconnected V :=
    (convex_ball w₀ s).isPreconnected.prod
      (convex_ball (0 : C(S, ℂ)) s).isPreconnected
  have hVnonempty : V.Nonempty :=
    ⟨(w₀, (0 : C(S, ℂ))),
      Metric.mem_ball_self hs, Metric.mem_ball_self hs⟩
  have hq₀V : q₀ ∈ V := by
    exact ⟨Metric.mem_ball_self hs, Metric.mem_ball_self hs⟩

  let ΨUnit : ℂ × C(S, ℂ) → C(S, ℂ) :=
    normalizedUnitAwayProfile M hM Ψ
  let R : ((ℂ × C(S, ℂ)) × C(S, ℂ)) → C(S, ℂ) :=
    fun p => TreeCritical.residual M (activityMap M hM p.1, p.2)
  have hUnitA : AnalyticOnNhd ℂ ΨUnit V := by
    intro q hq
    exact hUnitAnalytic q (hVUnit hq)
  have hFoldA : AnalyticOnNhd ℂ (normalizedFoldProfile M hM) V := by
    intro q hq
    exact hFoldAnalytic q (hVFold hq)
  have hFoldRes : ∀ q ∈ V,
      R (q, normalizedFoldProfile M hM q) = 0 := by
    intro q hq
    exact (hFoldData q (hVFold hq)).2.1

  have hw₀U : w₀ ∈ U := by
    have htarget : activityMap M hM (w₀, 0) ∈
        U ×ˢ Metric.ball (0 : C(S, ℂ)) ε := hq₀Unit
    rw [activityMap_zeroField] at htarget
    exact htarget.1
  have hUnitSeed : ΨUnit q₀ = M.rootedTreeSeries w₀ := by
    simpa only [ΨUnit, q₀] using hUnitInside w₀ hw₀U hw₀norm
  have hFoldSeed : normalizedFoldProfile M hM q₀ =
      M.rootedTreeSeries w₀ := by
    simpa only [q₀] using hLens hw₀Lens
  have hSeed : ΨUnit q₀ = normalizedFoldProfile M hM q₀ :=
    hUnitSeed.trans hFoldSeed.symm
  have hUnitUniq : ∀ᶠ p in
      nhds (q₀, ΨUnit q₀),
      R p = 0 ↔ ΨUnit p.1 = p.2 := by
    simpa only [q₀, ΨUnit, R] using hUnitUniqRaw w₀ hw₀U

  have hEqUnitFold : Set.EqOn ΨUnit (normalizedFoldProfile M hM) V :=
    analytic_solutions_agree_on_open_preconnected_overlap_of_local_uniqueness
      R V hVopen hVpre ΨUnit (normalizedFoldProfile M hM)
      hUnitA hFoldA hFoldRes q₀ hq₀V hSeed hUnitUniq
  have hEqFoldUnit : Set.EqOn (normalizedFoldProfile M hM) ΨUnit V :=
    fun q hq => (hEqUnitFold hq).symm

  refine ⟨rFold, U, ε, Ψ, w₀, s, hrFold, hε, hs, hw₀norm,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [V] using hVnonempty
  · simpa only [V] using hVopen
  · simpa only [V] using hVpre
  · simpa only [V, DFold] using hVFold
  · simpa only [V, DUnit] using hVUnit
  · simpa only [V, ΨUnit] using hEqFoldUnit

end PerronWright.TreeNormalizedOverlapGluing
