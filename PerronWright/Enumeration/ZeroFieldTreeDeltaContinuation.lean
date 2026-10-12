import PerronWright.Enumeration.ZeroFieldTreeEGFMatching
import PerronWright.Analysis.NormalizedDeltaProfile

/-!
# Cartesian-Delta continuation of the zero-field tree EGF

The genuine unrooted-tree series was matched to the integrated fold germ on
the positive physical ray in `ZeroFieldTreeEGFMatching`.  Here we transport
that germ through the canonical coordinate `X(w) = sqrt (1-w)` and use the
identity theorem to upgrade the physical-ray equality to the full complex
lens.  The resulting formula is already in the activity coordinate consumed
by Cartesian transfer.
-/

open Filter Topology Set
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.ZeroFieldTreeDeltaContinuation

open PerronWright.ZeroFieldTreeLocalSingularity
open PerronWright.ZeroFieldTreeIntegratedSingularity

namespace Match

export PerronWright.ZeroFieldTreeEGFMatching
  (zeroFieldTreeSeries zeroFieldTreeSeries_analyticOnNhd_unit
    exists_positive_ray_treeSeries_eq_const_add_of_primitive)

end Match

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- A local activity-coordinate continuation which agrees with the genuine
tree EGF on the positive physical ray agrees with it on the entire complex
lens. -/
theorem localContinuation_eq_zeroFieldTreeSeries_on_lens
    (M : CompactBJRModel S)
    {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r))
    (hphysical : ∀ X : ℝ, 0 < X → X < r →
      Match.zeroFieldTreeSeries M (((1 - X ^ 2 : ℝ) : ℂ)) =
        F (((1 - X ^ 2 : ℝ) : ℂ))) :
    Set.EqOn F (Match.zeroFieldTreeSeries M)
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
  have hg : AnalyticOnNhd ℂ (Match.zeroFieldTreeSeries M) U :=
    (Match.zeroFieldTreeSeries_analyticOnNhd_unit M).mono
      inter_subset_left
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
  have hIevent : ∀ᶠ x : ℝ in nhds w₀, x ∈ Set.Ioo b 1 :=
    isOpen_Ioo.mem_nhds hw₀I
  have hreal : ∃ᶠ x : ℝ in nhdsWithin w₀ {w₀}ᶜ,
      F (x : ℂ) = Match.zeroFieldTreeSeries M (x : ℂ) := by
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

  have hcomplex : ∃ᶠ z : ℂ in nhdsWithin (w₀ : ℂ) {(w₀ : ℂ)}ᶜ,
      F z = Match.zeroFieldTreeSeries M z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hxs_tendsto, hxs_eq⟩ := hreal
    refine ⟨fun n ↦ (xs n : ℂ), ?_, fun n ↦ hxs_eq n⟩
    rw [tendsto_nhdsWithin_iff] at hxs_tendsto ⊢
    constructor
    · rw [tendsto_ofReal_iff]
      exact hxs_tendsto.1
    · simpa using hxs_tendsto.2

  change Set.EqOn F (Match.zeroFieldTreeSeries M) U
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hUpre hw₀U hcomplex

/-- The genuine zero-field tree EGF has a complex local continuation in
the normalized activity coordinate.  Its singular expansion is expressed
using the canonical Cartesian-Delta square root, so it can be fed directly
to the transfer layer. -/
theorem exists_zeroFieldTree_activity_singularity_data
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (C : ℂ) (E F : ℂ → ℂ) (r : ℝ),
      0 < r ∧
      AnalyticOnNhd ℂ E
        (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r) ∧
      AnalyticOnNhd ℂ F
        (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r) ∧
      Set.EqOn F (Match.zeroFieldTreeSeries M)
        (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) (r ^ 2)) ∧
      (∀ w ∈ TreeNormalizedFoldActivity.localCartesianDelta 1 0 r,
        F w = C - (1 - w) +
          (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
            Transfer.cartesianDeltaSqrt w ^ 3 +
          (1 - w) ^ 2 * E w) := by
  obtain ⟨U, R, rU, hrU, hU0, hUa, hRa, hUderiv, hUexp⟩ :=
    exists_normalized_zeroFieldTree_fold_expansion M hM
  obtain ⟨C, epsilon, hepsilon, hmatch⟩ :=
    Match.exists_positive_ray_treeSeries_eq_const_add_of_primitive
      M hM U hrU hUderiv
  obtain ⟨rR, hrR, hRball⟩ :=
    Metric.eventually_nhds_iff.mp hRa.eventually_analyticAt
  obtain ⟨rho, hrho, hUexpBall⟩ := Metric.mem_nhds_iff.mp hUexp
  let r : ℝ := min rU (min epsilon (min rR rho))
  have hr : 0 < r := lt_min hrU (lt_min hepsilon (lt_min hrR hrho))
  let E : ℂ → ℂ := fun w ↦ R (Transfer.cartesianDeltaSqrt w)
  let F : ℂ → ℂ := fun w ↦ C + U (Transfer.cartesianDeltaSqrt w)
  have hE : AnalyticOnNhd ℂ E
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r) := by
    intro w hw
    have hXanalytic : AnalyticAt ℂ Transfer.cartesianDeltaSqrt w :=
      Transfer.analyticOnNhd_cartesianDeltaSqrt (m := (0 : ℝ))
        (by norm_num) w hw.1
    have hXball : Transfer.cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) rR :=
      Metric.ball_subset_ball
        ((min_le_right rU (min epsilon (min rR rho))).trans
          ((min_le_right epsilon (min rR rho)).trans
            (min_le_left rR rho))) hw.2
    exact (hRball hXball).comp_of_eq hXanalytic rfl
  have hF : AnalyticOnNhd ℂ F
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r) := by
    intro w hw
    have hXanalytic : AnalyticAt ℂ Transfer.cartesianDeltaSqrt w :=
      Transfer.analyticOnNhd_cartesianDeltaSqrt (m := (0 : ℝ))
        (by norm_num) w hw.1
    have hXball : Transfer.cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) rU :=
      Metric.ball_subset_ball (min_le_left rU _) hw.2
    exact analyticAt_const.add ((hUa _ hXball).comp_of_eq hXanalytic rfl)
  have hphysical : ∀ X : ℝ, 0 < X → X < r →
      Match.zeroFieldTreeSeries M (((1 - X ^ 2 : ℝ) : ℂ)) =
        F (((1 - X ^ 2 : ℝ) : ℂ)) := by
    intro X hX0 hXr
    have hXepsilon : X < epsilon :=
      hXr.trans_le ((min_le_right rU _).trans (min_le_left epsilon _))
    have hsqrt : Transfer.cartesianDeltaSqrt
        (((1 - X ^ 2 : ℝ) : ℂ)) = (X : ℂ) := by
      rw [Transfer.cartesianDeltaSqrt]
      have hone : (1 : ℂ) - ((1 - X ^ 2 : ℝ) : ℂ) =
          ((X ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hone, Complex.sqrt_of_nonneg (by exact_mod_cast sq_nonneg X)]
      simp only [Complex.ofReal_re, Real.sqrt_sq_eq_abs, abs_of_pos hX0]
    dsimp only [F]
    rw [hsqrt]
    exact hmatch X hX0 hXepsilon
  have hLens := localContinuation_eq_zeroFieldTreeSeries_on_lens
    M hr hF hphysical
  refine ⟨C, E, F, r, hr, hE, hF, hLens, ?_⟩
  intro w hw
  let X := Transfer.cartesianDeltaSqrt w
  have hXrho : ‖X‖ < rho := by
    have hXr : ‖X‖ < r := by
      have hright := hw.2
      change Transfer.cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) r at hright
      simpa only [X, Metric.mem_ball, dist_zero_right] using hright
    exact hXr.trans_le
      ((min_le_right rU (min epsilon (min rR rho))).trans
        ((min_le_right epsilon (min rR rho)).trans
          (min_le_right rR rho)))
  have hUX := hUexpBall (by
    simpa only [Metric.mem_ball, dist_zero_right] using hXrho)
  have hXsq : X ^ 2 = 1 - w := Transfer.cartesianDeltaSqrt_sq w
  have hXfour : X ^ 4 = (1 - w) ^ 2 := by
    rw [show X ^ 4 = (X ^ 2) ^ 2 by ring, hXsq]
  change C + U X = C - (1 - w) +
    (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) * X ^ 3 +
      (1 - w) ^ 2 * R X
  rw [hUX, hXsq, hXfour]
  ring

end PerronWright.ZeroFieldTreeDeltaContinuation
