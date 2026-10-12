import PerronWright.Analysis.RootedTreeUnitGermBall

/-!
# Finite compatible atlases for noncritical unit-circle tree continuations

This scratch file turns the pointwise analytic germs into a finite atlas on
an arbitrary compact subset of the unit circle avoiding `1`.  We deliberately
use balls of half the analytic radius for the cover.  If two such cover balls
meet, a small geometric argument produces a point of the open unit disk in
the intersection of the two full analytic balls; the identity principle from
`RootedTreeUnitGermBall` then proves compatibility on the whole full overlap.
-/

open Filter
open scoped Classical Topology
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Two half-radius balls centred on the closed unit ball which meet have a
point of the open unit ball in the intersection of the corresponding
full-radius balls.  This is the elementary geometric input needed to compare
two boundary analytic germs through their common interior Taylor sum. -/
private theorem exists_openUnit_mem_full_balls_of_half_balls_inter
    {z₁ z₂ : ℂ} {r₁ r₂ : ℝ}
    (hz₁ : ‖z₁‖ ≤ 1) (hz₂ : ‖z₂‖ ≤ 1)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hinter : (Metric.ball z₁ (r₁ / 2) ∩
      Metric.ball z₂ (r₂ / 2)).Nonempty) :
    ∃ w : ℂ, w ∈ Metric.ball z₁ r₁ ∧
      w ∈ Metric.ball z₂ r₂ ∧ ‖w‖ < 1 := by
  obtain ⟨v, hv₁, hv₂⟩ := hinter
  have hrs : 0 < r₁ + r₂ := add_pos hr₁ hr₂
  have hzdist : dist z₁ z₂ < (r₁ + r₂) / 2 := by
    calc
      dist z₁ z₂ ≤ dist z₁ v + dist v z₂ := dist_triangle _ _ _
      _ < r₁ / 2 + r₂ / 2 :=
        add_lt_add
          (by simpa only [Metric.mem_ball, dist_comm] using hv₁)
          (by simpa only [Metric.mem_ball] using hv₂)
      _ = (r₁ + r₂) / 2 := by ring
  let t : ℝ := r₁ / (r₁ + r₂)
  let p : ℂ := AffineMap.lineMap z₁ z₂ t
  have ht0 : 0 ≤ t := (div_nonneg hr₁.le hrs.le)
  have ht1 : t ≤ 1 := by
    rw [div_le_one hrs]
    linarith
  have hpNorm : ‖p‖ ≤ 1 := by
    have hz₁ball : z₁ ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz₁
    have hz₂ball : z₂ ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz₂
    have hpball : p ∈ Metric.closedBall (0 : ℂ) 1 :=
      (convex_closedBall (0 : ℂ) 1).lineMap_mem hz₁ball hz₂ball ⟨ht0, ht1⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hpball
  have htNorm : ‖t‖ = t := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]
  have hOneSubT : 1 - t = r₂ / (r₁ + r₂) := by
    dsimp [t]
    field_simp [ne_of_gt hrs]
    ring
  have hOneSubT0 : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hOneSubTNorm : ‖1 - t‖ = 1 - t := by
    rw [Real.norm_eq_abs, abs_of_nonneg hOneSubT0]
  have hpz₁ : dist p z₁ < r₁ / 2 := by
    rw [show p = AffineMap.lineMap z₁ z₂ t from rfl,
      dist_lineMap_left, htNorm]
    calc
      t * dist z₁ z₂ < t * ((r₁ + r₂) / 2) :=
        mul_lt_mul_of_pos_left hzdist (div_pos hr₁ hrs)
      _ = r₁ / 2 := by
        dsimp [t]
        field_simp [ne_of_gt hrs]
  have hpz₂ : dist p z₂ < r₂ / 2 := by
    rw [show p = AffineMap.lineMap z₁ z₂ t from rfl,
      dist_lineMap_right, hOneSubTNorm, hOneSubT]
    calc
      r₂ / (r₁ + r₂) * dist z₁ z₂ <
          r₂ / (r₁ + r₂) * ((r₁ + r₂) / 2) :=
        mul_lt_mul_of_pos_left hzdist (div_pos hr₂ hrs)
      _ = r₂ / 2 := by
        field_simp [ne_of_gt hrs]
  let ε : ℝ := min (1 / 2) (min (r₁ / 4) (r₂ / 4))
  have hε0 : 0 < ε := by
    dsimp [ε]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hεr₁ : ε < r₁ / 2 :=
    (le_trans (min_le_right _ _) (min_le_left _ _)).trans_lt (by linarith)
  have hεr₂ : ε < r₂ / 2 :=
    (le_trans (min_le_right _ _) (min_le_right _ _)).trans_lt (by linarith)
  let w : ℂ := AffineMap.lineMap (0 : ℂ) p (1 - ε)
  have hscale0 : 0 ≤ 1 - ε := sub_nonneg.mpr hε1.le
  have hscaleNorm : ‖1 - ε‖ = 1 - ε := by
    rw [Real.norm_eq_abs, abs_of_nonneg hscale0]
  have hmove : dist w p ≤ ε := by
    rw [show w = AffineMap.lineMap (0 : ℂ) p (1 - ε) from rfl,
      dist_lineMap_right]
    simp only [sub_sub_cancel, Real.norm_eq_abs, abs_of_pos hε0, dist_zero_left]
    exact mul_le_of_le_one_right hε0.le hpNorm
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [Metric.mem_ball]
    calc
      dist w z₁ ≤ dist w p + dist p z₁ := dist_triangle _ _ _
      _ < ε + r₁ / 2 := add_lt_add_of_le_of_lt hmove hpz₁
      _ < r₁ := by linarith
  · rw [Metric.mem_ball]
    calc
      dist w z₂ ≤ dist w p + dist p z₂ := dist_triangle _ _ _
      _ < ε + r₂ / 2 := add_lt_add_of_le_of_lt hmove hpz₂
      _ < r₂ := by linarith
  · rw [show w = AffineMap.lineMap (0 : ℂ) p (1 - ε) from rfl,
      ← dist_zero_right, dist_lineMap_left, hscaleNorm, dist_zero_left]
    calc
      (1 - ε) * ‖p‖ ≤ (1 - ε) * 1 :=
        mul_le_mul_of_nonneg_left hpNorm hscale0
      _ < 1 := by simpa using sub_lt_self (1 : ℝ) hε0

/-- A compact subset of the noncritical unit circle admits a finite atlas of
genuine analytic rooted-tree continuations.  The half-radius balls cover the
compact set.  Whenever two such cover balls meet, their profiles agree on
the entire overlap of the corresponding full analytic balls. -/
theorem CompactBJRModel.exists_finite_rootedTreeSeries_unit_germ_atlas
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {K : Set ℂ} (hK : IsCompact K)
    (hunit : ∀ z ∈ K, ‖z‖ = 1) (hnotone : (1 : ℂ) ∉ K) :
    ∃ (profile : K → (ℂ × C(S, ℂ) → C(S, ℂ)))
        (radius : K → ℝ) (F : Finset K),
      (∀ a : K, 0 < radius a) ∧
      (∀ a : K, profile a (a, 0) = M.rootedTreeSeries a) ∧
      (∀ a : K, ∀ w ∈ Metric.ball (a : ℂ) (radius a),
        AnalyticAt ℂ (fun u : ℂ => profile a (u, 0)) w) ∧
      (∀ a : K, ∀ w ∈ Metric.ball (a : ℂ) (radius a),
        TreeCritical.residual M ((w, 0), profile a (w, 0)) = 0) ∧
      (∀ a : K, ∀ w ∈ Metric.ball (a : ℂ) (radius a), ‖w‖ < 1 →
        profile a (w, 0) = M.rootedTreeSeries w) ∧
      K ⊆ ⋃ a ∈ F, Metric.ball (a : ℂ) (radius a / 2) ∧
      ∀ a ∈ F, ∀ b ∈ F,
        (Metric.ball (a : ℂ) (radius a / 2) ∩
          Metric.ball (b : ℂ) (radius b / 2)).Nonempty →
        Set.EqOn (fun w : ℂ => profile a (w, 0))
          (fun w : ℂ => profile b (w, 0))
          (Metric.ball (a : ℂ) (radius a) ∩
            Metric.ball (b : ℂ) (radius b)) := by
  have hlocal (a : K) :
      ∃ (ψ : ℂ × C(S, ℂ) → C(S, ℂ)) (r : ℝ),
        0 < r ∧
        ψ (a, 0) = M.rootedTreeSeries a ∧
        (∀ w ∈ Metric.ball (a : ℂ) r,
          AnalyticAt ℂ (fun u : ℂ => ψ (u, 0)) w) ∧
        (∀ w ∈ Metric.ball (a : ℂ) r,
          TreeCritical.residual M ((w, 0), ψ (w, 0)) = 0) ∧
        ∀ w ∈ Metric.ball (a : ℂ) r, ‖w‖ < 1 →
          ψ (w, 0) = M.rootedTreeSeries w := by
    exact M.exists_rootedTreeSeries_unit_germ_ball hM
      (hunit a a.property) (fun ha => hnotone (ha ▸ a.property))
  choose profile radius hr hcenter han hres hinside using hlocal
  have hcover : K ⊆ ⋃ a : K,
      Metric.ball (a : ℂ) (radius a / 2) := by
    intro z hz
    let a : K := ⟨z, hz⟩
    apply Set.mem_iUnion.mpr
    refine ⟨a, ?_⟩
    rw [Metric.mem_ball, dist_self]
    exact half_pos (hr a)
  obtain ⟨F, hFcover⟩ := hK.elim_finite_subcover
    (fun a : K => Metric.ball (a : ℂ) (radius a / 2))
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨profile, radius, F, hr, hcenter, han, hres, hinside, hFcover, ?_⟩
  intro a ha b hb hinter
  obtain ⟨w₀, hw₀a, hw₀b, hw₀I⟩ :=
    exists_openUnit_mem_full_balls_of_half_balls_inter
      (hunit a a.property).le (hunit b b.property).le
      (hr a) (hr b) hinter
  exact M.rootedTreeSeries_unit_germ_balls_agree_on_overlap
    (a : ℂ) (b : ℂ) (radius a) (radius b)
    (profile a) (profile b) (han a) (han b)
    (hinside a) (hinside b) hw₀a hw₀b hw₀I

/-- The compatible finite atlas glues to a single analytic continuation on
an open neighborhood of the prescribed compact subset of the noncritical
unit circle.  The resulting function still solves the genuine tree equation
and restricts to the actual rooted-tree Taylor sum wherever this neighborhood
meets the open unit disk. -/
theorem CompactBJRModel.exists_rootedTreeSeries_analytic_continuation_near_compact_unit
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {K : Set ℂ} (hK : IsCompact K)
    (hunit : ∀ z ∈ K, ‖z‖ = 1) (hnotone : (1 : ℂ) ∉ K) :
    ∃ (U : Set ℂ) (T : ℂ → C(S, ℂ)),
      IsOpen U ∧ K ⊆ U ∧ AnalyticOnNhd ℂ T U ∧
      (∀ w ∈ U, TreeCritical.residual M ((w, 0), T w) = 0) ∧
      ∀ w ∈ U, ‖w‖ < 1 → T w = M.rootedTreeSeries w := by
  obtain ⟨profile, radius, F, hr, -, han, hres, hinside,
    hcover, hcompat⟩ :=
    M.exists_finite_rootedTreeSeries_unit_germ_atlas hM hK hunit hnotone
  let U : Set ℂ := ⋃ a ∈ F, Metric.ball (a : ℂ) (radius a / 2)
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_biUnion fun a _ => Metric.isOpen_ball
  have hchoose (w : ℂ) (hw : w ∈ U) :
      ∃ a : K, a ∈ F ∧ w ∈ Metric.ball (a : ℂ) (radius a / 2) := by
    simpa only [U, Set.mem_iUnion, exists_prop] using hw
  let pick (w : ℂ) (hw : w ∈ U) : K := Classical.choose (hchoose w hw)
  have hpickF (w : ℂ) (hw : w ∈ U) : pick w hw ∈ F :=
    (Classical.choose_spec (hchoose w hw)).1
  have hpickBall (w : ℂ) (hw : w ∈ U) :
      w ∈ Metric.ball ((pick w hw : K) : ℂ) (radius (pick w hw) / 2) :=
    (Classical.choose_spec (hchoose w hw)).2
  let T : ℂ → C(S, ℂ) := fun w =>
    if hw : w ∈ U then profile (pick w hw) (w, 0) else 0
  have hhalf_full (a : K) :
      Metric.ball (a : ℂ) (radius a / 2) ⊆
        Metric.ball (a : ℂ) (radius a) :=
    Metric.ball_subset_ball (by linarith [hr a])
  have hT_eq_chart (a : K) (haF : a ∈ F) (w : ℂ)
      (hwa : w ∈ Metric.ball (a : ℂ) (radius a / 2)) :
      T w = profile a (w, 0) := by
    have hwU : w ∈ U := by
      dsimp [U]
      exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨haF, hwa⟩⟩
    rw [show T w = profile (pick w hwU) (w, 0) by simp [T, hwU]]
    let b : K := pick w hwU
    have hbF : b ∈ F := hpickF w hwU
    have hwb : w ∈ Metric.ball (b : ℂ) (radius b / 2) := hpickBall w hwU
    have hinter : (Metric.ball (b : ℂ) (radius b / 2) ∩
        Metric.ball (a : ℂ) (radius a / 2)).Nonempty :=
      ⟨w, hwb, hwa⟩
    have heq := hcompat b hbF a haF hinter
    exact heq ⟨hhalf_full b hwb, hhalf_full a hwa⟩
  refine ⟨U, T, hUopen, hcover, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨a, haF, hwa⟩ := hchoose w hw
    have hwaNhd : Metric.ball (a : ℂ) (radius a / 2) ∈ nhds w :=
      Metric.isOpen_ball.mem_nhds hwa
    have hlocalEq : T =ᶠ[nhds w] fun y : ℂ => profile a (y, 0) := by
      filter_upwards [hwaNhd] with y hya
      exact hT_eq_chart a haF y hya
    exact (han a w (hhalf_full a hwa)).congr hlocalEq.symm
  · intro w hw
    obtain ⟨a, haF, hwa⟩ := hchoose w hw
    rw [hT_eq_chart a haF w hwa]
    exact hres a w (hhalf_full a hwa)
  · intro w hw hwI
    obtain ⟨a, haF, hwa⟩ := hchoose w hw
    rw [hT_eq_chart a haF w hwa]
    exact hinside a w (hhalf_full a hwa) hwI

/-- In the form used by the later dented-domain construction: for every
positive angular cutoff, the whole part of the unit circle at distance at
least that cutoff from `1` has one genuine analytic tree continuation on an
open neighborhood. -/
theorem CompactBJRModel.exists_rootedTreeSeries_analytic_continuation_unit_away
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ (U : Set ℂ) (T : ℂ → C(S, ℂ)),
      IsOpen U ∧
      (Metric.sphere (0 : ℂ) 1 ∩
        {z : ℂ | delta ≤ dist z 1}) ⊆ U ∧
      AnalyticOnNhd ℂ T U ∧
      (∀ w ∈ U, TreeCritical.residual M ((w, 0), T w) = 0) ∧
      ∀ w ∈ U, ‖w‖ < 1 → T w = M.rootedTreeSeries w := by
  let K : Set ℂ := Metric.sphere (0 : ℂ) 1 ∩
    {z : ℂ | delta ≤ dist z 1}
  have haway : IsClosed {z : ℂ | delta ≤ dist z 1} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hK : IsCompact K :=
    (isCompact_sphere (0 : ℂ) 1).inter_right haway
  have hunit : ∀ z ∈ K, ‖z‖ = 1 := by
    intro z hz
    simpa only [Metric.mem_sphere, dist_zero_right] using hz.1
  have hnotone : (1 : ℂ) ∉ K := by
    intro hone
    have hawayOne := hone.2
    change delta ≤ dist (1 : ℂ) 1 at hawayOne
    rw [dist_self] at hawayOne
    exact (not_le_of_gt hdelta) hawayOne
  simpa only [K] using
    M.exists_rootedTreeSeries_analytic_continuation_near_compact_unit
      hM hK hunit hnotone

end PerronWright
