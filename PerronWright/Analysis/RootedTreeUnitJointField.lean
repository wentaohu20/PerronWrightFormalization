import PerronWright.Analysis.RootedTreeUnitFiniteCover

/-!
# A field-uniform joint atlas near noncritical unit-circle sets

Its overlap argument does **not** infer joint equality from equality on
`g = 0`.  The zero-field
equality is used only to identify one common solution.  The implicit-function
uniqueness neighborhood is then pulled back along the second graph to obtain
equality on a genuinely open joint neighborhood; higher-dimensional analytic
uniqueness propagates that equality across the connected product overlap.
-/

open Filter
open scoped Classical Topology
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- A noncritical unit-circle germ can be shrunk to a genuine joint product
box.  In addition to analyticity and the tree equation, every point of its
zero-field spine retains the local uniqueness conclusion of the implicit
function theorem. -/
theorem CompactBJRModel.exists_rootedTreeSeries_unit_joint_germ_box
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ (ψ : ℂ × C(S, ℂ) → C(S, ℂ)) (r : ℝ),
      0 < r ∧
      ψ (z, 0) = M.rootedTreeSeries z ∧
      (∀ q ∈ Metric.ball z r ×ˢ Metric.ball (0 : C(S, ℂ)) r,
        AnalyticAt ℂ ψ q) ∧
      (∀ q ∈ Metric.ball z r ×ˢ Metric.ball (0 : C(S, ℂ)) r,
        TreeCritical.residual M (q, ψ q) = 0) ∧
      (∀ w ∈ Metric.ball z r, ‖w‖ < 1 →
        ψ (w, 0) = M.rootedTreeSeries w) ∧
      ∀ w ∈ Metric.ball z r,
        ∀ᶠ p in nhds ((w, (0 : C(S, ℂ))), ψ (w, 0)),
          TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2 := by
  obtain ⟨ψ, hψa, hψz, hψres, hψuniq, hglue⟩ :=
    M.exists_rootedTreeSeries_unit_germ_glued hM hz hz1
  have hjoint : ∀ᶠ q in nhds (z, (0 : C(S, ℂ))),
      AnalyticAt ℂ ψ q ∧ TreeCritical.residual M (q, ψ q) = 0 :=
    hψa.eventually_analyticAt.and hψres
  obtain ⟨rJoint, hrJoint, hJointBall⟩ := Metric.mem_nhds_iff.mp hjoint

  let H : Set ((ℂ × C(S, ℂ)) × C(S, ℂ)) :=
    {p | TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2}
  have hH : H ∈ nhds (((z, (0 : C(S, ℂ))), M.rootedTreeSeries z)) := by
    change ∀ᶠ p in nhds (((z, (0 : C(S, ℂ))), M.rootedTreeSeries z)),
      TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2
    exact hψuniq
  obtain ⟨δ, hδ, hδH⟩ := Metric.mem_nhds_iff.mp hH
  have hembA : AnalyticAt ℂ
      (fun w : ℂ => (w, (0 : C(S, ℂ)))) z :=
    analyticAt_id.prod analyticAt_const
  have hembT : Tendsto (fun w : ℂ => (w, (0 : C(S, ℂ))))
      (nhds z) (nhds (z, 0)) := hembA.continuousAt.tendsto
  have hψT : Tendsto (fun w : ℂ => ψ (w, 0)) (nhds z) (nhds (ψ (z, 0))) :=
    hψa.continuousAt.tendsto.comp hembT
  have hgraphT : Tendsto
      (fun w : ℂ => ((w, (0 : C(S, ℂ))), ψ (w, 0)))
      (nhds z) (nhds (((z, (0 : C(S, ℂ))), M.rootedTreeSeries z))) := by
    simpa only [hψz] using hembT.prodMk_nhds hψT
  have hgraphBall : ∀ᶠ w : ℂ in nhds z,
      ((w, (0 : C(S, ℂ))), ψ (w, 0)) ∈
        Metric.ball (((z, (0 : C(S, ℂ))), M.rootedTreeSeries z)) δ :=
    hgraphT.eventually
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
  have hspineUniq : ∀ᶠ w : ℂ in nhds z,
      ∀ᶠ p in nhds ((w, (0 : C(S, ℂ))), ψ (w, 0)),
        TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2 := by
    filter_upwards [hgraphBall] with w hw
    exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hw) hδH
  obtain ⟨rUniq, hrUniq, hUniqBall⟩ := Metric.mem_nhds_iff.mp hspineUniq

  have hglue' : (fun w : ℂ => ψ (w, 0)) =ᶠ[
      nhdsWithin z {w : ℂ | ‖w‖ < 1}] M.rootedTreeSeries := by
    simpa only [Function.comp_def] using hglue
  obtain ⟨rGlue, hrGlue, hGlueBall⟩ := Metric.mem_nhdsWithin_iff.mp hglue'

  let r : ℝ := min rJoint (min rUniq rGlue)
  have hr : 0 < r := lt_min hrJoint (lt_min hrUniq hrGlue)
  have hrJoint' : r ≤ rJoint := min_le_left _ _
  have hrUniq' : r ≤ rUniq :=
    (min_le_right rJoint (min rUniq rGlue)).trans (min_le_left _ _)
  have hrGlue' : r ≤ rGlue :=
    (min_le_right rJoint (min rUniq rGlue)).trans (min_le_right _ _)
  refine ⟨ψ, r, hr, hψz, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hq' : q ∈ Metric.ball (z, (0 : C(S, ℂ))) rJoint := by
      rw [← ball_prod_same]
      exact ⟨Metric.ball_subset_ball hrJoint' hq.1,
        Metric.ball_subset_ball hrJoint' hq.2⟩
    exact (hJointBall hq').1
  · intro q hq
    have hq' : q ∈ Metric.ball (z, (0 : C(S, ℂ))) rJoint := by
      rw [← ball_prod_same]
      exact ⟨Metric.ball_subset_ball hrJoint' hq.1,
        Metric.ball_subset_ball hrJoint' hq.2⟩
    exact (hJointBall hq').2
  · intro w hw hwI
    exact hGlueBall ⟨Metric.ball_subset_ball hrGlue' hw, hwI⟩
  · intro w hw
    exact hUniqBall (Metric.ball_subset_ball hrUniq' hw)

/-- Joint overlap uniqueness.  The hypotheses on the zero-field slice are
used only to identify the solution at `q₀ = (w₀,0)`.  The actual open-set
equality comes from `h₁uniq` and the residual equation for `ψ₂`. -/
theorem CompactBJRModel.rootedTreeSeries_unit_joint_germ_boxes_agree_on_overlap
    (M : CompactBJRModel S)
    (z₁ z₂ : ℂ) (r₁ r₂ ε : ℝ) (hε : 0 < ε)
    (ψ₁ ψ₂ : ℂ × C(S, ℂ) → C(S, ℂ))
    (h₁a : ∀ q ∈ Metric.ball z₁ r₁ ×ˢ Metric.ball (0 : C(S, ℂ)) ε,
      AnalyticAt ℂ ψ₁ q)
    (h₂a : ∀ q ∈ Metric.ball z₂ r₂ ×ˢ Metric.ball (0 : C(S, ℂ)) ε,
      AnalyticAt ℂ ψ₂ q)
    (h₂res : ∀ q ∈ Metric.ball z₂ r₂ ×ˢ Metric.ball (0 : C(S, ℂ)) ε,
      TreeCritical.residual M (q, ψ₂ q) = 0)
    (h₁eq : ∀ w ∈ Metric.ball z₁ r₁, ‖w‖ < 1 →
      ψ₁ (w, 0) = M.rootedTreeSeries w)
    (h₂eq : ∀ w ∈ Metric.ball z₂ r₂, ‖w‖ < 1 →
      ψ₂ (w, 0) = M.rootedTreeSeries w)
    (h₁uniq : ∀ w ∈ Metric.ball z₁ r₁,
      ∀ᶠ p in nhds ((w, (0 : C(S, ℂ))), ψ₁ (w, 0)),
        TreeCritical.residual M p = 0 ↔ ψ₁ p.1 = p.2)
    {w₀ : ℂ} (hw₀₁ : w₀ ∈ Metric.ball z₁ r₁)
    (hw₀₂ : w₀ ∈ Metric.ball z₂ r₂) (hw₀I : ‖w₀‖ < 1) :
    Set.EqOn ψ₁ ψ₂
      ((Metric.ball z₁ r₁ ×ˢ Metric.ball (0 : C(S, ℂ)) ε) ∩
        (Metric.ball z₂ r₂ ×ˢ Metric.ball (0 : C(S, ℂ)) ε)) := by
  let B₁ : Set (ℂ × C(S, ℂ)) :=
    Metric.ball z₁ r₁ ×ˢ Metric.ball (0 : C(S, ℂ)) ε
  let B₂ : Set (ℂ × C(S, ℂ)) :=
    Metric.ball z₂ r₂ ×ˢ Metric.ball (0 : C(S, ℂ)) ε
  let U : Set (ℂ × C(S, ℂ)) := B₁ ∩ B₂
  let q₀ : ℂ × C(S, ℂ) := (w₀, 0)
  have h0 : (0 : C(S, ℂ)) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
  have hq₀₁ : q₀ ∈ B₁ := ⟨hw₀₁, h0⟩
  have hq₀₂ : q₀ ∈ B₂ := ⟨hw₀₂, h0⟩
  have hseed : ψ₁ q₀ = ψ₂ q₀ := by
    exact (h₁eq w₀ hw₀₁ hw₀I).trans
      (h₂eq w₀ hw₀₂ hw₀I).symm
  have hgraph₂ : Tendsto (fun q => (q, ψ₂ q)) (nhds q₀)
      (nhds (q₀, ψ₁ q₀)) := by
    have hid : Tendsto (fun q : ℂ × C(S, ℂ) => q) (nhds q₀) (nhds q₀) :=
      tendsto_id
    have h := hid.prodMk_nhds (h₂a q₀ hq₀₂).continuousAt.tendsto
    simpa only [hseed] using h
  have heqNhd : ψ₁ =ᶠ[nhds q₀] ψ₂ := by
    have hB₂ : B₂ ∈ nhds q₀ :=
      (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hq₀₂
    filter_upwards [hgraph₂.eventually (h₁uniq w₀ hw₀₁), hB₂]
      with q huniq hq
    exact huniq.mp (h₂res q hq)
  have h₁an : AnalyticOnNhd ℂ ψ₁ U := by
    intro q hq
    exact h₁a q hq.1
  have h₂an : AnalyticOnNhd ℂ ψ₂ U := by
    intro q hq
    exact h₂a q hq.2
  have hUpre : IsPreconnected U := by
    exact (((convex_ball z₁ r₁).prod
      (convex_ball (0 : C(S, ℂ)) ε)).inter
      ((convex_ball z₂ r₂).prod
        (convex_ball (0 : C(S, ℂ)) ε))).isPreconnected
  have hq₀U : q₀ ∈ U := ⟨hq₀₁, hq₀₂⟩
  simpa only [U, B₁, B₂] using
    h₁an.eqOn_of_preconnected_of_eventuallyEq h₂an hUpre hq₀U heqNhd

/-- The geometric seed used for joint overlaps. -/
private theorem exists_openUnit_mem_full_balls_of_half_balls_inter_joint
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
  have ht0 : 0 ≤ t := div_nonneg hr₁.le hrs.le
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
  let η : ℝ := min (1 / 2) (min (r₁ / 4) (r₂ / 4))
  have hη0 : 0 < η := by
    dsimp [η]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hη1 : η < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hηr₁ : η < r₁ / 2 :=
    (le_trans (min_le_right _ _) (min_le_left _ _)).trans_lt (by linarith)
  have hηr₂ : η < r₂ / 2 :=
    (le_trans (min_le_right _ _) (min_le_right _ _)).trans_lt (by linarith)
  let w : ℂ := AffineMap.lineMap (0 : ℂ) p (1 - η)
  have hscale0 : 0 ≤ 1 - η := sub_nonneg.mpr hη1.le
  have hscaleNorm : ‖1 - η‖ = 1 - η := by
    rw [Real.norm_eq_abs, abs_of_nonneg hscale0]
  have hmove : dist w p ≤ η := by
    rw [show w = AffineMap.lineMap (0 : ℂ) p (1 - η) from rfl,
      dist_lineMap_right]
    simp only [sub_sub_cancel, Real.norm_eq_abs, abs_of_pos hη0, dist_zero_left]
    exact mul_le_of_le_one_right hη0.le hpNorm
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [Metric.mem_ball]
    calc
      dist w z₁ ≤ dist w p + dist p z₁ := dist_triangle _ _ _
      _ < η + r₁ / 2 := add_lt_add_of_le_of_lt hmove hpz₁
      _ < r₁ := by linarith
  · rw [Metric.mem_ball]
    calc
      dist w z₂ ≤ dist w p + dist p z₂ := dist_triangle _ _ _
      _ < η + r₂ / 2 := add_lt_add_of_le_of_lt hmove hpz₂
      _ < r₂ := by linarith
  · rw [show w = AffineMap.lineMap (0 : ℂ) p (1 - η) from rfl,
      ← dist_zero_right, dist_lineMap_left, hscaleNorm, dist_zero_left]
    calc
      (1 - η) * ‖p‖ ≤ (1 - η) * 1 :=
        mul_le_mul_of_nonneg_left hpNorm hscale0
      _ < 1 := by simpa using sub_lt_self (1 : ℝ) hη0

/-- A finite joint atlas with one field radius.  Only the finitely selected
charts are asserted on the common field ball; no lower bound over all of the
possibly infinite subtype `K` is needed.  Each selected chart retains its
implicit-function residual uniqueness along the full zero-field spine. -/
theorem CompactBJRModel.exists_finite_rootedTreeSeries_unit_joint_atlas
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {K : Set ℂ} (hK : IsCompact K)
    (hunit : ∀ z ∈ K, ‖z‖ = 1) (hnotone : (1 : ℂ) ∉ K) :
    ∃ (profile : K → (ℂ × C(S, ℂ) → C(S, ℂ)))
        (radius : K → ℝ) (ε : ℝ) (F : Finset K),
      0 < ε ∧
      (∀ a : K, 0 < radius a) ∧
      (∀ a : K, profile a (a, 0) = M.rootedTreeSeries a) ∧
      (∀ a ∈ F, ∀ q ∈
        Metric.ball (a : ℂ) (radius a) ×ˢ Metric.ball (0 : C(S, ℂ)) ε,
        AnalyticAt ℂ (profile a) q) ∧
      (∀ a ∈ F, ∀ q ∈
        Metric.ball (a : ℂ) (radius a) ×ˢ Metric.ball (0 : C(S, ℂ)) ε,
        TreeCritical.residual M (q, profile a q) = 0) ∧
      (∀ a : K, ∀ w ∈ Metric.ball (a : ℂ) (radius a), ‖w‖ < 1 →
        profile a (w, 0) = M.rootedTreeSeries w) ∧
      (∀ a ∈ F, ∀ w ∈ Metric.ball (a : ℂ) (radius a),
        ∀ᶠ p in nhds ((w, (0 : C(S, ℂ))), profile a (w, 0)),
          TreeCritical.residual M p = 0 ↔ profile a p.1 = p.2) ∧
      K ⊆ ⋃ a ∈ F, Metric.ball (a : ℂ) (radius a / 2) ∧
      ∀ a ∈ F, ∀ b ∈ F,
        (Metric.ball (a : ℂ) (radius a / 2) ∩
          Metric.ball (b : ℂ) (radius b / 2)).Nonempty →
        Set.EqOn (profile a) (profile b)
          ((Metric.ball (a : ℂ) (radius a) ×ˢ
              Metric.ball (0 : C(S, ℂ)) ε) ∩
            (Metric.ball (b : ℂ) (radius b) ×ˢ
              Metric.ball (0 : C(S, ℂ)) ε)) := by
  have hlocal (a : K) :
      ∃ (ψ : ℂ × C(S, ℂ) → C(S, ℂ)) (r : ℝ),
        0 < r ∧
        ψ (a, 0) = M.rootedTreeSeries a ∧
        (∀ q ∈ Metric.ball (a : ℂ) r ×ˢ Metric.ball (0 : C(S, ℂ)) r,
          AnalyticAt ℂ ψ q) ∧
        (∀ q ∈ Metric.ball (a : ℂ) r ×ˢ Metric.ball (0 : C(S, ℂ)) r,
          TreeCritical.residual M (q, ψ q) = 0) ∧
        (∀ w ∈ Metric.ball (a : ℂ) r, ‖w‖ < 1 →
          ψ (w, 0) = M.rootedTreeSeries w) ∧
        ∀ w ∈ Metric.ball (a : ℂ) r,
          ∀ᶠ p in nhds ((w, (0 : C(S, ℂ))), ψ (w, 0)),
            TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2 := by
    exact M.exists_rootedTreeSeries_unit_joint_germ_box hM
      (hunit a a.property) (fun ha => hnotone (ha ▸ a.property))
  choose profile radius hr hcenter han hres hinside huniq using hlocal
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
  let ε : ℝ := if hF : F.Nonempty then F.inf' hF radius else 1
  have hε : 0 < ε := by
    dsimp [ε]
    split_ifs with hF
    · exact (Finset.lt_inf'_iff hF).2 fun a _ => hr a
    · norm_num
  have hεle (a : K) (ha : a ∈ F) : ε ≤ radius a := by
    dsimp [ε]
    split_ifs with hF
    · exact Finset.inf'_le radius ha
    · exact False.elim (hF ⟨a, ha⟩)
  refine ⟨profile, radius, ε, F, hε, hr, hcenter, ?_, ?_, hinside,
    (fun a _ => huniq a), hFcover, ?_⟩
  · intro a ha q hq
    exact han a q ⟨hq.1, Metric.ball_subset_ball (hεle a ha) hq.2⟩
  · intro a ha q hq
    exact hres a q ⟨hq.1, Metric.ball_subset_ball (hεle a ha) hq.2⟩
  · intro a ha b hb hinter
    obtain ⟨w₀, hw₀a, hw₀b, hw₀I⟩ :=
      exists_openUnit_mem_full_balls_of_half_balls_inter_joint
        (hunit a a.property).le (hunit b b.property).le
        (hr a) (hr b) hinter
    exact M.rootedTreeSeries_unit_joint_germ_boxes_agree_on_overlap
      (a : ℂ) (b : ℂ) (radius a) (radius b) ε hε
      (profile a) (profile b)
      (fun q hq => han a q ⟨hq.1,
        Metric.ball_subset_ball (hεle a ha) hq.2⟩)
      (fun q hq => han b q ⟨hq.1,
        Metric.ball_subset_ball (hεle b hb) hq.2⟩)
      (fun q hq => hres b q ⟨hq.1,
        Metric.ball_subset_ball (hεle b hb) hq.2⟩)
      (hinside a) (hinside b) (huniq a)
      hw₀a hw₀b hw₀I

/-- The finite joint atlas glues to one jointly analytic solution on an
explicit product `U × ball 0 ε`, retaining local residual uniqueness at every
point of its zero-field spine. -/
theorem CompactBJRModel.exists_rootedTreeSeries_joint_analytic_continuation_near_compact_unit
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {K : Set ℂ} (hK : IsCompact K)
    (hunit : ∀ z ∈ K, ‖z‖ = 1) (hnotone : (1 : ℂ) ∉ K) :
    ∃ (U : Set ℂ) (ε : ℝ) (Ψ : ℂ × C(S, ℂ) → C(S, ℂ)),
      IsOpen U ∧ K ⊆ U ∧ 0 < ε ∧
      AnalyticOnNhd ℂ Ψ (U ×ˢ Metric.ball (0 : C(S, ℂ)) ε) ∧
      (∀ q ∈ U ×ˢ Metric.ball (0 : C(S, ℂ)) ε,
        TreeCritical.residual M (q, Ψ q) = 0) ∧
      (∀ w ∈ U, ‖w‖ < 1 → Ψ (w, 0) = M.rootedTreeSeries w) ∧
      ∀ w ∈ U,
        ∀ᶠ p in nhds ((w, (0 : C(S, ℂ))), Ψ (w, 0)),
          TreeCritical.residual M p = 0 ↔ Ψ p.1 = p.2 := by
  obtain ⟨profile, radius, ε, F, hε, hr, -, han, hres, hinside,
    huniq, hcover, hcompat⟩ :=
    M.exists_finite_rootedTreeSeries_unit_joint_atlas hM hK hunit hnotone
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
  let W : Set (ℂ × C(S, ℂ)) :=
    U ×ˢ Metric.ball (0 : C(S, ℂ)) ε
  let Ψ : ℂ × C(S, ℂ) → C(S, ℂ) := fun q =>
    if hq : q ∈ W then profile (pick q.1 hq.1) q else 0
  have hhalf_full (a : K) :
      Metric.ball (a : ℂ) (radius a / 2) ⊆
        Metric.ball (a : ℂ) (radius a) :=
    Metric.ball_subset_ball (by linarith [hr a])
  have hΨ_eq_chart (a : K) (haF : a ∈ F) (q : ℂ × C(S, ℂ))
      (hqa : q ∈ Metric.ball (a : ℂ) (radius a / 2) ×ˢ
        Metric.ball (0 : C(S, ℂ)) ε) :
      Ψ q = profile a q := by
    have hqU : q.1 ∈ U := by
      dsimp [U]
      exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨haF, hqa.1⟩⟩
    have hqW : q ∈ W := ⟨hqU, hqa.2⟩
    rw [show Ψ q = profile (pick q.1 hqU) q by simp [Ψ, hqW]]
    let b : K := pick q.1 hqU
    have hbF : b ∈ F := hpickF q.1 hqU
    have hqb : q.1 ∈ Metric.ball (b : ℂ) (radius b / 2) :=
      hpickBall q.1 hqU
    have hinter : (Metric.ball (b : ℂ) (radius b / 2) ∩
        Metric.ball (a : ℂ) (radius a / 2)).Nonempty :=
      ⟨q.1, hqb, hqa.1⟩
    have heq := hcompat b hbF a haF hinter
    exact heq ⟨⟨hhalf_full b hqb, hqa.2⟩,
      ⟨hhalf_full a hqa.1, hqa.2⟩⟩
  refine ⟨U, ε, Ψ, hUopen, hcover, hε, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨a, haF, hqa⟩ := hchoose q.1 hq.1
    have hlocalMem : q ∈ Metric.ball (a : ℂ) (radius a / 2) ×ˢ
        Metric.ball (0 : C(S, ℂ)) ε := ⟨hqa, hq.2⟩
    have hlocalNhd :
        Metric.ball (a : ℂ) (radius a / 2) ×ˢ
          Metric.ball (0 : C(S, ℂ)) ε ∈ nhds q :=
      (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hlocalMem
    have hlocalEq : Ψ =ᶠ[nhds q] profile a := by
      filter_upwards [hlocalNhd] with y hy
      exact hΨ_eq_chart a haF y hy
    exact (han a haF q ⟨hhalf_full a hqa, hq.2⟩).congr hlocalEq.symm
  · intro q hq
    obtain ⟨a, haF, hqa⟩ := hchoose q.1 hq.1
    rw [hΨ_eq_chart a haF q ⟨hqa, hq.2⟩]
    exact hres a haF q ⟨hhalf_full a hqa, hq.2⟩
  · intro w hw hwI
    obtain ⟨a, haF, hwa⟩ := hchoose w hw
    have h0 : (0 : C(S, ℂ)) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
    rw [hΨ_eq_chart a haF (w, 0) ⟨hwa, h0⟩]
    exact hinside a w (hhalf_full a hwa) hwI
  · intro w hw
    obtain ⟨a, haF, hwa⟩ := hchoose w hw
    have h0 : (0 : C(S, ℂ)) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
    have hlocalMem : (w, (0 : C(S, ℂ))) ∈
        Metric.ball (a : ℂ) (radius a / 2) ×ˢ
          Metric.ball (0 : C(S, ℂ)) ε := ⟨hwa, h0⟩
    have hlocalNhd :
        Metric.ball (a : ℂ) (radius a / 2) ×ˢ
          Metric.ball (0 : C(S, ℂ)) ε ∈ nhds (w, (0 : C(S, ℂ))) :=
      (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hlocalMem
    have hlocalEq : Ψ =ᶠ[nhds (w, (0 : C(S, ℂ)))] profile a := by
      filter_upwards [hlocalNhd] with y hy
      exact hΨ_eq_chart a haF y hy
    have hbase : Ψ (w, 0) = profile a (w, 0) :=
      hΨ_eq_chart a haF (w, 0) hlocalMem
    rw [hbase]
    have hfst : Tendsto
        (fun p : ((ℂ × C(S, ℂ)) × C(S, ℂ)) => p.1)
        (nhds (((w, (0 : C(S, ℂ))), profile a (w, 0))))
        (nhds (w, (0 : C(S, ℂ)))) := continuousAt_fst
    filter_upwards [huniq a haF w (hhalf_full a hwa),
      hfst.eventually hlocalEq] with p hp heq
    rw [heq]
    exact hp

/-- Field-uniform form for the full unit-circle arc separated from `1` by a
positive metric cutoff, including the inherited zero-field local uniqueness. -/
theorem CompactBJRModel.exists_rootedTreeSeries_joint_analytic_continuation_unit_away
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ (U : Set ℂ) (ε : ℝ) (Ψ : ℂ × C(S, ℂ) → C(S, ℂ)),
      IsOpen U ∧
      (Metric.sphere (0 : ℂ) 1 ∩
        {z : ℂ | delta ≤ dist z 1}) ⊆ U ∧
      0 < ε ∧
      AnalyticOnNhd ℂ Ψ (U ×ˢ Metric.ball (0 : C(S, ℂ)) ε) ∧
      (∀ q ∈ U ×ˢ Metric.ball (0 : C(S, ℂ)) ε,
        TreeCritical.residual M (q, Ψ q) = 0) ∧
      (∀ w ∈ U, ‖w‖ < 1 → Ψ (w, 0) = M.rootedTreeSeries w) ∧
      ∀ w ∈ U,
        ∀ᶠ p in nhds ((w, (0 : C(S, ℂ))), Ψ (w, 0)),
          TreeCritical.residual M p = 0 ↔ Ψ p.1 = p.2 := by
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
    M.exists_rootedTreeSeries_joint_analytic_continuation_near_compact_unit
      hM hK hunit hnotone

end PerronWright
