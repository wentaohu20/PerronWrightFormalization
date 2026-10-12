import PerronWright.Analysis.RootedTreeUnitJointField
import PerronWright.Analysis.RootedTreeClosedDiskGerm

/-!
# A finite joint rooted-tree atlas on compact noncritical closed-disk sets

The local input is the closed-disk joint germ box.  Compactness supplies a
finite subcover and hence one common field radius.  The overlap theorem is
already independent of the unit-circle hypothesis; the only geometric input
needed here is that intersecting half-radius balls with centres in the closed
unit disk have an open-unit-disk point in the corresponding full balls.
-/

open Filter
open scoped Classical Topology

noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem exists_openUnit_mem_full_balls_of_half_balls_inter_closedDisk
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

/-- A compact subset of the closed unit disk avoiding `1` admits a finite
joint atlas with one common field radius.  Intersecting selected half-radius
balls have compatible profiles on the full joint overlap. -/
theorem CompactBJRModel.exists_finite_rootedTreeSeries_closedDisk_joint_atlas
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {K : Set ℂ} (hK : IsCompact K)
    (hKdisk : K ⊆ Metric.closedBall (0 : ℂ) 1)
    (hnotone : (1 : ℂ) ∉ K) :
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
  have hnorm (a : K) : ‖(a : ℂ)‖ ≤ 1 := by
    have ha := hKdisk a.property
    simpa only [Metric.mem_closedBall, dist_zero_right] using ha
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
    exact M.exists_rootedTreeSeries_closedDisk_joint_germ_box hM
      (hnorm a) (fun ha => hnotone (ha ▸ a.property))
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
    (fun a : K ↦ Metric.ball (a : ℂ) (radius a / 2))
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
      exists_openUnit_mem_full_balls_of_half_balls_inter_closedDisk
        (hnorm a) (hnorm b) (hr a) (hr b) hinter
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

end PerronWright
