import PerronWright.Probability.BrownianPositiveBridgeAreaMomentBounds

/-! # Uniform tail control for the actual positive-bridge area powers

One further genuine moment controls every truncated moment.  The final
epsilon/delta statement is uniform over all sufficiently small positive
endpoints, with no uniform-integrability premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeAreaMomentTails

open BrownianPathLaw BrownianBridgeCyclicArea BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeAreaMomentBounds

theorem measurableSet_area_tail (T : ℝ≥0) (B : ℝ) :
    MeasurableSet {g : Path | B ≤ |pathArea T g|} :=
  measurableSet_le measurable_const (measurable_pathArea T).abs

theorem area_tail_power_le_succ (T : ℝ≥0) (n : ℕ) {B : ℝ} (hB : 0 < B)
    (g : Path) (hg : B ≤ |pathArea T g|) :
    ENNReal.ofReal (|pathArea T g|^n) ≤
      ENNReal.ofReal (|pathArea T g|^(n+1))/ENNReal.ofReal B := by
  rw [← ENNReal.ofReal_div_of_pos hB]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ hB).mpr
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_left hg (by positivity)

theorem eventually_area_tail_moment_bound (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ B : ℝ, 0 < B →
      (∫⁻ g : Path in {g : Path | B ≤ |pathArea T g|}, ENNReal.ofReal (|pathArea T g|^n)
        ∂positiveBridgeLaw a T) ≤ areaBound T (n+1)/ENNReal.ofReal B := by
  filter_upwards [eventually_area_moment_bound T hT (n+1)] with a hb
  intro B hB
  calc
    _ ≤ ∫⁻ g : Path in {g : Path | B ≤ |pathArea T g|},
        ENNReal.ofReal (|pathArea T g|^(n+1))/ENNReal.ofReal B ∂positiveBridgeLaw a T := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_area_tail T B)] with g hg
      exact area_tail_power_le_succ T n hB g hg
    _ ≤ ∫⁻ g : Path, ENNReal.ofReal (|pathArea T g|^(n+1))/ENNReal.ofReal B ∂positiveBridgeLaw a T :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = (∫⁻ g : Path, ENNReal.ofReal (|pathArea T g|^(n+1)) ∂positiveBridgeLaw a T)/ENNReal.ofReal B := by
      simp only [div_eq_mul_inv]
      rw [lintegral_mul_const _ (((measurable_pathArea T).abs.pow_const (n+1)).ennreal_ofReal)]
    _ ≤ _ := ENNReal.div_le_div_right hb _

theorem area_moment_tails_uniformly_vanish (T : ℝ≥0) (hT : 0 < T) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℝ, 0 < B ∧ ∀ a : ℝ, 0 < a → a < δ →
      (∫⁻ g : Path in {g : Path | B ≤ |pathArea T g|}, ENNReal.ofReal (|pathArea T g|^n)
        ∂positiveBridgeLaw a T) ≤ ENNReal.ofReal ε := by
  obtain ⟨δ,hδ,hh⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (eventually_area_tail_moment_bound T hT n)
  let C : ℝ := (areaBound T (n+1)).toReal
  let B : ℝ := C/ε+1
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hB : 0 < B := by dsimp [B]; positivity
  have hratio : C/B ≤ ε := by
    apply (div_le_iff₀ hB).mpr
    dsimp [B]
    rw [mul_add,mul_div_cancel₀ _ hε.ne',mul_one]
    exact le_add_of_nonneg_right hε.le
  have hENN : areaBound T (n+1)/ENNReal.ofReal B ≤ ENNReal.ofReal ε := by
    have he : areaBound T (n+1) = ENNReal.ofReal C :=
      (ENNReal.ofReal_toReal (areaBound_lt_top T hT (n+1)).ne).symm
    rw [he,← ENNReal.ofReal_div_of_pos hB]
    exact ENNReal.ofReal_le_ofReal hratio
  refine ⟨δ,hδ,B,hB,?_⟩
  intro a ha haδ
  exact (hh ⟨ha,haδ⟩ B hB).trans hENN

theorem area_real_moment_tails_uniformly_vanish (T : ℝ≥0) (hT : 0 < T) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℝ, 0 < B ∧ ∀ a : ℝ, 0 < a → a < δ →
      (∫ g : Path in {g : Path | B ≤ |pathArea T g|}, |pathArea T g|^n
        ∂positiveBridgeLaw a T) ≤ ε := by
  obtain ⟨δ,hδ,B,hB,hh⟩ := area_moment_tails_uniformly_vanish T hT n hε
  refine ⟨δ,hδ,B,hB,?_⟩
  intro a ha haδ
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ ↦ by positivity))
    (((measurable_pathArea T).abs.pow_const n).aestronglyMeasurable)]
  calc
    _ ≤ (ENNReal.ofReal ε).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hh a ha haδ)
    _ = ε := ENNReal.toReal_ofReal hε.le

end PerronWright.BrownianPositiveBridgeAreaMomentTails
