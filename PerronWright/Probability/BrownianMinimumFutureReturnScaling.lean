import PerronWright.Probability.BrownianMinimumFutureFirstReturn
import PerronWright.Probability.BrownianKilledAreaScalingGeometry

/-! # Positive-time return under actual Brownian time-space dilation

The literal strictly-positive hit set scales before its infimum is taken.
Thus the result includes infinite return times and does not assume an
excursion-duration law. Actual entrance-source positivity and finite return
then transfer to every positive duration.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianMinimumFutureReturnScaling

open BrownianPathLaw BrownianPathDilationLaw BrownianKilledAreaScalingGeometry
open BrownianMinimumFutureEntranceSource BrownianMinimumFutureFirstReturn

theorem positive_return_hit_set_dilation (c : ℝ≥0) (hc : 0 < c) (g : Path) :
    (fun t : ℝ≥0 ↦ (t : ℝ≥0∞)) ''
        {t : ℝ≥0 | 0 < t ∧ brownianDilation c g t ≤ 0} =
      (fun x : ℝ≥0∞ ↦ (c : ℝ≥0∞)*x) ''
        ((fun t : ℝ≥0 ↦ (t : ℝ≥0∞)) '' {t : ℝ≥0 | 0 < t ∧ g t ≤ 0}) := by
  ext x
  constructor
  · rintro ⟨t,⟨ht,hg⟩,rfl⟩
    refine ⟨((t/c : ℝ≥0) : ℝ≥0∞),⟨t/c,⟨div_pos ht hc,?_⟩,rfl⟩,?_⟩
    · change Real.sqrt (c : ℝ)*g (t/c) ≤ 0 at hg
      by_contra hn
      exact (not_le_of_gt (mul_pos (Real.sqrt_pos.mpr hc) (lt_of_not_ge hn))) hg
    · change (c : ℝ≥0∞)*((t/c : ℝ≥0) : ℝ≥0∞) = (t : ℝ≥0∞)
      rw [← ENNReal.coe_mul,mul_div_cancel₀ t (ne_of_gt hc)]
  · rintro ⟨x,⟨t,⟨ht,hg⟩,rfl⟩,rfl⟩
    refine ⟨c*t,⟨mul_pos hc ht,?_⟩,by simp only [ENNReal.coe_mul]⟩
    rw [brownianDilation,dilatePath_eval_scaled_duration c t hc]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hg

theorem firstReturnZero_brownianDilation (c : ℝ≥0) (hc : 0 < c) (g : Path) :
    firstReturnZero (brownianDilation c g) = (c : ℝ≥0∞)*firstReturnZero g := by
  have hu : IsUnit (c : ℝ≥0∞) := ENNReal.isUnit_iff.mpr
    ⟨by exact_mod_cast ne_of_gt hc,ENNReal.coe_ne_top⟩
  let e := ENNReal.mulLeftOrderIso (c : ℝ≥0∞) hu
  unfold firstReturnZero
  rw [positive_return_hit_set_dilation c hc]
  exact (map_sInf e _).symm

theorem aemeasurable_dilated_firstReturnZero (c : ℝ≥0) (hc : 0 < c) :
    AEMeasurable (fun g : Path ↦ firstReturnZero (brownianDilation c g)) unitSourceLaw := by
  have hm := aemeasurable_firstReturnZero.const_mul (c : ℝ≥0∞)
  exact hm.congr (Filter.Eventually.of_forall
    (fun g ↦ (firstReturnZero_brownianDilation c hc g).symm))

theorem ae_dilated_source_strict_positive_prefix (c : ℝ≥0) (hc : 0 < c) :
    ∀ᵐ g : Path ∂unitSourceLaw, ∀ t : ℝ≥0, 0 < t → t ≤ c →
      0 < brownianDilation c g t := by
  filter_upwards [ae_unitSourceLaw_strict_positive_prefix] with g hg
  intro t ht0 htc
  change 0 < Real.sqrt (c : ℝ)*g (t/c)
  apply mul_pos (Real.sqrt_pos.mpr hc)
  apply hg (t/c) (div_pos ht0 hc)
  exact (div_le_one hc).mpr htc

theorem ae_dilated_source_firstReturn_finite (c : ℝ≥0) (hc : 0 < c) :
    ∀ᵐ g : Path ∂unitSourceLaw, firstReturnZero (brownianDilation c g) ≠ ⊤ := by
  filter_upwards [ae_unitSourceLaw_firstReturn_finite] with g hg
  rw [firstReturnZero_brownianDilation c hc]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top hg

theorem ae_dilated_source_firstReturn_gt_duration (c : ℝ≥0) (hc : 0 < c) :
    ∀ᵐ g : Path ∂unitSourceLaw, (c : ℝ≥0∞) < firstReturnZero (brownianDilation c g) := by
  filter_upwards [ae_unitSourceLaw_firstReturn_gt_one] with g hg
  rw [firstReturnZero_brownianDilation c hc]
  simpa only [mul_one] using
    (ENNReal.mul_lt_mul_iff_right (by exact_mod_cast ne_of_gt hc) ENNReal.coe_ne_top).mpr hg

theorem ae_dilated_source_firstReturn_exact_zero (c : ℝ≥0) (hc : 0 < c) :
    ∀ᵐ g : Path ∂unitSourceLaw,
      brownianDilation c g (firstReturnZero (brownianDilation c g)).toNNReal = 0 := by
  filter_upwards [ae_unitSourceLaw_firstReturn_exact_zero] with g hg
  rw [firstReturnZero_brownianDilation c hc,ENNReal.toNNReal_mul,ENNReal.toNNReal_coe,
    brownianDilation,dilatePath_eval_scaled_duration c _ hc,hg,mul_zero]

end PerronWright.BrownianMinimumFutureReturnScaling
