import PerronWright.Probability.BrownianEntranceDyadicSamples
import PerronWright.Probability.BrownianEntrancePaddedIncrement
import PerronWright.Probability.BrownianPositiveBridgeGlobalIncrementMoments

/-! # Actual fourth moments of the constructed entrance samples

The genuine positive-bridge full-horizon estimate is discharged here.
Endpoint padding has a proved vanishing error; bounded-source limits and
monotone truncation give unbounded moments under the constructed countable
law. The physical clamped dyadic gap is bounded by 2^(-n).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceDyadicMoments

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianEntranceMomentTransfer
open BrownianEntrancePaddedIncrement BrownianEntranceDyadicSamples DyadicFloorGeometry
open BrownianPositiveBridgeGlobalIncrementMoments

theorem countable_fourth_increment_bound (T : ℝ≥0) (hT : 0 < T)
    (σ : ℕ → ℝ≥0) (i j : ℕ) (hi : σ i ≤ T) (hj : σ j ≤ T) :
    (∫⁻ x, ENNReal.ofReal (‖x j-x i‖^4) ∂BrownianEntranceCountableLaw.law T hT σ) ≤
      (8*globalCoefficient T)*ENNReal.ofReal (|(σ j : ℝ)-(σ i : ℝ)|^2) := by
  let D : ℝ≥0∞ := (8*globalCoefficient T)*ENNReal.ofReal (|(σ j : ℝ)-(σ i : ℝ)|^2)
  have ht : Tendsto (fun a : ℝ ↦ D+8*ENNReal.ofReal (|a|^4)) (𝓝[>] 0) (𝓝 D) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := D)).add vanishing_padding_error
  apply fourth_increment_le_of_actual_upper_limit T hT σ i j _ D ht
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_pair_fourth_increment T hT] with a ha hbound
  apply (padded_fourth_lintegral_le a ha T hT (σ i) (σ j) hi hj).trans
  have hm := mul_le_mul' (le_rfl : (8 : ℝ≥0∞) ≤ 8) (hbound (σ i) (σ j) hi hj)
  simpa only [D,mul_assoc] using add_le_add hm
    (le_rfl : 8*ENNReal.ofReal (|a|^4) ≤ 8*ENNReal.ofReal (|a|^4))

def momentCoefficient (T : ℝ≥0) : ℝ := (8*globalCoefficient T).toReal

theorem momentCoefficient_nonneg (T : ℝ≥0) : 0 ≤ momentCoefficient T :=
  ENNReal.toReal_nonneg

theorem ofReal_momentCoefficient (T : ℝ≥0) (hT : 0 < T) :
    ENNReal.ofReal (momentCoefficient T) = 8*globalCoefficient T :=
  ENNReal.ofReal_toReal (ENNReal.mul_ne_top (by simp) (globalCoefficient_ne_top T hT))

theorem coordinate_neighbor_gap (n k : ℕ) :
    |(coordinate n (k+1) : ℝ)-(coordinate n k : ℝ)| = 1/(2 : ℝ)^n := by
  have he : (coordinate n (k+1) : ℝ)-(coordinate n k : ℝ) = 1/(2 : ℝ)^n := by
    simp only [coordinate_real,Nat.cast_add,Nat.cast_one]
    ring
  rw [he,abs_of_nonneg (by positivity)]

theorem clamped_neighbor_gap_le (T : ℝ≥0) (n k : ℕ) :
    |(clampedTime T n (k+1) : ℝ)-(clampedTime T n k : ℝ)| ≤ 1/(2 : ℝ)^n := by
  simp only [clampedTime,NNReal.coe_min]
  calc
    _ ≤ max |(coordinate n (k+1) : ℝ)-(coordinate n k : ℝ)| |(T : ℝ)-T| :=
      abs_min_sub_min_le_max _ _ _ _
    _ = _ := by rw [coordinate_neighbor_gap,sub_self,abs_zero,max_eq_left (by positivity)]

/-- Actual dyadic fourth moments, with no moment-bound or regularity
interface remaining as an input. -/
theorem fourth_dyadic_increment_bound (T : ℝ≥0) (hT : 0 < T) (n k : ℕ) :
    (∫⁻ x, ENNReal.ofReal (‖samples x n (k+1)-samples x n k‖^4) ∂law T hT) ≤
      ENNReal.ofReal (momentCoefficient T*(1/(2 : ℝ)^n)^2) := by
  have he := countable_fourth_increment_bound T hT (samplingTimes T) (Nat.pair n k)
    (Nat.pair n (k+1))
    (by simpa only [samplingTimes_pair] using clampedTime_le_horizon T n k)
    (by simpa only [samplingTimes_pair] using clampedTime_le_horizon T n (k+1))
  simp only [samplingTimes_pair] at he
  apply he.trans
  calc
    _ ≤ (8*globalCoefficient T)*ENNReal.ofReal ((1/(2 : ℝ)^n)^2) := by
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _)
        (clamped_neighbor_gap_le T n k) 2))
    _ = _ := by
      rw [ENNReal.ofReal_mul (momentCoefficient_nonneg T),ofReal_momentCoefficient T hT]

end PerronWright.BrownianEntranceDyadicMoments
