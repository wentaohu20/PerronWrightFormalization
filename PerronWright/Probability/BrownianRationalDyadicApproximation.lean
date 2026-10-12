import PerronWright.Probability.BrownianDyadicModulus
import PerronWright.Probability.DyadicFloorGeometry

/-!
# The actual rational skeleton agrees with its dyadic approximations

Fourth-moment tails and Borel--Cantelli prove, on one common full-measure
set, convergence to the original process value at every nonnegative
rational time. Thus a later continuous dyadic extension cannot silently
replace the sampled process by an unrelated interpolation.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.BrownianRationalDyadicApproximation

open BrownianGaussianSkeleton BrownianGaussianMoments BrownianDyadicGrid
open BrownianDyadicModulus

def approxTime (n : ℕ) (q : RationalTime) : RationalTime :=
  dyadicTime n (DyadicFloorGeometry.index n (rationalTimeReal q))

theorem approxTime_real (n : ℕ) (q : RationalTime) :
    ((approxTime n q).val : ℝ) =
      (DyadicFloorGeometry.coordinate n (DyadicFloorGeometry.index n (rationalTimeReal q)) : ℝ) := by
  simp only [approxTime,dyadicTime_real,DyadicFloorGeometry.coordinate_real]

theorem approxTime_distance_bound (n : ℕ) (q : RationalTime) :
    |((approxTime n q).val : ℝ) - (q.val : ℝ)| ≤ 1 / (2 : ℝ) ^ n := by
  have hd : 0 < (2 : ℝ) ^ n := by positivity
  have h0 := DyadicFloorGeometry.index_le_scaled n (rationalTimeReal q)
  have h1 := DyadicFloorGeometry.scaled_lt_index_add_one n (rationalTimeReal q)
  change (DyadicFloorGeometry.index n (rationalTimeReal q) : ℝ) ≤ (q.val : ℝ) * (2 : ℝ) ^ n at h0
  change (q.val : ℝ) * (2 : ℝ) ^ n < (DyadicFloorGeometry.index n (rationalTimeReal q) : ℝ) + 1 at h1
  rw [approxTime_real,DyadicFloorGeometry.coordinate_real,abs_sub_comm]
  have hnn : 0 ≤ (q.val : ℝ) - (DyadicFloorGeometry.index n (rationalTimeReal q) : ℝ) / (2 : ℝ) ^ n :=
    sub_nonneg.mpr ((div_le_iff₀ hd).mpr h0)
  rw [abs_of_nonneg hnn]
  apply le_of_lt
  rw [sub_lt_iff_lt_add,← add_div,lt_div_iff₀ hd]
  simpa only [add_comm] using h1

def pointTailRatio : ℝ := 1 / (4 * decay ^ 4)

theorem pointTailRatio_pos : 0 < pointTailRatio := by norm_num [pointTailRatio,decay]

theorem pointTailRatio_lt_one : pointTailRatio < 1 := by norm_num [pointTailRatio,decay]

def pointBad (q : RationalTime) (n : ℕ) : Set (ℕ → ℝ) :=
  {x | decay ^ n ≤ ‖rationalProcess (approxTime n q) x - rationalProcess q x‖}

theorem point_tail_scaling (n : ℕ) :
    fourthMomentConstant * (1 / (2 : ℝ) ^ n) ^ 2 / (decay ^ n) ^ 4 =
      fourthMomentConstant * pointTailRatio ^ n := by
  have hp : (decay ^ 4) ^ n = (decay ^ n) ^ 4 := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  have ht : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [← pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  simp only [pointTailRatio,div_pow,one_pow,mul_pow,hp]
  rw [ht]
  field_simp

theorem pointBad_real_bound (q : RationalTime) (n : ℕ) :
    rationalLaw.real (pointBad q n) ≤ fourthMomentConstant * pointTailRatio ^ n := by
  have ht := rational_increment_tail_bound (approxTime n q) q (pow_pos decay_pos n)
  have hc := fourthMomentConstant_nonneg
  have hd := approxTime_distance_bound n q
  calc
    _ ≤ fourthMomentConstant * |((approxTime n q).val : ℝ) - (q.val : ℝ)| ^ 2 / (decay ^ n) ^ 4 := ht
    _ ≤ fourthMomentConstant * (1 / (2 : ℝ) ^ n) ^ 2 / (decay ^ n) ^ 4 := by
      gcongr
    _ = _ := point_tail_scaling n

theorem pointBad_measure_bound (q : RationalTime) (n : ℕ) :
    rationalLaw (pointBad q n) ≤ ENNReal.ofReal (fourthMomentConstant * pointTailRatio ^ n) := by
  calc
    _ = ENNReal.ofReal (rationalLaw.real (pointBad q n)) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (pointBad_real_bound q n)

theorem pointBad_tsum_ne_top (q : RationalTime) : (∑' n, rationalLaw (pointBad q n)) ≠ ∞ := by
  have hs : Summable (fun n : ℕ ↦ fourthMomentConstant * pointTailRatio ^ n) :=
    (summable_geometric_of_abs_lt_one (by rw [abs_of_pos pointTailRatio_pos]; exact pointTailRatio_lt_one)).mul_left _
  exact ne_of_lt ((ENNReal.tsum_le_tsum (pointBad_measure_bound q)).trans_lt hs.tsum_ofReal_lt_top)

/-- Convergence to the literal original sample value, not to an assumed
modification. This is proved separately at each rational time. -/
theorem ae_approxTime_process_tendsto (q : RationalTime) :
    ∀ᵐ x ∂rationalLaw, Tendsto (fun n ↦ rationalProcess (approxTime n q) x)
      atTop (𝓝 (rationalProcess q x)) := by
  filter_upwards [ae_eventually_notMem (pointBad_tsum_ne_top q)] with x hx
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
    (hx.mono (fun n hn ↦ (lt_of_not_ge hn).le))
  exact tendsto_pow_atTop_nhds_zero_of_lt_one decay_pos.le decay_lt_one

/-- All actual rational times agree simultaneously with their dyadic
approximation limits on one full-measure set of the constructed law. -/
theorem ae_all_rational_approxTime_process_tendsto :
    ∀ᵐ x ∂rationalLaw, ∀ q : RationalTime,
      Tendsto (fun n ↦ rationalProcess (approxTime n q) x) atTop (𝓝 (rationalProcess q x)) :=
  ae_all_iff.mpr ae_approxTime_process_tendsto

end PerronWright.BrownianRationalDyadicApproximation
