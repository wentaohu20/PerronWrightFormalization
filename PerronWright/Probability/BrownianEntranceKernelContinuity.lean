import PerronWright.Probability.BrownianMinimumEndpointCandidateContinuity

/-! # Actual entrance kernel continuity at positive duration

The positive-part expression removes the spatial indicator without
discarding the absorbing boundary. Gaussian continuity then gives
genuine joint duration/height continuity. The uniform bound retains
Gaussian decay, not only its constant supremum.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianEntranceKernelContinuity

open BrownianKilledBoundaryEntrance BrownianPositiveBridgeGaussianBounds

theorem entranceReal_eq_positive_part (t : ℝ≥0) (y : ℝ) :
    entranceReal t y = 2*max y 0/(t : ℝ)*gaussianPDFReal 0 t y := by
  by_cases hy : 0 < y
  · simp only [entranceReal,indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy),max_eq_left hy.le]
  · simp only [entranceReal,indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy),
      max_eq_right (le_of_not_gt hy),mul_zero,zero_div,zero_mul]

theorem continuousAt_joint_entranceReal (q : ℝ≥0 × ℝ) (ht : 0 < q.1) :
    ContinuousAt (fun p : ℝ≥0 × ℝ ↦ entranceReal p.1 p.2) q := by
  simp_rw [entranceReal_eq_positive_part]
  unfold gaussianPDFReal
  have htR : (0 : ℝ) < q.1 := ht
  fun_prop (disch := positivity)

theorem continuousAt_joint_entrance (q : ℝ≥0 × ℝ) (ht : 0 < q.1) :
    ContinuousAt (fun p : ℝ≥0 × ℝ ↦ entrance p.1 p.2) q :=
  ENNReal.continuous_ofReal.continuousAt.comp (continuousAt_joint_entranceReal q ht)

theorem entrance_le_envelope (δ t T : ℝ≥0) (hδ : 0 < δ)
    (hδt : δ ≤ t) (htT : t ≤ T) (y : ℝ) :
    entrance t y ≤ ENNReal.ofReal (envelopeReal δ T y) := by
  apply ENNReal.ofReal_le_ofReal
  apply le_of_tendsto (densityReal_div_start_tendsto t (hδ.trans_le hδt) y)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with a ha ha1
  exact densityReal_div_start_le_envelope a ha ha1.le δ t T hδ hδt htT y

end PerronWright.BrownianEntranceKernelContinuity
