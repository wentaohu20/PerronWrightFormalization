import PerronWright.Probability.BrownianPinnedBridgeFiniteLaw

/-! # Exact cyclic bridge covariance algebra

The cyclic splice is literal addition followed by one wrap on [0,T].
Endpoints 0 and T are interchangeable for a closed bridge. No cyclic
invariance theorem or excursion law is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBridgeCycleKernel

def cycleTime (T s t : ℝ≥0) : ℝ≥0 :=
  if s+t ≤ T then s+t else s+t-T

def realCycleTime (T s t : ℝ) : ℝ :=
  if s+t ≤ T then s+t else s+t-T

theorem cycleTime_le (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) :
    cycleTime T s t ≤ T := by
  unfold cycleTime
  split_ifs with h
  · exact h
  · exact tsub_le_iff_right.mpr (by linarith)

theorem cycleTime_real (T s t : ℝ≥0) :
    (cycleTime T s t : ℝ) = realCycleTime T s t := by
  unfold cycleTime realCycleTime
  by_cases h : s+t ≤ T
  · have hr : (s : ℝ)+(t : ℝ) ≤ T := h
    simp only [if_pos h,if_pos hr,NNReal.coe_add]
  · have hr : ¬(s : ℝ)+(t : ℝ) ≤ T := h
    simp only [if_neg h,if_neg hr,NNReal.coe_sub (le_of_lt (lt_of_not_ge h)),NNReal.coe_add]

theorem cycleTime_zero (T s : ℝ≥0) (hs : s ≤ T) : cycleTime T s 0 = s := by
  simp [cycleTime,hs]

theorem cycleTime_endpoint (T s : ℝ≥0) : cycleTime T s T = if s=0 then T else s := by
  by_cases hs : s=0
  · simp [cycleTime,hs]
  · have hp : 0 < s := pos_iff_ne_zero.mpr hs
    have hn : ¬s+T ≤ T := by linarith
    simp [cycleTime,hn,hs]

private theorem kernel_identity_ordered (T s t u : ℝ) (hT : 0 < T)
    (ht0 : 0 ≤ t) (hu : u ≤ T) (htu : t ≤ u) :
    (min (realCycleTime T s t) (realCycleTime T s u) -
      realCycleTime T s t*realCycleTime T s u/T) -
    (min (realCycleTime T s t) s-realCycleTime T s t*s/T) -
    (min s (realCycleTime T s u)-s*realCycleTime T s u/T) + (s-s*s/T) =
      min t u-t*u/T := by
  have hne : T ≠ 0 := ne_of_gt hT
  unfold realCycleTime
  by_cases ht : s+t ≤ T
  · by_cases hu' : s+u ≤ T
    · simp only [if_pos ht,if_pos hu',min_eq_left htu,
        min_eq_left (show s+t ≤ s+u by linarith),
        min_eq_right (show s ≤ s+t by linarith),
        min_eq_left (show s ≤ s+u by linarith)]
      field_simp
      ring
    · simp only [if_pos ht,if_neg hu',min_eq_left htu,
        min_eq_right (show s+u-T ≤ s+t by linarith),
        min_eq_right (show s ≤ s+t by linarith),
        min_eq_right (show s+u-T ≤ s by linarith)]
      field_simp
      ring
  · have hu' : ¬s+u ≤ T := by linarith
    simp only [if_neg ht,if_neg hu',min_eq_left htu,
      min_eq_left (show s+t-T ≤ s+u-T by linarith),
      min_eq_left (show s+t-T ≤ s by linarith),
      min_eq_right (show s+u-T ≤ s by linarith)]
    field_simp
    ring

theorem cycle_kernel_identity (T s t u : ℝ≥0) (hT : 0 < T)
    (_hs : s ≤ T) (ht : t ≤ T) (hu : u ≤ T) :
    (min (cycleTime T s t : ℝ) (cycleTime T s u : ℝ) -
      (cycleTime T s t : ℝ)*(cycleTime T s u : ℝ)/(T : ℝ)) -
    (min (cycleTime T s t : ℝ) (s : ℝ)-(cycleTime T s t : ℝ)*(s : ℝ)/(T : ℝ)) -
    (min (s : ℝ) (cycleTime T s u : ℝ)-(s : ℝ)*(cycleTime T s u : ℝ)/(T : ℝ)) +
      ((s : ℝ)-(s : ℝ)*(s : ℝ)/(T : ℝ)) =
      min (t : ℝ) (u : ℝ)-(t : ℝ)*(u : ℝ)/(T : ℝ) := by
  simp only [cycleTime_real]
  rcases le_total t u with htu|hut
  · exact kernel_identity_ordered T s t u hT t.coe_nonneg hu htu
  · have h := kernel_identity_ordered T s u t hT u.coe_nonneg ht hut
    rw [min_comm (realCycleTime _ _ _) (realCycleTime _ _ _),min_comm (u : ℝ) (t : ℝ),
      min_comm (realCycleTime T s u) (s : ℝ),min_comm (s : ℝ) (realCycleTime T s t)] at h
    convert h using 1 <;> ring

end PerronWright.BrownianBridgeCycleKernel
