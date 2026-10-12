import PerronWright.Probability.ContinuousPathMinimumDilation
import PerronWright.Probability.BrownianBridgeMinimumShift

/-! # Exact bridge closure, cyclic splice and earliest minimum dilation

All identities are for literal path operations. Positive space scaling
preserves the earliest minimizer even when the minimum is nonunique.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeDilationGeometry

open BrownianPathLaw BrownianPathDilationLaw BrownianPinnedBridge
open BrownianBridgeCyclicPath BrownianBridgeCycleKernel BrownianBridgeMinimumShift
open ContinuousPathMinimumDilation

theorem min_div_unit (T : ℝ≥0) (hT : 0 < T) (t : ℝ≥0) :
    min t T/T = min (t/T) 1 := by
  by_cases ht : t ≤ T
  · rw [min_eq_left ht,min_eq_left ((div_le_iff₀ hT).mpr (by simpa only [one_mul] using ht))]
  · have hTt : T ≤ t := (lt_of_not_ge ht).le
    rw [min_eq_right hTt,min_eq_right ((le_div_iff₀ hT).mpr (by simpa only [one_mul] using hTt)),
      div_self (ne_of_gt hT)]

theorem closedBridge_dilatePath (T : ℝ≥0) (hT : 0 < T) (c : ℝ) (f : Path) (t : ℝ≥0) :
    closedBridge T t (dilatePath T c f) = c*closedBridge 1 (t/T) f := by
  unfold closedBridge bridge
  change c*f (t/T)-(t : ℝ)/(T : ℝ)*(c*f (T/T))-
    (1-(t : ℝ)/(T : ℝ))*(c*f (0/T)) =
    c*(f (t/T)-(↑(t/T) : ℝ)/(1 : ℝ)*(f 1)-(1-(↑(t/T) : ℝ)/(1 : ℝ))*f 0)
  rw [div_self (ne_of_gt hT),zero_div,NNReal.coe_div]
  ring

theorem stoppedClosedBridgePath_dilatePath (T : ℝ≥0) (hT : 0 < T) (c : ℝ) (f : Path) :
    stoppedClosedBridgePath T (dilatePath T c f) = dilatePath T c (stoppedClosedBridgePath 1 f) := by
  apply ContinuousMap.ext
  intro t
  change closedBridge T (min t T) (dilatePath T c f) = c*closedBridge 1 (min (t/T) 1) f
  rw [closedBridge_dilatePath T hT c f,min_div_unit T hT t]

theorem bridgeMinimumValue_dilatePath (T : ℝ≥0) (hT : 0 < T) (c : ℝ) (hc : 0 < c) (f : Path) :
    bridgeMinimumValue T (dilatePath T c f) = c*bridgeMinimumValue 1 f := by
  unfold bridgeMinimumValue
  rw [stoppedClosedBridgePath_dilatePath T hT c f,minimumValue_dilatePath T hT c hc]

theorem bridgeMinimumTime_dilatePath (T : ℝ≥0) (hT : 0 < T) (c : ℝ) (hc : 0 < c) (f : Path) :
    bridgeMinimumTime T (dilatePath T c f) = T*bridgeMinimumTime 1 f := by
  unfold bridgeMinimumTime
  rw [stoppedClosedBridgePath_dilatePath T hT c f,leastMinimizer_dilatePath T hT c hc]

theorem cycleTime_dilate (T : ℝ≥0) (hT : 0 < T) (s t : ℝ≥0) :
    cycleTime T (T*s) t = T*cycleTime 1 s (t/T) := by
  have he : T*(s+t/T) = T*s+t := by
    rw [mul_add,mul_comm T (t/T),div_mul_cancel₀ _ (ne_of_gt hT)]
  have hbranch : T*s+t ≤ T ↔ s+t/T ≤ 1 := by
    rw [← he]
    constructor
    · intro h
      apply (mul_le_mul_iff_right₀ hT).mp
      simpa only [mul_one] using h
    · intro h
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h (show 0 ≤ T from zero_le)
  unfold cycleTime
  by_cases h : T*s+t ≤ T
  · rw [if_pos h,if_pos (hbranch.mp h)]
    exact he.symm
  · rw [if_neg h,if_neg (fun he ↦ h (hbranch.mpr he)),mul_tsub,mul_one]
    rw [he]

theorem cyclicBridgePath_dilatePath (T : ℝ≥0) (hT : 0 < T) (s : ℝ≥0) (c : ℝ) (f : Path) :
    cyclicBridgePath T hT (T*s) (dilatePath T c f) =
      dilatePath T c (cyclicBridgePath 1 zero_lt_one s f) := by
  apply ContinuousMap.ext
  intro t
  change closedBridge T (cycleTime T (T*s) (min t T)) (dilatePath T c f)-
    closedBridge T (T*s) (dilatePath T c f) =
    c*(closedBridge 1 (cycleTime 1 s (min (t/T) 1)) f-closedBridge 1 s f)
  rw [closedBridge_dilatePath T hT c f,closedBridge_dilatePath T hT c f,
    cycleTime_dilate T hT,mul_comm T,mul_div_cancel_right₀ _ (ne_of_gt hT),
    min_div_unit T hT,mul_comm T,mul_div_cancel_right₀ _ (ne_of_gt hT)]
  ring

theorem minimumShiftPath_dilatePath (T : ℝ≥0) (hT : 0 < T) (c : ℝ) (hc : 0 < c) (f : Path) :
    minimumShiftPath T hT (dilatePath T c f) = dilatePath T c (minimumShiftPath 1 zero_lt_one f) := by
  unfold minimumShiftPath
  rw [bridgeMinimumTime_dilatePath T hT c hc f,cyclicBridgePath_dilatePath T hT]

end PerronWright.BrownianBridgeDilationGeometry
