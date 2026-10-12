import PerronWright.Probability.BrownianBridgeCircleGeometry

/-! # Exact unique-minimum and minimum-shift rotation equivariance

For any continuous closed bridge with a unique minimum, the actual
earliest minimizer rotates by the signed offset modulo T. The actual
minimum-shifted path is unchanged. The offset-zero case is handled by
leastness, because the rotated closed path then has both endpoint minima.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeMinimumRotationGeometry

open BrownianPathLaw BrownianBridgeCyclicPath BrownianBridgeMinimumShift
open BrownianBridgeCircleGeometry BrownianBridgeCyclicGeometry

theorem bridgeMinimumTime_lt_end (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    bridgeMinimumTime T f < T := by
  apply lt_of_le_of_ne (bridgeMinimumTime_le T f)
  intro he
  have hmin : closedBridge T 0 f = bridgeMinimumValue T f := by
    rw [closedBridge_zero,← bridgeMinimumTime_value T f,he,closedBridge_endpoint T hT f]
  have hz := bridgeMinimumTime_le_of_eq T f 0 zero_le hmin
  rw [he] at hz
  exact hT.not_ge hz

theorem bridgeMinimumValue_cyclicBridgePath (T s : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (f : Path) :
    bridgeMinimumValue T (cyclicBridgePath T hT s f) = bridgeMinimumValue T f-closedBridge T s f := by
  let m := bridgeMinimumTime T f
  let r := circleTime T hT ((m : ℝ)-(s : ℝ))
  have hmr : circleTime T hT ((s : ℝ)+(r : ℝ)) = m :=
    circleTime_sub_inverse T m s hT (bridgeMinimumTime_lt_end T hT f)
  have hr : r < T := circleTime_lt T hT _
  have heAt : closedBridge T r (cyclicBridgePath T hT s f) = bridgeMinimumValue T f-closedBridge T s f := by
    rw [closedBridge_cyclicBridgePath T s r hT hs,
      cyclicBridgePath_eq_circle T s r hT hs,min_eq_left hr.le,hmr]
    rw [bridgeMinimumTime_value]
  apply le_antisymm
  · rw [← heAt]
    exact bridgeMinimumValue_le T _ r hr.le
  · rw [← bridgeMinimumTime_value T (cyclicBridgePath T hT s f),
      closedBridge_cyclicBridgePath T s _ hT hs,cyclicBridgePath_eq_circle T s _ hT hs,
      min_eq_left (bridgeMinimumTime_le T (cyclicBridgePath T hT s f))]
    exact sub_le_sub_right (bridgeMinimumValue_le T f _ (circleTime_lt T hT _).le) _

theorem bridgeMinimumTime_cyclicBridgePath_of_unique (T s : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (f : Path)
    (huniq : ∀ t : ℝ≥0, t ≤ T → closedBridge T t f = bridgeMinimumValue T f →
      t = bridgeMinimumTime T f) :
    bridgeMinimumTime T (cyclicBridgePath T hT s f) =
      circleTime T hT ((bridgeMinimumTime T f : ℝ)-(s : ℝ)) := by
  let g := cyclicBridgePath T hT s f
  let j := bridgeMinimumTime T g
  have hj : j < T := bridgeMinimumTime_lt_end T hT g
  have hm : closedBridge T (circleTime T hT ((s : ℝ)+(j : ℝ))) f = bridgeMinimumValue T f := by
    have he := bridgeMinimumTime_value T g
    rw [bridgeMinimumValue_cyclicBridgePath T s hT hs f,
      closedBridge_cyclicBridgePath T s j hT hs,
      cyclicBridgePath_eq_circle T s j hT hs,min_eq_left hj.le] at he
    linarith
  have horig : circleTime T hT ((s : ℝ)+(j : ℝ)) = bridgeMinimumTime T f :=
    huniq _ (circleTime_lt T hT _).le hm
  have hback := congrArg (fun u : ℝ≥0 ↦ circleTime T hT (-(s : ℝ)+(u : ℝ))) horig
  rw [circleTime_cancel_shift T j s hT hj] at hback
  simpa only [sub_eq_add_neg,add_comm] using hback

theorem minimumShiftPath_cyclicBridgePath_of_unique (T s : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (f : Path)
    (huniq : ∀ t : ℝ≥0, t ≤ T → closedBridge T t f = bridgeMinimumValue T f →
      t = bridgeMinimumTime T f) :
    minimumShiftPath T hT (cyclicBridgePath T hT s f) = minimumShiftPath T hT f := by
  unfold minimumShiftPath
  rw [bridgeMinimumTime_cyclicBridgePath_of_unique T s hT hs f huniq,
    cyclicBridgePath_compose T s _ hT hs (circleTime_lt T hT _).le,
    circleTime_sub_inverse T (bridgeMinimumTime T f) s hT (bridgeMinimumTime_lt_end T hT f)]

end PerronWright.BrownianBridgeMinimumRotationGeometry
