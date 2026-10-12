import PerronWright.Probability.BrownianBridgeMinimumUniformTests
import PerronWright.Probability.BrownianPositiveBridgeConditioning

/-! # Exact reconstruction and minimum-depth geometry

The earliest-minimum cyclic transform can be inverted by rotating back.
Its value at the inverse rotation time is exactly the original minimum
depth. Constant translations do not affect this literal transform.
No excursion identity or conditional-law premise is introduced.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeMinimumReconstruction

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeCyclicPath BrownianBridgeCycleKernel
open BrownianBridgeMinimumShift BrownianBridgeCircleGeometry BrownianPositiveBridgeConditioning
open BrownianFirstPassageBridgeLaw

theorem closedBridge_translate (T t : ℝ≥0) (a : ℝ) (f : Path) :
    closedBridge T t (translate a f) = closedBridge T t f := by
  unfold closedBridge bridge
  simp only [translate_eval]
  ring

theorem stoppedClosedBridgePath_translate (T : ℝ≥0) (a : ℝ) (f : Path) :
    stoppedClosedBridgePath T (translate a f) = stoppedClosedBridgePath T f := by
  apply ContinuousMap.ext
  intro t
  exact closedBridge_translate T (min t T) a f

theorem bridgeMinimumTime_translate (T : ℝ≥0) (a : ℝ) (f : Path) :
    bridgeMinimumTime T (translate a f) = bridgeMinimumTime T f := by
  unfold bridgeMinimumTime
  rw [stoppedClosedBridgePath_translate]

theorem minimumShiftPath_translate (T : ℝ≥0) (hT : 0 < T) (a : ℝ) (f : Path) :
    minimumShiftPath T hT (translate a f) = minimumShiftPath T hT f := by
  unfold minimumShiftPath
  rw [bridgeMinimumTime_translate]
  apply ContinuousMap.ext
  intro t
  change closedBridge T (cycleTime T (bridgeMinimumTime T f) (min t T)) (translate a f)-
      closedBridge T (bridgeMinimumTime T f) (translate a f) = _
  rw [closedBridge_translate,closedBridge_translate]
  rfl

theorem cyclicBridgePath_zero_offset (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    cyclicBridgePath T hT 0 f = stoppedClosedBridgePath T f := by
  apply ContinuousMap.ext
  intro t
  change closedBridge T (cycleTime T 0 (min t T)) f-closedBridge T 0 f = _
  have he : cycleTime T 0 (min t T) = min t T := by
    simp only [cycleTime,zero_add,if_pos (min_le_right t T)]
  rw [he,closedBridge_zero,sub_zero]
  rfl

theorem minimumShiftPath_inverse_rotate (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    cyclicBridgePath T hT (T-bridgeMinimumTime T f) (minimumShiftPath T hT f) =
      stoppedClosedBridgePath T f := by
  unfold minimumShiftPath
  rw [cyclicBridgePath_compose T (bridgeMinimumTime T f) (T-bridgeMinimumTime T f)
    hT (bridgeMinimumTime_le T f) tsub_le_self]
  have he : (bridgeMinimumTime T f : ℝ)+(T-bridgeMinimumTime T f : ℝ≥0) = (T : ℝ) := by
    rw [NNReal.coe_sub (bridgeMinimumTime_le T f)]
    ring
  rw [he,circleTime_period,cyclicBridgePath_zero_offset]

theorem minimumShiftPath_inverse_time_value (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    minimumShiftPath T hT f (T-bridgeMinimumTime T f) = -bridgeMinimumValue T f := by
  unfold minimumShiftPath
  change closedBridge T (cycleTime T (bridgeMinimumTime T f)
    (min (T-bridgeMinimumTime T f) T)) f-closedBridge T (bridgeMinimumTime T f) f = _
  rw [min_eq_left tsub_le_self]
  have he : bridgeMinimumTime T f+(T-bridgeMinimumTime T f) = T :=
    add_tsub_cancel_of_le (bridgeMinimumTime_le T f)
  rw [cycleTime,he,if_pos le_rfl,closedBridge_endpoint T hT f,bridgeMinimumTime_value,zero_sub]

theorem closedBridge_eq_of_endpoints (T t : ℝ≥0) (f : Path) (h0 : f 0 = 0) (hT : f T = 0) :
    closedBridge T t f = f t := by
  simp only [closedBridge,bridge,h0,hT,mul_zero,sub_zero]

theorem bridgeConstraint_iff_minimum (a : ℝ) (T : ℝ≥0) (f : Path)
    (h0 : f 0 = 0) (hT : f T = 0) :
    f ∈ bridgeConstraint (-a) T 0 ↔ -a < bridgeMinimumValue T f := by
  rw [mem_bridgeConstraint_iff]
  simp only [mul_zero,add_zero]
  constructor
  · intro hf
    have he := hf (bridgeMinimumTime T f) (bridgeMinimumTime_le T f)
    rw [← closedBridge_eq_of_endpoints T _ f h0 hT,bridgeMinimumTime_value] at he
    exact he
  · intro hf t ht
    have hm := bridgeMinimumValue_le T f t ht
    rw [closedBridge_eq_of_endpoints T t f h0 hT] at hm
    exact hf.trans_le hm

theorem bridgeConstraint_iff_shifted_height (a : ℝ) (T : ℝ≥0) (hT : 0 < T) (f : Path)
    (h0 : f 0 = 0) (hend : f T = 0) :
    f ∈ bridgeConstraint (-a) T 0 ↔
      minimumShiftPath T hT f (T-bridgeMinimumTime T f) < a := by
  rw [bridgeConstraint_iff_minimum a T f h0 hend,minimumShiftPath_inverse_time_value]
  constructor <;> intro h <;> linarith

end PerronWright.BrownianBridgeMinimumReconstruction
