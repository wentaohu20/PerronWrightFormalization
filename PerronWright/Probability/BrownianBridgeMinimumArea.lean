import PerronWright.Probability.BrownianBridgeMinimumShift
import PerronWright.Probability.BrownianBridgeCyclicArea

/-! # Actual measurable earliest-minimum-shift bridge area

This is the literal integral of the genuine earliest-minimum cyclic
transform of the constructed Brownian bridge. It is measurable and
nonnegative, and equals signed bridge area minus T times the actual
minimum. No positive-excursion law or Wright moments are asserted.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBridgeMinimumArea

open BrownianPathLaw BrownianPinnedBridge BrownianPinnedBridgeArea
open BrownianBridgeCyclicArea BrownianBridgeMinimumShift

def minimumShiftArea (T : ℝ≥0) (hT : 0 < T) (f : Path) : ℝ :=
  pathArea T (minimumShiftPath T hT f)

theorem intervalIntegrable_minimumShiftPath (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    IntervalIntegrable (fun t : ℝ ↦ minimumShiftPath T hT f (Real.toNNReal t)) volume 0 (T : ℝ) :=
  ((continuous_path (minimumShiftPath T hT f)).comp continuous_real_toNNReal).intervalIntegrable 0 T

theorem measurable_minimumShiftArea (T : ℝ≥0) (hT : 0 < T) :
    Measurable (minimumShiftArea T hT) :=
  (measurable_pathArea T).comp (measurable_minimumShiftPath T hT)

theorem minimumShiftArea_eq_closedArea_sub_minimum (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    minimumShiftArea T hT f = closedArea T f-(T : ℝ)*bridgeMinimumValue T f := by
  unfold minimumShiftArea minimumShiftPath
  rw [pathArea_cyclicBridgePath T _ hT (bridgeMinimumTime_le T f) f,bridgeMinimumTime_value]

theorem minimumShiftArea_nonnegative (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    0 ≤ minimumShiftArea T hT f :=
  intervalIntegral.integral_nonneg_of_forall T.coe_nonneg
    (fun _ ↦ minimumShiftPath_nonnegative T hT f _)

/-- The actual Brownian path identity relates the true measurable
nonnegative minimum-shift area to the signed Gaussian bridge area.
Their laws are not equated. -/
theorem ae_minimumShiftArea_eq_area_sub_minimum (T : ℝ≥0) (hT : 0 < T) :
    minimumShiftArea T hT =ᵐ[pathLaw] fun f ↦ area T f-(T : ℝ)*bridgeMinimumValue T f := by
  filter_upwards [ae_closedArea_eq_area T] with f hf
  rw [minimumShiftArea_eq_closedArea_sub_minimum T hT f,hf]

theorem ae_minimumShiftArea_eq_area_sub_value (T : ℝ≥0) (hT : 0 < T) :
    minimumShiftArea T hT =ᵐ[pathLaw]
      fun f ↦ area T f-(T : ℝ)*bridge T (bridgeMinimumTime T f) f := by
  filter_upwards [ae_pathArea_cyclicBridgePath T hT] with f hf
  exact hf _ (bridgeMinimumTime_le T f)

end PerronWright.BrownianBridgeMinimumArea
