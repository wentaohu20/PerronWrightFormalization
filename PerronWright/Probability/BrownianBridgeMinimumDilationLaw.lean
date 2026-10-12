import PerronWright.Probability.BrownianBridgeDilationGeometry
import PerronWright.Probability.BrownianBridgeCyclicPathLaw

/-! # Actual minimum-shift bridge path law duration scaling

The actual Brownian whole-path scaling law is combined with pointwise
bridge minimum-shift dilation. This is a law of the genuine measurable
bridge transform, not an asserted standard-excursion identification.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBridgeMinimumDilationLaw

open BrownianPathLaw BrownianPathDilationLaw BrownianBridgeMinimumShift
open BrownianBridgeDilationGeometry BrownianBridgeCyclicPathLaw BrownianBridgeCyclicPath

theorem minimumShiftPath_brownianDilation (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    minimumShiftPath T hT (brownianDilation T f) =
      brownianDilation T (minimumShiftPath 1 zero_lt_one f) :=
  minimumShiftPath_dilatePath T hT _ (Real.sqrt_pos.mpr hT) f

theorem minimumShiftLaw_duration_scaling (T : ℝ≥0) (hT : 0 < T) :
    minimumShiftLaw T hT = (minimumShiftLaw 1 zero_lt_one).map (brownianDilation T) := by
  calc minimumShiftLaw T hT = (pathLaw.map (brownianDilation T)).map (minimumShiftPath T hT) := by
        rw [pathLaw_brownianDilation T hT]
        rfl
    _ = pathLaw.map (brownianDilation T ∘ minimumShiftPath 1 zero_lt_one) := by
        rw [Measure.map_map (measurable_minimumShiftPath T hT) (measurable_brownianDilation T)]
        congr 1
        exact funext (minimumShiftPath_brownianDilation T hT)
    _ = (minimumShiftLaw 1 zero_lt_one).map (brownianDilation T) := by
        rw [minimumShiftLaw,Measure.map_map (measurable_brownianDilation T)
          (measurable_minimumShiftPath 1 zero_lt_one)]

theorem closedBridgePath_duration_scaling (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (stoppedClosedBridgePath T) =
      (pathLaw.map (stoppedClosedBridgePath 1)).map (brownianDilation T) := by
  calc pathLaw.map (stoppedClosedBridgePath T) =
        (pathLaw.map (brownianDilation T)).map (stoppedClosedBridgePath T) := by
        rw [pathLaw_brownianDilation T hT]
    _ = pathLaw.map (brownianDilation T ∘ stoppedClosedBridgePath 1) := by
        rw [Measure.map_map (measurable_stoppedClosedBridgePath T) (measurable_brownianDilation T)]
        congr 1
        exact funext (stoppedClosedBridgePath_dilatePath T hT _)
    _ = (pathLaw.map (stoppedClosedBridgePath 1)).map (brownianDilation T) := by
        rw [Measure.map_map (measurable_brownianDilation T) (measurable_stoppedClosedBridgePath 1)]

theorem bridgePathLaw_duration_scaling (T : ℝ≥0) (hT : 0 < T) :
    bridgePathLaw T = (bridgePathLaw 1).map (brownianDilation T) := by
  unfold bridgePathLaw
  rw [← Measure.map_congr (ae_stoppedClosedBridgePath_eq_stoppedBridgePath T),
    ← Measure.map_congr (ae_stoppedClosedBridgePath_eq_stoppedBridgePath 1)]
  exact closedBridgePath_duration_scaling T hT

theorem bridgeMinimumTime_duration_scaling (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (bridgeMinimumTime T) = (pathLaw.map (bridgeMinimumTime 1)).map (fun s ↦ T*s) := by
  calc pathLaw.map (bridgeMinimumTime T) = (pathLaw.map (brownianDilation T)).map (bridgeMinimumTime T) := by
        rw [pathLaw_brownianDilation T hT]
    _ = pathLaw.map ((fun s ↦ T*s) ∘ bridgeMinimumTime 1) := by
        rw [Measure.map_map (measurable_bridgeMinimumTime T) (measurable_brownianDilation T)]
        congr 1
        exact funext (bridgeMinimumTime_dilatePath T hT _ (Real.sqrt_pos.mpr hT))
    _ = (pathLaw.map (bridgeMinimumTime 1)).map (fun s ↦ T*s) := by
        rw [Measure.map_map (by fun_prop) (measurable_bridgeMinimumTime 1)]

theorem bridgeMinimumValue_duration_scaling (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (bridgeMinimumValue T) =
      (pathLaw.map (bridgeMinimumValue 1)).map (fun x ↦ Real.sqrt (T : ℝ)*x) := by
  calc pathLaw.map (bridgeMinimumValue T) = (pathLaw.map (brownianDilation T)).map (bridgeMinimumValue T) := by
        rw [pathLaw_brownianDilation T hT]
    _ = pathLaw.map ((fun x ↦ Real.sqrt (T : ℝ)*x) ∘ bridgeMinimumValue 1) := by
        rw [Measure.map_map (measurable_bridgeMinimumValue T) (measurable_brownianDilation T)]
        congr 1
        exact funext (bridgeMinimumValue_dilatePath T hT _ (Real.sqrt_pos.mpr hT))
    _ = (pathLaw.map (bridgeMinimumValue 1)).map (fun x ↦ Real.sqrt (T : ℝ)*x) := by
        rw [Measure.map_map (by fun_prop) (measurable_bridgeMinimumValue 1)]

end PerronWright.BrownianBridgeMinimumDilationLaw
