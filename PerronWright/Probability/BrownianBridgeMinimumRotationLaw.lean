import PerronWright.Probability.BrownianBridgeMinimumRotationGeometry
import PerronWright.Probability.BrownianBridgeRotationOffset

/-! # Actual minimum-shift joint law is invariant under rotating its time

Actual Gaussian bridge unique-minimum and whole-path cyclic invariance
give exact measurable time-offset equivariance and joint-law invariance.
This leaf does not assume or yet conclude a uniform time or independence.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeMinimumRotationLaw

open BrownianPathLaw BrownianBridgeCyclicPath BrownianBridgeCyclicPathLaw
open BrownianBridgeAreaTiltPathLaw BrownianBridgeMinimumShift BrownianBridgeUniqueMinimum
open BrownianBridgeMinimumRotationGeometry BrownianBridgeRotationOffset

theorem stoppedClosedBridgePath_stoppedBridgePath (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    stoppedClosedBridgePath T (stoppedBridgePath T f) = stoppedClosedBridgePath T f := by
  apply ContinuousMap.ext
  intro t
  exact closedBridge_stoppedBridgePath T hT (min t T) (min_le_right _ _) f

theorem bridgeMinimumTime_stoppedBridgePath (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    bridgeMinimumTime T (stoppedBridgePath T f) = bridgeMinimumTime T f := by
  unfold bridgeMinimumTime
  rw [stoppedClosedBridgePath_stoppedBridgePath T hT f]

theorem minimumShiftPath_stoppedBridgePath (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    minimumShiftPath T hT (stoppedBridgePath T f) = minimumShiftPath T hT f := by
  unfold minimumShiftPath
  rw [bridgeMinimumTime_stoppedBridgePath T hT f,
    cyclicBridgePath_stoppedBridgePath T _ hT (bridgeMinimumTime_le T f) f]

theorem ae_minimum_rotation_equivariance (T s : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) :
    ∀ᵐ f ∂pathLaw,
      bridgeMinimumTime T (cyclicBridgePath T hT s f) = reverseOffset T s (bridgeMinimumTime T f) ∧
      minimumShiftPath T hT (cyclicBridgePath T hT s f) = minimumShiftPath T hT f := by
  filter_upwards [ae_closedBridge_unique_minimum T hT] with f huniq
  constructor
  · rw [bridgeMinimumTime_cyclicBridgePath_of_unique T s hT hs f huniq,
      reverseOffset_eq_circleTime T s _ hT hs (bridgeMinimumTime_lt_end T hT f)]
  · exact minimumShiftPath_cyclicBridgePath_of_unique T s hT hs f huniq

def minimumShiftJointMap (T : ℝ≥0) (hT : 0 < T) (f : Path) : ℝ≥0 × Path :=
  (bridgeMinimumTime T f,minimumShiftPath T hT f)

theorem measurable_minimumShiftJointMap (T : ℝ≥0) (hT : 0 < T) :
    Measurable (minimumShiftJointMap T hT) :=
  (measurable_bridgeMinimumTime T).prodMk (measurable_minimumShiftPath T hT)

def minimumShiftJointLaw (T : ℝ≥0) (hT : 0 < T) : Measure (ℝ≥0 × Path) :=
  pathLaw.map (minimumShiftJointMap T hT)

instance (T : ℝ≥0) (hT : 0 < T) : IsProbabilityMeasure (minimumShiftJointLaw T hT) :=
  Measure.isProbabilityMeasure_map (measurable_minimumShiftJointMap T hT).aemeasurable

theorem minimumShiftJointLaw_rotation_invariant (T s : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) :
    (minimumShiftJointLaw T hT).map (fun p ↦ (reverseOffset T s p.1,p.2)) = minimumShiftJointLaw T hT := by
  have hmR : Measurable (fun p : ℝ≥0 × Path ↦ (reverseOffset T s p.1,p.2)) :=
    ((measurable_reverseOffset T s).comp measurable_fst).prodMk measurable_snd
  have he : (fun f : Path ↦ (reverseOffset T s (bridgeMinimumTime T f),minimumShiftPath T hT f)) =ᵐ[pathLaw]
      (minimumShiftJointMap T hT ∘ cyclicBridgePath T hT s) := by
    filter_upwards [ae_minimum_rotation_equivariance T s hT hs] with f hf
    exact Prod.ext hf.1.symm hf.2.symm
  unfold minimumShiftJointLaw
  rw [Measure.map_map hmR (measurable_minimumShiftJointMap T hT)]
  change pathLaw.map (fun f : Path ↦
    (reverseOffset T s (bridgeMinimumTime T f),minimumShiftPath T hT f)) = _
  rw [Measure.map_congr he,← Measure.map_map (measurable_minimumShiftJointMap T hT)
    (measurable_cyclicBridgePath T hT s),pathLaw_cyclicBridgePath_eq_stoppedBridgePath T s hT hs,
    Measure.map_map (measurable_minimumShiftJointMap T hT) (measurable_stoppedBridgePath T)]
  congr 1
  funext f
  exact Prod.ext (bridgeMinimumTime_stoppedBridgePath T hT f) (minimumShiftPath_stoppedBridgePath T hT f)

end PerronWright.BrownianBridgeMinimumRotationLaw
