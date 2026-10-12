import PerronWright.Probability.BrownianBridgeCyclicPath
import PerronWright.Probability.BrownianBridgeCyclicFiniteLaw
import PerronWright.Probability.BrownianBridgeAreaTiltPathLaw

/-! # Actual full continuous pinned-bridge cyclic law

The explicit cyclic splice has the same compact-open path Borel law
as the genuine stopped pinned Brownian bridge. This follows from
proved Gaussian finite laws, projective uniqueness and the actual
rational-evaluation measurable embedding. It is not an assumption
about a bridge, excursion, conditioning or Palm distribution.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeCyclicPathLaw

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeCycleKernel
open BrownianBridgeCyclicPath BrownianBridgeCyclicFiniteLaw
open BrownianBridgeAreaTiltPathLaw BrownianGaussianSkeleton

theorem ae_cyclicValue_eq_rotation (T s : ℝ≥0) :
    ∀ᵐ f ∂pathLaw, ∀ t, cyclicValue T s t f = rotation T s t f := by
  filter_upwards [ae_closedBridge_eq_bridge T] with f hf
  intro t
  simp only [cyclicValue,rotation,hf]

theorem ae_stoppedClosedBridgePath_eq_stoppedBridgePath (T : ℝ≥0) :
    stoppedClosedBridgePath T =ᵐ[pathLaw] stoppedBridgePath T := by
  filter_upwards [ae_closedBridge_eq_bridge T] with f hf
  apply ContinuousMap.ext
  intro t
  exact hf (min t T)

/-- Complete continuous path-space law equality for the actual bridge
under every fixed cyclic shift in [0,T], including endpoints. -/
theorem pathLaw_cyclicBridgePath_eq_stoppedBridgePath (T s : ℝ≥0)
    (hT : 0 < T) (hs : s ≤ T) :
    pathLaw.map (cyclicBridgePath T hT s) = pathLaw.map (stoppedBridgePath T) := by
  apply rationalEval_measurableEmbedding.map_injective
  rw [Measure.map_map continuous_rationalEval.measurable (measurable_cyclicBridgePath T hT s),
    Measure.map_map continuous_rationalEval.measurable (measurable_stoppedBridgePath T)]
  change pathLaw.map (fun f : Path ↦ fun q ↦ cyclicValue T s (min (rationalTimeReal q) T) f) = _
  have he : (fun f : Path ↦ fun q ↦ cyclicValue T s (min (rationalTimeReal q) T) f) =ᵐ[pathLaw]
      (fun f : Path ↦ fun q ↦ rotation T s (min (rationalTimeReal q) T) f) := by
    filter_upwards [ae_cyclicValue_eq_rotation T s] with f hf
    exact funext (fun q ↦ hf _)
  rw [Measure.map_congr he]
  exact indexed_rotation_law T s hT hs (fun q ↦ min (rationalTimeReal q) T)
    (fun _ ↦ min_le_right _ _)

theorem pathLaw_cyclicBridgePath_eq_closed (T s : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) :
    pathLaw.map (cyclicBridgePath T hT s) = pathLaw.map (stoppedClosedBridgePath T) := by
  rw [Measure.map_congr (ae_stoppedClosedBridgePath_eq_stoppedBridgePath T)]
  exact pathLaw_cyclicBridgePath_eq_stoppedBridgePath T s hT hs

theorem closedBridge_stoppedBridgePath (T : ℝ≥0) (hT : 0 < T) (t : ℝ≥0)
    (ht : t ≤ T) (f : Path) :
    closedBridge T t (stoppedBridgePath T f) = closedBridge T t f := by
  change bridge T t (stoppedBridgePath T f)-(1-(t : ℝ)/(T : ℝ))*(stoppedBridgePath T f) 0 = _
  have h0 : (stoppedBridgePath T f) 0 = f 0 := by
    change bridge T (min 0 T) f = f 0
    simp [bridge]
  have he : (stoppedBridgePath T f) T = 0 := by
    change bridge T (min T T) f = 0
    simpa only [min_self] using bridge_endpoint_zero T hT f
  have ht' : (stoppedBridgePath T f) t = bridge T t f := by
    change bridge T (min t T) f = _
    rw [min_eq_left ht]
  unfold bridge closedBridge
  rw [ht',h0,he]
  ring

theorem cyclicBridgePath_stoppedBridgePath (T s : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (f : Path) :
    cyclicBridgePath T hT s (stoppedBridgePath T f) = cyclicBridgePath T hT s f := by
  apply ContinuousMap.ext
  intro t
  change cyclicValue T s (min t T) (stoppedBridgePath T f) = cyclicValue T s (min t T) f
  unfold cyclicValue
  rw [closedBridge_stoppedBridgePath T hT _ (cycleTime_le T s _ hs (min_le_right _ _)),
    closedBridge_stoppedBridgePath T hT s hs]

def bridgePathLaw (T : ℝ≥0) : Measure Path := pathLaw.map (stoppedBridgePath T)

instance (T : ℝ≥0) : IsProbabilityMeasure (bridgePathLaw T) :=
  Measure.isProbabilityMeasure_map (measurable_stoppedBridgePath T).aemeasurable

/-- Cyclic shift invariance expressed as a genuine pushforward of the
actual pinned bridge probability law itself. -/
theorem bridgePathLaw_cyclic_invariant (T s : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) :
    (bridgePathLaw T).map (cyclicBridgePath T hT s) = bridgePathLaw T := by
  unfold bridgePathLaw
  rw [Measure.map_map (measurable_cyclicBridgePath T hT s) (measurable_stoppedBridgePath T)]
  have he : cyclicBridgePath T hT s ∘ stoppedBridgePath T = cyclicBridgePath T hT s :=
    funext (cyclicBridgePath_stoppedBridgePath T s hT hs)
  rw [he]
  exact pathLaw_cyclicBridgePath_eq_stoppedBridgePath T s hT hs

end PerronWright.BrownianBridgeCyclicPathLaw
