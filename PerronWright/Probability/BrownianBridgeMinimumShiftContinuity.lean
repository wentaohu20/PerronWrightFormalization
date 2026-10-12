import PerronWright.Probability.ContinuousPathUniqueMinimumContinuity
import PerronWright.Probability.BrownianBridgeUniqueMinimum

/-! # Actual minimum-shift continuity at the Brownian bridge

The cyclic path map is jointly continuous despite the splice, since the
two values agree at the seam of a closed bridge. The genuine least
minimum selector is continuous at every uniquely minimized closed path.
The actual Brownian bridge uniqueness theorem discharges that condition
almost everywhere. No excursion distributional identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBridgeMinimumShiftContinuity

open BrownianPathLaw BrownianBridgeCyclicPath BrownianBridgeCyclicGeometry
open BrownianBridgeCycleKernel BrownianBridgeMinimumShift BrownianBridgeUniqueMinimum
open ContinuousPathUniqueMinimumContinuity

theorem continuous_stoppedClosedBridgePath (T : ℝ≥0) :
    Continuous (stoppedClosedBridgePath T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_joint_closedBridge T).comp
    (continuous_fst.prodMk (continuous_snd.min continuous_const))

theorem continuous_joint_cyclicValue (T : ℝ≥0) (hT : 0 < T) :
    Continuous (fun p : (ℝ≥0 × Path) × ℝ≥0 ↦ cyclicValue T p.1.1 p.2 p.1.2) := by
  have hp : Continuous (fun p : (ℝ≥0 × Path) × ℝ≥0 ↦ p.1.1 + p.2) :=
    continuous_fst.fst.add continuous_snd
  have hm : Continuous (fun p : (ℝ≥0 × Path) × ℝ≥0 ↦ p.1.1 + p.2 - T) :=
    hp.sub continuous_const
  have he : Continuous (fun p : (ℝ≥0 × Path) × ℝ≥0 ↦ closedBridge T p.1.1 p.1.2) :=
    (continuous_joint_closedBridge T).comp (continuous_fst.snd.prodMk continuous_fst.fst)
  have hl := ((continuous_joint_closedBridge T).comp
    (continuous_fst.snd.prodMk hp)).sub he
  have hr := ((continuous_joint_closedBridge T).comp
    (continuous_fst.snd.prodMk hm)).sub he
  have hc := hl.if_le hr hp (continuous_const : Continuous (fun _ ↦ T)) (fun p hs ↦ by
    change closedBridge T (p.1.1 + p.2) p.1.2 - closedBridge T p.1.1 p.1.2 =
      closedBridge T (p.1.1 + p.2 - T) p.1.2 - closedBridge T p.1.1 p.1.2
    simp only [hs,tsub_self,closedBridge_zero,closedBridge_endpoint T hT p.1.2])
  apply hc.congr
  intro p
  dsimp only [cyclicValue,cycleTime]
  split_ifs <;> rfl

theorem continuous_joint_cyclicBridgePath (T : ℝ≥0) (hT : 0 < T) :
    Continuous (fun p : ℝ≥0 × Path ↦ cyclicBridgePath T hT p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_joint_cyclicValue T hT).comp
    (continuous_fst.prodMk (continuous_snd.min continuous_const))

theorem continuousAt_bridgeMinimumTime_of_unique (T : ℝ≥0) (f : Path)
    (hunique : ∀ t : ℝ≥0, t ≤ T → closedBridge T t f = bridgeMinimumValue T f →
      t = bridgeMinimumTime T f) :
    ContinuousAt (bridgeMinimumTime T) f := by
  have hu : ∀ t : ℝ≥0, t ≤ T →
      stoppedClosedBridgePath T f t =
        ContinuousPathLeastMinimum.minimumValue T (stoppedClosedBridgePath T f) →
      t = ContinuousPathLeastMinimum.leastMinimizer T (stoppedClosedBridgePath T f) := by
    intro t ht he
    apply hunique t ht
    change closedBridge T (min t T) f = bridgeMinimumValue T f at he
    rwa [min_eq_left ht] at he
  exact (continuousAt_leastMinimizer_of_unique T _ hu).comp
    (continuous_stoppedClosedBridgePath T).continuousAt

theorem continuousAt_minimumShiftPath_of_unique (T : ℝ≥0) (hT : 0 < T) (f : Path)
    (hunique : ∀ t : ℝ≥0, t ≤ T → closedBridge T t f = bridgeMinimumValue T f →
      t = bridgeMinimumTime T f) :
    ContinuousAt (minimumShiftPath T hT) f :=
  (continuous_joint_cyclicBridgePath T hT).continuousAt.comp
    ((continuousAt_bridgeMinimumTime_of_unique T f hunique).prodMk continuousAt_id)

theorem ae_continuousAt_minimumShiftPath (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, ContinuousAt (minimumShiftPath T hT) f := by
  filter_upwards [ae_closedBridge_unique_minimum T hT] with f hf
  exact continuousAt_minimumShiftPath_of_unique T hT f hf

end PerronWright.BrownianBridgeMinimumShiftContinuity
