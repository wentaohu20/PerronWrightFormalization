import PerronWright.Probability.ContinuousPathMinimumScaling
import PerronWright.Probability.BrownianBridgeCyclicGeometry

/-! # Genuine measurable earliest-minimum cyclic transform

The time is the proved measurable least minimizer of the actual closed
bridge on [0,T], not an assumed selector. The stopped cyclic path map
is measurable jointly with a positive horizon and is nonnegative with
zero endpoints for every input path. Its law is the actual Brownian
path-law pushforward. No positive-excursion distribution, unique-minimum
property or Vervaat distributional identity is presumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeMinimumShift

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeCycleKernel
open BrownianBridgeCyclicPath BrownianBridgeCyclicGeometry
open ContinuousPathLeastMinimum ContinuousPathMinimumScaling BrownianGaussianSkeleton

theorem measurable_variable_closedBridge {Ω : Type*} [MeasurableSpace Ω]
    (T t : Ω → ℝ≥0) (F : Ω → Path) (hT : Measurable T) (ht : Measurable t) (hF : Measurable F) :
    Measurable (fun w ↦ closedBridge (T w) (t w) (F w)) := by
  unfold closedBridge bridge
  have he := continuous_joint_eval.measurable
  have hc := NNReal.continuous_coe.measurable
  exact ((he.comp (hF.prodMk ht)).sub
    (((hc.comp ht).div (hc.comp hT)).mul (he.comp (hF.prodMk hT)))).sub
    ((measurable_const.sub ((hc.comp ht).div (hc.comp hT))).mul
      (he.comp (hF.prodMk measurable_const)))

theorem measurable_joint_stoppedClosedBridgePath :
    Measurable (fun p : ℝ≥0 × Path ↦ stoppedClosedBridgePath p.1 p.2) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun p : ℝ≥0 × Path ↦ fun q ↦ closedBridge p.1 (min (rationalTimeReal q) p.1) p.2)
  exact measurable_pi_lambda _ (fun _ ↦ measurable_variable_closedBridge _ _ _
    measurable_fst (measurable_const.min measurable_fst) measurable_snd)

def bridgeMinimumTime (T : ℝ≥0) (f : Path) : ℝ≥0 :=
  leastMinimizer T (stoppedClosedBridgePath T f)

def bridgeMinimumValue (T : ℝ≥0) (f : Path) : ℝ :=
  minimumValue T (stoppedClosedBridgePath T f)

theorem bridgeMinimumTime_le (T : ℝ≥0) (f : Path) : bridgeMinimumTime T f ≤ T :=
  leastMinimizer_le_time T (stoppedClosedBridgePath T f)

theorem bridgeMinimumTime_value (T : ℝ≥0) (f : Path) :
    closedBridge T (bridgeMinimumTime T f) f = bridgeMinimumValue T f := by
  have h := leastMinimizer_value T (stoppedClosedBridgePath T f)
  change closedBridge T (min (bridgeMinimumTime T f) T) f = _ at h
  simpa only [min_eq_left (bridgeMinimumTime_le T f),bridgeMinimumValue] using h

theorem bridgeMinimumValue_le (T : ℝ≥0) (f : Path) (t : ℝ≥0) (ht : t ≤ T) :
    bridgeMinimumValue T f ≤ closedBridge T t f := by
  have h := minimumValue_le T (stoppedClosedBridgePath T f) t ht
  change bridgeMinimumValue T f ≤ closedBridge T (min t T) f at h
  simpa only [min_eq_left ht] using h

theorem bridgeMinimumTime_le_of_eq (T : ℝ≥0) (f : Path) (t : ℝ≥0)
    (ht : t ≤ T) (he : closedBridge T t f = bridgeMinimumValue T f) :
    bridgeMinimumTime T f ≤ t := by
  apply leastMinimizer_le T (stoppedClosedBridgePath T f) t ht
  change closedBridge T (min t T) f = _
  simpa only [min_eq_left ht,bridgeMinimumValue] using he

theorem measurable_joint_bridgeMinimumTime :
    Measurable (fun p : ℝ≥0 × Path ↦ bridgeMinimumTime p.1 p.2) :=
  measurable_joint_leastMinimizer.comp (measurable_fst.prodMk measurable_joint_stoppedClosedBridgePath)

theorem measurable_joint_bridgeMinimumValue :
    Measurable (fun p : ℝ≥0 × Path ↦ bridgeMinimumValue p.1 p.2) :=
  continuous_joint_minimumValue.measurable.comp
    (measurable_fst.prodMk measurable_joint_stoppedClosedBridgePath)

theorem measurable_bridgeMinimumTime (T : ℝ≥0) : Measurable (bridgeMinimumTime T) :=
  measurable_joint_bridgeMinimumTime.comp (measurable_const.prodMk measurable_id)

theorem measurable_bridgeMinimumValue (T : ℝ≥0) : Measurable (bridgeMinimumValue T) :=
  measurable_joint_bridgeMinimumValue.comp (measurable_const.prodMk measurable_id)

theorem measurable_variable_cyclicBridgePath {Ω : Type*} [MeasurableSpace Ω]
    (T s : Ω → ℝ≥0) (F : Ω → Path) (hT : Measurable T) (hs : Measurable s) (hF : Measurable F)
    (hp : ∀ w, 0 < T w) :
    Measurable (fun w ↦ cyclicBridgePath (T w) (hp w) (s w) (F w)) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun w ↦ fun q ↦ cyclicValue (T w) (s w) (min (rationalTimeReal q) (T w)) (F w))
  apply measurable_pi_lambda
  intro q
  let t : Ω → ℝ≥0 := fun w ↦ min (rationalTimeReal q) (T w)
  have ht : Measurable t := measurable_const.min hT
  have hc : Measurable (fun w ↦ cycleTime (T w) (s w) (t w)) := by
    unfold cycleTime
    exact Measurable.ite (measurableSet_le (hs.add ht) hT) (hs.add ht) ((hs.add ht).sub hT)
  exact (measurable_variable_closedBridge T _ F hT hc hF).sub
    (measurable_variable_closedBridge T s F hT hs hF)

def minimumShiftPath (T : ℝ≥0) (hT : 0 < T) (f : Path) : Path :=
  cyclicBridgePath T hT (bridgeMinimumTime T f) f

theorem measurable_minimumShiftPath (T : ℝ≥0) (hT : 0 < T) :
    Measurable (minimumShiftPath T hT) :=
  measurable_variable_cyclicBridgePath _ _ _ measurable_const (measurable_bridgeMinimumTime T)
    measurable_id (fun _ ↦ hT)

/-- True joint measurable minimum transform on the actual positive
duration and continuous-path spaces, including paths with nonunique minima. -/
theorem measurable_joint_minimumShiftPath :
    Measurable (fun p : {T : ℝ≥0 // 0 < T} × Path ↦ minimumShiftPath p.1.val p.1.property p.2) := by
  have hT : Measurable (fun p : {T : ℝ≥0 // 0 < T} × Path ↦ p.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  exact measurable_variable_cyclicBridgePath _ _ _ hT
    (measurable_joint_bridgeMinimumTime.comp (hT.prodMk measurable_snd)) measurable_snd
    (fun p ↦ p.1.property)

theorem minimumShiftPath_nonnegative (T : ℝ≥0) (hT : 0 < T) (f : Path) (t : ℝ≥0) :
    0 ≤ minimumShiftPath T hT f t := by
  apply cyclicBridgePath_nonneg_of_minimizer T _ hT (bridgeMinimumTime_le T f) f _ t
  intro s hs
  rw [bridgeMinimumTime_value]
  exact bridgeMinimumValue_le T f s hs

theorem minimumShiftPath_zero (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    minimumShiftPath T hT f 0 = 0 :=
  cyclicBridgePath_zero T hT _ (bridgeMinimumTime_le T f) f

theorem minimumShiftPath_endpoint (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    minimumShiftPath T hT f T = 0 := cyclicBridgePath_endpoint T hT _ f

theorem minimumShiftPath_stopped (T : ℝ≥0) (hT : 0 < T) (f : Path) (t : ℝ≥0) (ht : T ≤ t) :
    minimumShiftPath T hT f t = 0 := cyclicBridgePath_stopped T hT _ f t ht

def minimumShiftLaw (T : ℝ≥0) (hT : 0 < T) : Measure Path := pathLaw.map (minimumShiftPath T hT)

instance (T : ℝ≥0) (hT : 0 < T) : IsProbabilityMeasure (minimumShiftLaw T hT) :=
  Measure.isProbabilityMeasure_map (measurable_minimumShiftPath T hT).aemeasurable

theorem hasLaw_minimumShiftPath (T : ℝ≥0) (hT : 0 < T) :
    HasLaw (minimumShiftPath T hT) (minimumShiftLaw T hT) pathLaw :=
  ⟨(measurable_minimumShiftPath T hT).aemeasurable,rfl⟩

theorem ae_minimumShiftLaw_nonnegative (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂minimumShiftLaw T hT, ∀ t : ℝ≥0, 0 ≤ f t := by
  apply (ae_map_iff (measurable_minimumShiftPath T hT).aemeasurable _).mpr
  · exact Eventually.of_forall (fun f t ↦ minimumShiftPath_nonnegative T hT f t)
  · have he : {f : Path | ∀ t : ℝ≥0, 0 ≤ f t} = ⋂ t : ℝ≥0, {f : Path | 0 ≤ f t} := by
      ext f
      simp only [mem_ofPred_eq,mem_iInter]
    rw [he]
    exact (isClosed_iInter (fun t ↦ isClosed_le continuous_const (continuous_eval t))).measurableSet

end PerronWright.BrownianBridgeMinimumShift
