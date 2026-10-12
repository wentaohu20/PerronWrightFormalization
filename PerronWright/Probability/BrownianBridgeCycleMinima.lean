import PerronWright.Probability.BrownianBridgeMinimumShift

/-! # Actual cyclic minimum events have equal probabilities

The literal cyclic time map covers every closed-bridge value. Thus its
nonnegative-path event is precisely that the starting point is a global
minimum. The proved actual whole-path cyclic law, not an invariance
assumption, gives equality of every fixed minimum-event probability.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBridgeCycleMinima

open BrownianPathLaw BrownianBridgeCycleKernel BrownianBridgeCyclicPath
open BrownianBridgeCyclicGeometry BrownianBridgeCyclicPathLaw BrownianBridgeMinimumShift

theorem cycle_closedBridge_value_covers (T s u : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (hu : u ≤ T) (f : Path) :
    ∃ t : ℝ≥0, t ≤ T ∧ closedBridge T (cycleTime T s t) f = closedBridge T u f := by
  by_cases hsu : s ≤ u
  · refine ⟨u-s,(tsub_le_self).trans hu,?_⟩
    have he : s+(u-s)=u := add_tsub_cancel_of_le hsu
    simp only [cycleTime,he,if_pos hu]
  · refine ⟨T-s+u,?_,?_⟩
    · calc T-s+u ≤ T-s+s := by gcongr; exact le_of_lt (lt_of_not_ge hsu)
        _ = T := by rw [add_comm]; exact add_tsub_cancel_of_le hs
    · have he : s+(T-s+u)=T+u := by rw [← add_assoc,add_tsub_cancel_of_le hs]
      by_cases hu0 : u=0
      · subst u
        have hsum : s+(T-s)=T := add_tsub_cancel_of_le hs
        simp only [add_zero,cycleTime,hsum,le_refl,if_true,closedBridge_zero,closedBridge_endpoint T hT f]
      · have hnu : ¬T+u ≤ T := by have hp : 0 < u := pos_iff_ne_zero.mpr hu0; linarith
        simp only [cycleTime,he,if_neg hnu,add_tsub_cancel_left]

def fixedMinimumEvent (T s : ℝ≥0) : Set Path :=
  {f | bridgeMinimumValue T f = closedBridge T s f}

theorem measurableSet_fixedMinimumEvent (T s : ℝ≥0) : MeasurableSet (fixedMinimumEvent T s) :=
  measurableSet_eq_fun (measurable_bridgeMinimumValue T) (continuous_closedBridge T s).measurable

def nonnegativePaths : Set Path := {f | ∀ t : ℝ≥0, 0 ≤ f t}

theorem measurableSet_nonnegativePaths : MeasurableSet nonnegativePaths := by
  have he : nonnegativePaths = ⋂ t : ℝ≥0, {f : Path | 0 ≤ f t} := by
    ext f
    simp only [nonnegativePaths,mem_ofPred_eq,mem_iInter]
  rw [he]
  exact (isClosed_iInter (fun t ↦ isClosed_le continuous_const (continuous_eval t))).measurableSet

theorem cyclicBridgePath_nonnegative_iff_minimum (T s : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (f : Path) :
    cyclicBridgePath T hT s f ∈ nonnegativePaths ↔ f ∈ fixedMinimumEvent T s := by
  constructor
  · intro h
    apply le_antisymm (bridgeMinimumValue_le T f s hs)
    obtain ⟨t,ht,he⟩ := cycle_closedBridge_value_covers T s (bridgeMinimumTime T f) hT hs
      (bridgeMinimumTime_le T f) f
    have hv := h t
    change 0 ≤ closedBridge T (cycleTime T s (min t T)) f-closedBridge T s f at hv
    rw [min_eq_left ht,he,bridgeMinimumTime_value] at hv
    exact sub_nonneg.mp hv
  · intro h
    apply cyclicBridgePath_nonneg_of_minimizer T s hT hs f
    intro t ht
    change bridgeMinimumValue T f = closedBridge T s f at h
    rw [← h]
    exact bridgeMinimumValue_le T f t ht

theorem cyclicBridgePath_zero_eq_closed (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    cyclicBridgePath T hT 0 f = stoppedClosedBridgePath T f := by
  apply ContinuousMap.ext
  intro t
  change closedBridge T (cycleTime T 0 (min t T)) f-closedBridge T 0 f = closedBridge T (min t T) f
  simp only [cycleTime,zero_add,if_pos (min_le_right _ _),closedBridge_zero,sub_zero]

theorem fixedMinimumEvent_measure_eq (T s : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) :
    pathLaw (fixedMinimumEvent T s) = pathLaw (fixedMinimumEvent T 0) := by
  have he := congrArg (fun m : Measure Path ↦ m nonnegativePaths)
    (pathLaw_cyclicBridgePath_eq_closed T s hT hs)
  rw [Measure.map_apply (measurable_cyclicBridgePath T hT s) measurableSet_nonnegativePaths,
    Measure.map_apply (measurable_stoppedClosedBridgePath T) measurableSet_nonnegativePaths] at he
  have hl : (cyclicBridgePath T hT s) ⁻¹' nonnegativePaths = fixedMinimumEvent T s := by
    ext f
    exact cyclicBridgePath_nonnegative_iff_minimum T s hT hs f
  have hr : (stoppedClosedBridgePath T) ⁻¹' nonnegativePaths = fixedMinimumEvent T 0 := by
    ext f
    change stoppedClosedBridgePath T f ∈ nonnegativePaths ↔ f ∈ fixedMinimumEvent T 0
    rw [← cyclicBridgePath_zero_eq_closed T hT f]
    exact cyclicBridgePath_nonnegative_iff_minimum T 0 hT zero_le f
  rwa [hl,hr] at he

end PerronWright.BrownianBridgeCycleMinima
