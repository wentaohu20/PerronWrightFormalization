import PerronWright.Probability.BrownianBridgeUniqueMinimum
import PerronWright.Probability.ContinuousPathPositiveInterior

/-! # The actual minimum-shifted bridge is strictly positive inside

The actual Gaussian bridge minimum uniqueness is proved in the imported
leaf, not assumed here. An interior cyclic offset cannot return to the
minimum time, so its value is strictly above the minimum. This proves
positivity of the genuine measurable minimum-shift law. It does not
identify that law with a conditioned Brownian excursion or a Palm law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBridgeMinimumStrictPositivity

open BrownianPathLaw BrownianBridgeCyclicPath BrownianBridgeCycleKernel
open BrownianBridgeMinimumShift BrownianBridgeUniqueMinimum ContinuousPathPositiveInterior

theorem cycleTime_ne_origin (T s t : ℝ≥0) (ht : 0 < t) (htT : t < T) :
    cycleTime T s t ≠ s := by
  intro he
  unfold cycleTime at he
  split_ifs at he with h
  · have hr := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) he
    simp only [NNReal.coe_add] at hr
    have hp : 0 < (t : ℝ) := ht
    linarith
  · have hr := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) he
    rw [NNReal.coe_sub (le_of_lt (lt_of_not_ge h)),NNReal.coe_add] at hr
    have hp : (t : ℝ) < T := htT
    linarith

theorem ae_minimumShiftPath_strictly_positive (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, ∀ t : ℝ≥0, 0 < t → t < T → 0 < minimumShiftPath T hT f t := by
  filter_upwards [ae_closedBridge_unique_minimum T hT] with f huniq
  intro t ht htT
  have hct : cycleTime T (bridgeMinimumTime T f) t ≤ T :=
    cycleTime_le T _ _ (bridgeMinimumTime_le T f) htT.le
  have hne : cycleTime T (bridgeMinimumTime T f) t ≠ bridgeMinimumTime T f :=
    cycleTime_ne_origin T _ t ht htT
  have hval : closedBridge T (cycleTime T (bridgeMinimumTime T f) t) f ≠ bridgeMinimumValue T f :=
    fun he ↦ hne (huniq _ hct he)
  have hp : bridgeMinimumValue T f < closedBridge T (cycleTime T (bridgeMinimumTime T f) t) f :=
    lt_of_le_of_ne (bridgeMinimumValue_le T f _ hct) hval.symm
  change 0 < cyclicValue T (bridgeMinimumTime T f) (min t T) f
  rw [min_eq_left htT.le]
  unfold cyclicValue
  rw [bridgeMinimumTime_value]
  exact sub_pos.mpr hp

theorem ae_minimumShiftLaw_strictly_positive (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂minimumShiftLaw T hT, ∀ t : ℝ≥0, 0 < t → t < T → 0 < f t := by
  exact (ae_map_iff (measurable_minimumShiftPath T hT).aemeasurable
    (measurableSet_positiveInterior T)).mpr (ae_minimumShiftPath_strictly_positive T hT)

theorem minimumShiftLaw_positiveInterior_measure_one (T : ℝ≥0) (hT : 0 < T) :
    minimumShiftLaw T hT (positiveInterior T) = 1 := by
  have hs : positiveInterior T =ᵐ[minimumShiftLaw T hT] Set.univ := by
    filter_upwards [ae_minimumShiftLaw_strictly_positive T hT] with f hf
    exact propext ⟨fun _ ↦ Set.mem_univ f,fun _ ↦ hf⟩
  rw [measure_congr hs,measure_univ]

end PerronWright.BrownianBridgeMinimumStrictPositivity
