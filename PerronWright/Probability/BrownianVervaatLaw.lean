import PerronWright.Probability.BrownianMinimumShiftEntranceIdentification
import PerronWright.Probability.BrownianPositiveBridgePathConvergence
import PerronWright.Probability.BrownianBridgeMinimumOccupationBias

/-! # Genuine Vervaat continuous-path law and conditioned-bridge limit

The actual minimum-shift law is identified with the constructed entrance
continuous-path probability. The existing actual positive-bridge path
limit and the exact uniform-minimum-time and occupation identities are
therefore identities for this same law, with no identification premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section

namespace PerronWright.BrownianVervaatLaw

open BrownianPathLaw BrownianBridgeMinimumShift BrownianMinimumShiftEntranceIdentification
open BrownianBridgeCyclicPathLaw BrownianBridgeMinimumUniformProduct BrownianCircleUniformTime
open BrownianBridgeMinimumUniformTests BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeWeakClusterSupport BrownianPositiveBridgePathConvergence
open BrownianBridgeMinimumTimeWeakLimit BrownianBridgeMinimumOccupationBias

theorem hasLaw_actual_minimumShift_entrance (T : ℝ≥0) (hT : 0 < T) :
    HasLaw (minimumShiftPath T hT) (BrownianEntranceContinuousRealization.pathLaw T hT)
      BrownianPathLaw.pathLaw := by
  rw [← actual_minimumShiftLaw_eq_entrance T hT]
  exact hasLaw_minimumShiftPath T hT

theorem actual_bridge_minimumShift_entrance (T : ℝ≥0) (hT : 0 < T) :
    (bridgePathLaw T).map (minimumShiftPath T hT) =
      BrownianEntranceContinuousRealization.pathLaw T hT := by
  rw [bridgePathLaw_minimumShiftPath_map_eq,actual_minimumShiftLaw_eq_entrance]

theorem actual_bridge_minimumTime_entrance_product (T : ℝ≥0) (hT : 0 < T) :
    (bridgePathLaw T).map (realMinimumJointMap T hT) =
      (intervalUniform (T : ℝ)).prod (BrownianEntranceContinuousRealization.pathLaw T hT) := by
  rw [bridgePathLaw_realMinimumJointMap_eq,actual_minimumShiftLaw_eq_entrance]

private theorem entranceProbability_eq_minimumShiftProbability (T : ℝ≥0) (hT : 0 < T) :
    entranceProbability T hT = minimumShiftProbability T hT :=
  Subtype.ext (actual_minimumShiftLaw_eq_entrance T hT).symm

theorem tendsto_actual_positiveBridgeProbability_minimumShift (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (bridgeProbability T hT) (𝓝[>] 0) (𝓝 (minimumShiftProbability T hT)) := by
  rw [← entranceProbability_eq_minimumShiftProbability]
  exact tendsto_positiveBridgeProbability T hT

theorem tendsto_actual_positiveBridge_minimumShift_lintegral (T : ℝ≥0) (hT : 0 < T)
    (Ψ : Path →ᵇ ℝ≥0) :
    Tendsto (fun a : ℝ ↦ ∫⁻ f, (Ψ f : ℝ≥0∞) ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (∫⁻ f, (Ψ f : ℝ≥0∞) ∂minimumShiftLaw T hT)) := by
  rw [actual_minimumShiftLaw_eq_entrance]
  exact tendsto_actual_positiveBridge_bounded_lintegral T hT Ψ

theorem tendsto_actual_positiveBridge_minimumShift_integral (T : ℝ≥0) (hT : 0 < T)
    (Ψ : Path →ᵇ ℝ) :
    Tendsto (fun a : ℝ ↦ ∫ f, Ψ f ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (∫ f, Ψ f ∂minimumShiftLaw T hT)) := by
  rw [actual_minimumShiftLaw_eq_entrance]
  exact tendsto_actual_positiveBridge_bounded_integral T hT Ψ

theorem actual_positiveBridge_minimumShift_occupation_bias (a : ℝ) (ha : 0 < a)
    (T : ℝ≥0) (hT : 0 < T) :
    (positiveBridgeLaw a T).map (minimumShiftPath T hT) =
      (BrownianEntranceContinuousRealization.pathLaw T hT).withDensity (occupationDensity T a) := by
  rw [← actual_minimumShiftLaw_eq_entrance]
  exact actual_minimumShiftLaw_eq_occupation_bias a ha T hT

end PerronWright.BrownianVervaatLaw
