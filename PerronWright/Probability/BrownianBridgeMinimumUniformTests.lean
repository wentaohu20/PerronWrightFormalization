import PerronWright.Probability.BrownianBridgeMinimumUniformProduct

/-! # Literal uniform probabilities and full bridge-law product tests

The same true product law is proved under the actual stopped bridge
law, not only under its Brownian source. Tonelli gives arbitrary Borel
nonnegative joint tests and the explicit normalized Lebesgue factor.
No positive-excursion conditioning or area-moment identity is inferred.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeMinimumUniformTests

open BrownianPathLaw BrownianBridgeMinimumShift BrownianBridgeMinimumRotationLaw
open BrownianBridgeCyclicPathLaw BrownianBridgeAreaTiltPathLaw
open BrownianCircleUniformTime BrownianBridgeMinimumUniformProduct

theorem bridgePathLaw_realMinimumJointMap_eq (T : ℝ≥0) (hT : 0 < T) :
    (bridgePathLaw T).map (realMinimumJointMap T hT) =
      (intervalUniform (T : ℝ)).prod (minimumShiftLaw T hT) := by
  rw [bridgePathLaw,Measure.map_map (measurable_realMinimumJointMap T hT) (measurable_stoppedBridgePath T)]
  have he : realMinimumJointMap T hT ∘ stoppedBridgePath T = realMinimumJointMap T hT := by
    funext f
    apply Prod.ext
    · exact congrArg (fun t : ℝ≥0 ↦ (t : ℝ)) (bridgeMinimumTime_stoppedBridgePath T hT f)
    · exact minimumShiftPath_stoppedBridgePath T hT f
  rw [he]
  exact realMinimumJointLaw_eq_uniform_prod T hT

theorem bridgePathLaw_minimumTime_map_eq_uniform (T : ℝ≥0) (hT : 0 < T) :
    (bridgePathLaw T).map (fun f ↦ (bridgeMinimumTime T f : ℝ)) = intervalUniform (T : ℝ) := by
  rw [bridgePathLaw,Measure.map_map
    (show Measurable (fun f ↦ (bridgeMinimumTime T f : ℝ)) from
      NNReal.continuous_coe.measurable.comp (measurable_bridgeMinimumTime T)) (measurable_stoppedBridgePath T)]
  have he : (fun f ↦ (bridgeMinimumTime T f : ℝ)) ∘ stoppedBridgePath T =
      (fun f ↦ (bridgeMinimumTime T f : ℝ)) := by
    funext f
    exact congrArg (fun t : ℝ≥0 ↦ (t : ℝ)) (bridgeMinimumTime_stoppedBridgePath T hT f)
  rw [he]
  exact minimumTime_real_map_eq_uniform T hT

theorem bridgePathLaw_minimumShiftPath_map_eq (T : ℝ≥0) (hT : 0 < T) :
    (bridgePathLaw T).map (minimumShiftPath T hT) = minimumShiftLaw T hT := by
  rw [bridgePathLaw,Measure.map_map (measurable_minimumShiftPath T hT) (measurable_stoppedBridgePath T)]
  have he : minimumShiftPath T hT ∘ stoppedBridgePath T = minimumShiftPath T hT :=
    funext (minimumShiftPath_stoppedBridgePath T hT)
  rw [he]
  rfl

theorem bridgePathLaw_minimumTime_real_indep_minimumShiftPath (T : ℝ≥0) (hT : 0 < T) :
    IndepFun (fun f ↦ (bridgeMinimumTime T f : ℝ)) (minimumShiftPath T hT) (bridgePathLaw T) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (NNReal.continuous_coe.measurable.comp (measurable_bridgeMinimumTime T)).aemeasurable
    (measurable_minimumShiftPath T hT).aemeasurable).mpr
  change (bridgePathLaw T).map (fun f ↦ ((bridgeMinimumTime T f : ℝ),minimumShiftPath T hT f)) =
    ((bridgePathLaw T).map (fun f ↦ (bridgeMinimumTime T f : ℝ))).prod
      ((bridgePathLaw T).map (minimumShiftPath T hT))
  rw [bridgePathLaw_minimumTime_map_eq_uniform T hT,bridgePathLaw_minimumShiftPath_map_eq T hT]
  exact bridgePathLaw_realMinimumJointMap_eq T hT

theorem bridgePathLaw_minimumTime_indep_minimumShiftPath (T : ℝ≥0) (hT : 0 < T) :
    IndepFun (bridgeMinimumTime T) (minimumShiftPath T hT) (bridgePathLaw T) := by
  have he := (bridgePathLaw_minimumTime_real_indep_minimumShiftPath T hT).comp
    continuous_real_toNNReal.measurable (measurable_id (α := Path))
  simpa only [Function.comp_def,Real.toNNReal_coe,id_eq] using he

theorem intervalUniform_Ioc (T : ℝ) (a b : ℝ) (ha : 0 ≤ a) (_hab : a ≤ b) (hb : b ≤ T) :
    intervalUniform T (Ioc a b) = (ENNReal.ofReal T)⁻¹ * ENNReal.ofReal (b-a) := by
  have hsub : Ioc a b ⊆ Ioc 0 T := fun _ hx ↦ ⟨ha.trans_lt hx.1,hx.2.trans hb⟩
  rw [intervalUniform,Measure.smul_apply,Measure.restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr hsub,Real.volume_Ioc,smul_eq_mul]

theorem minimumTime_Ioc_probability (T : ℝ≥0) (hT : 0 < T) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (T : ℝ)) :
    pathLaw {f | (bridgeMinimumTime T f : ℝ) ∈ Ioc a b} =
      (ENNReal.ofReal (T : ℝ))⁻¹ * ENNReal.ofReal (b-a) := by
  rw [(hasLaw_minimumTime_real_uniform T hT).measure_eq (p := fun x ↦ x ∈ Ioc a b) measurableSet_Ioc]
  exact intervalUniform_Ioc (T : ℝ) a b ha hab hb

theorem lintegral_minimum_joint_eq_uniform (T : ℝ≥0) (hT : 0 < T)
    (Ψ : ℝ × Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ ((bridgeMinimumTime T f : ℝ),minimumShiftPath T hT f) ∂pathLaw) =
      (ENNReal.ofReal (T : ℝ))⁻¹ *
        ∫⁻ s in Ioc 0 (T : ℝ), ∫⁻ e, Ψ (s,e) ∂minimumShiftLaw T hT := by
  let : Fact (0 < (T : ℝ)) := ⟨hT⟩
  change (∫⁻ f, Ψ (realMinimumJointMap T hT f) ∂pathLaw) = _
  rw [← lintegral_map hΨ (measurable_realMinimumJointMap T hT),
    ← realMinimumJointLaw,realMinimumJointLaw_eq_uniform_prod T hT,
    lintegral_prod Ψ hΨ.aemeasurable,intervalUniform,lintegral_smul_measure,smul_eq_mul]

theorem lintegral_bridgePathLaw_minimum_joint_eq_uniform (T : ℝ≥0) (hT : 0 < T)
    (Ψ : ℝ × Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ ((bridgeMinimumTime T f : ℝ),minimumShiftPath T hT f) ∂bridgePathLaw T) =
      (ENNReal.ofReal (T : ℝ))⁻¹ *
        ∫⁻ s in Ioc 0 (T : ℝ), ∫⁻ e, Ψ (s,e) ∂minimumShiftLaw T hT := by
  let : Fact (0 < (T : ℝ)) := ⟨hT⟩
  change (∫⁻ f, Ψ (realMinimumJointMap T hT f) ∂bridgePathLaw T) = _
  rw [← lintegral_map hΨ (measurable_realMinimumJointMap T hT),
    bridgePathLaw_realMinimumJointMap_eq T hT,lintegral_prod Ψ hΨ.aemeasurable,
    intervalUniform,lintegral_smul_measure,smul_eq_mul]

end PerronWright.BrownianBridgeMinimumUniformTests
