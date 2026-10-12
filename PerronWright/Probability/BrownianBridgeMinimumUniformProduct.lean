import PerronWright.Probability.BrownianBridgeMinimumCircleProduct

/-! # Actual bridge minimum is uniform and independent of its shifted path

Circle Haar product factorization is unwrapped on (0,T]. The proved
actual bridge minimum lies in (0,T) almost surely, so the unwrapped
coordinate is the literal real minimum time. This proves the true joint
law, both marginal uniformity and independence, without identifying the
positive shifted path with a separately conditioned excursion law.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeMinimumUniformProduct

open BrownianPathLaw BrownianBridgeMinimumShift BrownianBridgeMinimumRotationLaw
open BrownianBridgeNegativeMinimum BrownianCircleUniformTime BrownianBridgeMinimumCircleProduct

def realMinimumJointMap (T : ℝ≥0) (hT : 0 < T) (f : Path) : ℝ × Path :=
  ((bridgeMinimumTime T f : ℝ),minimumShiftPath T hT f)

theorem measurable_realMinimumJointMap (T : ℝ≥0) (hT : 0 < T) :
    Measurable (realMinimumJointMap T hT) :=
  (NNReal.continuous_coe.measurable.comp (measurable_bridgeMinimumTime T)).prodMk
    (measurable_minimumShiftPath T hT)

def realMinimumJointLaw (T : ℝ≥0) (hT : 0 < T) : Measure (ℝ × Path) :=
  pathLaw.map (realMinimumJointMap T hT)

instance (T : ℝ≥0) (hT : 0 < T) : IsProbabilityMeasure (realMinimumJointLaw T hT) :=
  Measure.isProbabilityMeasure_map (measurable_realMinimumJointMap T hT).aemeasurable

theorem circleJointLaw_unwrap (T : ℝ≥0) (hT : 0 < T) :
    letI : Fact (0 < (T : ℝ)) := ⟨hT⟩
    (circleJointLaw T).map (Prod.map (unwrapTime (T : ℝ)) id) = realMinimumJointLaw T hT := by
  let : Fact (0 < (T : ℝ)) := ⟨hT⟩
  have hmU := (measurable_unwrapTime (T : ℝ)).prodMap (measurable_id (α := Path))
  unfold circleJointLaw minimumShiftJointLaw realMinimumJointLaw
  rw [Measure.map_map hmU (measurable_circlePair T),
    Measure.map_map (hmU.comp (measurable_circlePair T)) (measurable_minimumShiftJointMap T hT)]
  change pathLaw.map (fun f ↦ (unwrapTime (T : ℝ) ((bridgeMinimumTime T f : ℝ) : AddCircle (T : ℝ)),
      minimumShiftPath T hT f)) = pathLaw.map (realMinimumJointMap T hT)
  apply Measure.map_congr
  filter_upwards [ae_bridgeMinimumTime_interior T hT] with f hf
  apply Prod.ext
  · exact unwrapTime_coe (T : ℝ) (bridgeMinimumTime T f : ℝ)
      ⟨show 0 < (bridgeMinimumTime T f : ℝ) from hf.1,
        show (bridgeMinimumTime T f : ℝ) ≤ (T : ℝ) from hf.2.le⟩
  · rfl

theorem realMinimumJointLaw_eq_uniform_prod (T : ℝ≥0) (hT : 0 < T) :
    realMinimumJointLaw T hT = (intervalUniform (T : ℝ)).prod (minimumShiftLaw T hT) := by
  let : Fact (0 < (T : ℝ)) := ⟨hT⟩
  rw [← circleJointLaw_unwrap T hT,circleJointLaw_eq_uniform_prod,
    ← Measure.map_prod_map _ _ (measurable_unwrapTime (T : ℝ)) (measurable_id (α := Path)),
    circleUniform_map_unwrapTime,Measure.map_id]

theorem minimumTime_real_map_eq_uniform (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (fun f ↦ (bridgeMinimumTime T f : ℝ)) = intervalUniform (T : ℝ) := by
  have he := congrArg (fun m : Measure (ℝ × Path) ↦ m.map Prod.fst)
    (realMinimumJointLaw_eq_uniform_prod T hT)
  rw [realMinimumJointLaw,Measure.map_map measurable_fst (measurable_realMinimumJointMap T hT),
    Measure.map_fst_prod,measure_univ,one_smul] at he
  exact he

theorem hasLaw_minimumTime_real_uniform (T : ℝ≥0) (hT : 0 < T) :
    HasLaw (fun f ↦ (bridgeMinimumTime T f : ℝ)) (intervalUniform (T : ℝ)) pathLaw :=
  ⟨(NNReal.continuous_coe.measurable.comp (measurable_bridgeMinimumTime T)).aemeasurable,
    minimumTime_real_map_eq_uniform T hT⟩

theorem minimumTime_real_indep_minimumShiftPath (T : ℝ≥0) (hT : 0 < T) :
    IndepFun (fun f ↦ (bridgeMinimumTime T f : ℝ)) (minimumShiftPath T hT) pathLaw := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (NNReal.continuous_coe.measurable.comp (measurable_bridgeMinimumTime T)).aemeasurable
    (measurable_minimumShiftPath T hT).aemeasurable).mpr
  change pathLaw.map (fun f ↦ ((bridgeMinimumTime T f : ℝ),minimumShiftPath T hT f)) =
    (pathLaw.map (fun f ↦ (bridgeMinimumTime T f : ℝ))).prod (pathLaw.map (minimumShiftPath T hT))
  rw [minimumTime_real_map_eq_uniform T hT]
  exact realMinimumJointLaw_eq_uniform_prod T hT

theorem minimumTime_indep_minimumShiftPath (T : ℝ≥0) (hT : 0 < T) :
    IndepFun (bridgeMinimumTime T) (minimumShiftPath T hT) pathLaw := by
  have he := (minimumTime_real_indep_minimumShiftPath T hT).comp
    continuous_real_toNNReal.measurable (measurable_id (α := Path))
  simpa only [Function.comp_def,Real.toNNReal_coe,id_eq] using he

theorem minimumShiftJointLaw_eq_uniform_prod (T : ℝ≥0) (hT : 0 < T) :
    minimumShiftJointLaw T hT =
      ((intervalUniform (T : ℝ)).map Real.toNNReal).prod (minimumShiftLaw T hT) := by
  let : Fact (0 < (T : ℝ)) := ⟨hT⟩
  have he := congrArg (fun m : Measure (ℝ × Path) ↦ m.map (Prod.map Real.toNNReal id))
    (realMinimumJointLaw_eq_uniform_prod T hT)
  rw [realMinimumJointLaw,Measure.map_map (continuous_real_toNNReal.measurable.prodMap measurable_id)
      (measurable_realMinimumJointMap T hT),
    ← Measure.map_prod_map _ _ continuous_real_toNNReal.measurable measurable_id,Measure.map_id] at he
  have hJ : (Prod.map Real.toNNReal id) ∘ realMinimumJointMap T hT = minimumShiftJointMap T hT := by
    funext f
    simp only [Function.comp_def,Prod.map_apply,realMinimumJointMap,Real.toNNReal_coe,id_eq,
      minimumShiftJointMap]
  rw [hJ] at he
  exact he

end PerronWright.BrownianBridgeMinimumUniformProduct
