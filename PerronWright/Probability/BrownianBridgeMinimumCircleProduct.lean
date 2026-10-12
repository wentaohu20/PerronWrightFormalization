import PerronWright.Probability.BrownianBridgeMinimumRotationLaw
import PerronWright.Probability.BrownianCircleUniformTime
import PerronWright.Probability.InvariantHaarJointProduct

/-! # Actual bridge minimum circle time and shifted path have product law

The actual bridge joint rotation identity is transported to the circle.
Every circle translation has a literal interval representative, so the
proved Haar uniqueness theorem identifies the joint law. No uniform
minimum-time or independence premise is used.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeMinimumCircleProduct

open BrownianPathLaw BrownianBridgeMinimumShift BrownianBridgeMinimumRotationLaw
open BrownianBridgeMinimumRotationGeometry BrownianBridgeRotationOffset BrownianBridgeCircleGeometry
open BrownianCircleUniformTime

variable (T : ℝ≥0) [hT : Fact (0 < (T : ℝ))]

def circlePair (p : ℝ≥0 × Path) : AddCircle (T : ℝ) × Path :=
  (((p.1 : ℝ) : AddCircle (T : ℝ)),p.2)

omit hT in theorem measurable_circlePair : Measurable (circlePair T) :=
  ((AddCircle.continuous_mk' (T : ℝ)).measurable.comp
    (NNReal.continuous_coe.measurable.comp measurable_fst)).prodMk measurable_snd

def circleJointLaw : Measure (AddCircle (T : ℝ) × Path) :=
  (minimumShiftJointLaw T (show 0 < T from hT.out)).map (circlePair T)

instance : IsProbabilityMeasure (circleJointLaw T) :=
  Measure.isProbabilityMeasure_map (measurable_circlePair T).aemeasurable

theorem circleTime_circle_coe (x : ℝ) :
    ((circleTime T (show 0 < T from hT.out) x : ℝ) : AddCircle (T : ℝ)) = (x : AddCircle (T : ℝ)) := by
  rw [circleTime_coe]
  exact coe_toIcoMod_circle (T : ℝ) x

theorem reverseOffset_circle_coe (s m : ℝ≥0) (hs : s ≤ T) (hm : m < T) :
    ((reverseOffset T s m : ℝ) : AddCircle (T : ℝ)) =
      ((m : ℝ) : AddCircle (T : ℝ)) - ((s : ℝ) : AddCircle (T : ℝ)) := by
  rw [reverseOffset_eq_circleTime T s m (show 0 < T from hT.out) hs hm,
    circleTime_circle_coe,AddCircle.coe_sub]

theorem circleJointLaw_translation_invariant (g : AddCircle (T : ℝ)) :
    (circleJointLaw T).map (fun p ↦ (g+p.1,p.2)) = circleJointLaw T := by
  let r : ℝ := (AddCircle.equivIco (T : ℝ) 0 (-g) : ℝ)
  have hr0 : 0 ≤ r := (AddCircle.equivIco (T : ℝ) 0 (-g)).property.1
  have hrT : r < (T : ℝ) := by
    simpa only [zero_add] using (AddCircle.equivIco (T : ℝ) 0 (-g)).property.2
  let s : ℝ≥0 := Real.toNNReal r
  have hsR : (s : ℝ) = r := Real.coe_toNNReal r hr0
  have hs : s ≤ T := NNReal.coe_le_coe.mp (hsR ▸ hrT.le)
  have hsc : ((s : ℝ) : AddCircle (T : ℝ)) = -g := by
    rw [hsR]
    exact AddCircle.coe_equivIco
  let τ : AddCircle (T : ℝ) × Path → AddCircle (T : ℝ) × Path := fun p ↦ (g+p.1,p.2)
  let R : ℝ≥0 × Path → ℝ≥0 × Path := fun p ↦ (reverseOffset T s p.1,p.2)
  have hmτ : Measurable τ := (measurable_const.add measurable_fst).prodMk measurable_snd
  have hmR : Measurable R :=
    ((measurable_reverseOffset T s).comp measurable_fst).prodMk measurable_snd
  have hAE : ∀ᵐ p ∂minimumShiftJointLaw T (show 0 < T from hT.out), p.1 < T := by
    apply (ae_map_iff (measurable_minimumShiftJointMap T (show 0 < T from hT.out)).aemeasurable
      (measurableSet_lt measurable_fst measurable_const)).mpr
    exact Filter.Eventually.of_forall (fun f ↦ bridgeMinimumTime_lt_end T (show 0 < T from hT.out) f)
  calc
    (circleJointLaw T).map τ =
        (minimumShiftJointLaw T (show 0 < T from hT.out)).map (τ ∘ circlePair T) := by
      exact Measure.map_map hmτ (measurable_circlePair T)
    _ = (minimumShiftJointLaw T (show 0 < T from hT.out)).map (circlePair T ∘ R) := by
      apply Measure.map_congr
      filter_upwards [hAE] with p hp
      apply Prod.ext
      · change g + ((p.1 : ℝ) : AddCircle (T : ℝ)) =
          ((reverseOffset T s p.1 : ℝ) : AddCircle (T : ℝ))
        rw [reverseOffset_circle_coe T s p.1 hs hp,hsc,sub_neg_eq_add,add_comm]
      · rfl
    _ = ((minimumShiftJointLaw T (show 0 < T from hT.out)).map R).map (circlePair T) :=
      (Measure.map_map (measurable_circlePair T) hmR).symm
    _ = circleJointLaw T := by
      rw [minimumShiftJointLaw_rotation_invariant T s (show 0 < T from hT.out) hs]
      rfl

theorem circleJointLaw_snd : (circleJointLaw T).map Prod.snd = minimumShiftLaw T (show 0 < T from hT.out) := by
  unfold circleJointLaw minimumShiftJointLaw minimumShiftLaw
  rw [Measure.map_map measurable_snd (measurable_circlePair T),
    Measure.map_map (measurable_snd.comp (measurable_circlePair T))
      (measurable_minimumShiftJointMap T (show 0 < T from hT.out))]
  rfl

theorem circleJointLaw_eq_uniform_prod :
    circleJointLaw T = (circleUniform (T : ℝ)).prod (minimumShiftLaw T (show 0 < T from hT.out)) := by
  rw [InvariantHaarJointProduct.invariant_joint_eq_haar_prod (circleUniform (T : ℝ))
    (circleJointLaw T) (circleJointLaw_translation_invariant T),circleJointLaw_snd]

end PerronWright.BrownianBridgeMinimumCircleProduct
