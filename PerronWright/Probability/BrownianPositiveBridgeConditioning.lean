import PerronWright.Probability.BrownianBridgeSurvivalLaw
import Mathlib.Probability.ConditionalProbability

/-! # Actual positive-endpoint bridge conditioned above zero

For a>0 this law is the actual zero-endpoint pinned bridge conditioned
above -a, then translated by a. The conditioning has its proved exact
positive normalization. Its paths are strictly positive on [0,T] and
have endpoints a almost surely. No small-a limit, standard excursion
law or identification with minimumShiftLaw is assumed or claimed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeConditioning

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeAreaTiltPathLaw
open BrownianFirstPassageBridgeLaw BrownianBridgeSurvivalLaw ContinuousPathFirstPassage

def translate (a : ℝ) (f : Path) : Path :=
  ⟨fun t ↦ f t+a,(continuous_path f).add continuous_const⟩

@[simp] theorem translate_eval (a : ℝ) (f : Path) (t : ℝ≥0) : translate a f t = f t+a := rfl

theorem continuous_translate (a : ℝ) : Continuous (translate a) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_joint_eval.add continuous_const

theorem measurable_translate (a : ℝ) : Measurable (translate a) :=
  (continuous_translate a).measurable

def conditionedLaw (a : ℝ) (T : ℝ≥0) : Measure Path :=
  ProbabilityTheory.cond (pinnedLaw T) (bridgeConstraint (-a) T 0)

theorem conditionedLaw_isProbability (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    IsProbabilityMeasure (conditionedLaw a T) :=
  cond_isProbabilityMeasure (ne_of_gt (bridgeConstraint_probability_zero_endpoint_pos a ha T hT))

def positiveBridgeLaw (a : ℝ) (T : ℝ≥0) : Measure Path :=
  (conditionedLaw a T).map (translate a)

theorem positiveBridgeLaw_isProbability (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    IsProbabilityMeasure (positiveBridgeLaw a T) := by
  let : IsProbabilityMeasure (conditionedLaw a T) := conditionedLaw_isProbability a ha T hT
  exact Measure.isProbabilityMeasure_map (measurable_translate a).aemeasurable

theorem translate_mem_survival_iff (a : ℝ) (T : ℝ≥0) (g : Path) :
    translate a g ∈ survival 0 T ↔ g ∈ bridgeConstraint (-a) T 0 := by
  rw [mem_survival_iff,mem_bridgeConstraint_iff]
  constructor <;> intro h t ht
  · have hp := h t ht
    change 0 < g t+a at hp
    simp only [mul_zero,add_zero]
    linarith
  · have hp := h t ht
    simp only [mul_zero,add_zero] at hp
    change 0 < g t+a
    linarith

theorem ae_positiveBridgeLaw_survival (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ g ∂positiveBridgeLaw a T, g ∈ survival 0 T := by
  apply (ae_map_iff (measurable_translate a).aemeasurable (measurableSet_survival 0 T)).mpr
  have hc : ∀ᵐ g ∂conditionedLaw a T, g ∈ bridgeConstraint (-a) T 0 :=
    ae_cond_mem (measurableSet_bridgeConstraint (-a) T 0)
  exact hc.mono (fun g hg ↦ (translate_mem_survival_iff a T g).mpr hg)

theorem ae_positiveBridgeLaw_strictly_positive (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ g ∂positiveBridgeLaw a T, ∀ t : ℝ≥0, t ≤ T → 0 < g t :=
  (ae_positiveBridgeLaw_survival a T).mono (fun _ hg ↦ (mem_survival_iff _ _ _).mp hg)

theorem ae_pinnedLaw_endpoints_zero (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ g ∂pinnedLaw T, g 0 = 0 ∧ g T = 0 := by
  apply (ae_map_iff (measurable_stoppedBridgePath T).aemeasurable
    ((measurableSet_eq_fun (continuous_eval 0).measurable measurable_const).inter
      (measurableSet_eq_fun (continuous_eval T).measurable measurable_const))).mpr
  filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
  constructor
  · change bridge T (min 0 T) f = 0
    simp only [min_eq_left (show 0 ≤ T from zero_le),bridge,NNReal.coe_zero,zero_div,zero_mul,sub_zero,hf]
  · change bridge T (min T T) f = 0
    simpa only [min_self] using bridge_endpoint_zero T hT f

theorem ae_positiveBridgeLaw_endpoints (a : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ g ∂positiveBridgeLaw a T, g 0 = a ∧ g T = a := by
  apply (ae_map_iff (measurable_translate a).aemeasurable
    ((measurableSet_eq_fun (continuous_eval 0).measurable measurable_const).inter
      (measurableSet_eq_fun (continuous_eval T).measurable measurable_const))).mpr
  have hAC : conditionedLaw a T ≪ pinnedLaw T := cond_absolutelyContinuous
  filter_upwards [hAC.ae_le (ae_pinnedLaw_endpoints_zero T hT)] with g hg
  change g 0+a = a ∧ g T+a = a
  simp only [hg.1,hg.2,zero_add,and_self]

theorem positiveBridgeLaw_lintegral (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T)
    (Ψ : Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ g, Ψ g ∂positiveBridgeLaw a T) =
      (ENNReal.ofReal (1-Real.exp (-2*a^2/(T : ℝ))))⁻¹ *
        ∫⁻ g in bridgeConstraint (-a) T 0, Ψ (translate a g) ∂pinnedLaw T := by
  rw [positiveBridgeLaw,lintegral_map hΨ (measurable_translate a),conditionedLaw,
    ProbabilityTheory.cond,lintegral_smul_measure,smul_eq_mul,
    bridgeConstraint_probability_zero_endpoint a ha T hT]

end PerronWright.BrownianPositiveBridgeConditioning
