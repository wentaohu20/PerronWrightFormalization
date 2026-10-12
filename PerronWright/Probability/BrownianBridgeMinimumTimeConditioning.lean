import PerronWright.Probability.BrownianBridgeMinimumOccupationBias
import PerronWright.Probability.BrownianPositiveBridgeStoppedSupport
import PerronWright.Probability.BrownianBridgeMinimumShiftContinuity

/-! # Actual small-minimum-time bridge conditioning

The true pinned bridge conditioned on its literal minimum time in (0,ε]
is exactly the inverse cyclic splice of its true minimum-shift law and an
independent uniform time in (0,ε]. This conditioning is not conditioning
above a barrier, and is not yet identified with the entrance path law.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeMinimumTimeConditioning

open BrownianPathLaw BrownianBridgeMinimumShift BrownianBridgeMinimumReconstruction
open BrownianBridgeMinimumOccupationBias BrownianBridgeMinimumUniformTests
open BrownianBridgeMinimumUniformProduct BrownianBridgeCyclicPath BrownianCircleUniformTime
open BrownianFirstPassageBridgeLaw BrownianBridgeMinimumShiftContinuity

def inversePath (T : ℝ≥0) (hT : 0 < T) (p : ℝ × Path) : Path :=
  cyclicBridgePath T hT (reverseTime T p.1) p.2

theorem continuous_inversePath (T : ℝ≥0) (hT : 0 < T) : Continuous (inversePath T hT) :=
  (continuous_joint_cyclicBridgePath T hT).comp
    (((continuous_reverseTime T).comp continuous_fst).prodMk continuous_snd)

theorem inversePath_minimum_joint (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    inversePath T hT (realMinimumJointMap T hT f) = stoppedClosedBridgePath T f := by
  rw [inversePath,realMinimumJointMap,reverseTime_minimum,minimumShiftPath_inverse_rotate]

theorem ae_pinned_inversePath_minimum_joint (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pinnedLaw T, inversePath T hT (realMinimumJointMap T hT f) = f := by
  filter_upwards [BrownianPositiveBridgeConditioning.ae_pinnedLaw_endpoints_zero T hT,
    BrownianPositiveBridgeStoppedSupport.ae_pinnedLaw_stopped T] with f he hs
  rw [inversePath_minimum_joint]
  apply ContinuousMap.ext
  intro t
  change closedBridge T (min t T) f = f t
  rw [closedBridge_eq_of_endpoints T _ f he.1 he.2,← hs t]

def minimumTimeEvent (T : ℝ≥0) (ε : ℝ) : Set Path :=
  {f | (bridgeMinimumTime T f : ℝ) ∈ Ioc 0 ε}

theorem measurableSet_minimumTimeEvent (T : ℝ≥0) (ε : ℝ) : MeasurableSet (minimumTimeEvent T ε) :=
  (NNReal.continuous_coe.measurable.comp (measurable_bridgeMinimumTime T)) measurableSet_Ioc

theorem minimumTimeEvent_probability (T : ℝ≥0) (hT : 0 < T) (ε : ℝ)
    (hε : 0 < ε) (hεT : ε ≤ (T : ℝ)) :
    pinnedLaw T (minimumTimeEvent T ε) =
      (ENNReal.ofReal (T : ℝ))⁻¹*ENNReal.ofReal ε := by
  have he := bridgePathLaw_minimumTime_map_eq_uniform T hT
  change (pinnedLaw T).map (fun f ↦ (bridgeMinimumTime T f : ℝ)) = intervalUniform (T : ℝ) at he
  have hi := intervalUniform_Ioc (T : ℝ) 0 ε le_rfl hε.le hεT
  simp only [sub_zero] at hi
  rw [← hi,← he,
    Measure.map_apply (f := fun f ↦ (bridgeMinimumTime T f : ℝ))
      (NNReal.continuous_coe.measurable.comp (measurable_bridgeMinimumTime T))
      measurableSet_Ioc]
  rfl

def smallMinimumLaw (T : ℝ≥0) (ε : ℝ) : Measure Path :=
  ProbabilityTheory.cond (pinnedLaw T) (minimumTimeEvent T ε)

theorem smallMinimumLaw_isProbability (T : ℝ≥0) (hT : 0 < T) (ε : ℝ)
    (hε : 0 < ε) (hεT : ε ≤ (T : ℝ)) : IsProbabilityMeasure (smallMinimumLaw T ε) := by
  apply cond_isProbabilityMeasure
  rw [minimumTimeEvent_probability T hT ε hε hεT]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hε))

theorem smallMinimumLaw_lintegral (T : ℝ≥0) (hT : 0 < T) (ε : ℝ)
    (hε : 0 < ε) (hεT : ε ≤ (T : ℝ)) (Ψ : Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ f ∂smallMinimumLaw T ε) =
      ∫⁻ s, ∫⁻ e, Ψ (inversePath T hT (s,e)) ∂minimumShiftLaw T hT ∂intervalUniform ε := by
  have hI := (continuous_inversePath T hT).measurable
  let B : Set ℝ := Ioc 0 ε
  have htest : Measurable (fun p : ℝ × Path ↦ if p.1 ∈ B then Ψ (inversePath T hT p) else 0) :=
    Measurable.ite (measurable_fst measurableSet_Ioc) (hΨ.comp hI) measurable_const
  have he : (∫⁻ f in minimumTimeEvent T ε, Ψ f ∂pinnedLaw T) =
      ∫⁻ f, (if (bridgeMinimumTime T f : ℝ) ∈ B then
        Ψ (inversePath T hT (realMinimumJointMap T hT f)) else 0) ∂pinnedLaw T := by
    rw [← lintegral_indicator (measurableSet_minimumTimeEvent T ε)]
    apply lintegral_congr_ae
    filter_upwards [ae_pinned_inversePath_minimum_joint T hT] with f hf
    rw [hf]
    simp [minimumTimeEvent,B,Set.indicator]
  have hprod := lintegral_bridgePathLaw_minimum_joint_eq_uniform T hT _ htest
  change (∫⁻ f, (if (bridgeMinimumTime T f : ℝ) ∈ B then
      Ψ (inversePath T hT (realMinimumJointMap T hT f)) else 0) ∂pinnedLaw T) = _ at hprod
  have hinner (s : ℝ) : (∫⁻ e, (if s ∈ B then Ψ (inversePath T hT (s,e)) else 0)
      ∂minimumShiftLaw T hT) = B.indicator
        (fun s ↦ ∫⁻ e, Ψ (inversePath T hT (s,e)) ∂minimumShiftLaw T hT) s := by
    by_cases hs : s ∈ B <;> simp [hs,Set.indicator]
  have hsub : B ⊆ Ioc 0 (T : ℝ) := fun _ hs ↦ ⟨hs.1,hs.2.trans hεT⟩
  rw [smallMinimumLaw,ProbabilityTheory.cond,lintegral_smul_measure,smul_eq_mul,
    minimumTimeEvent_probability T hT ε hε hεT,he,hprod]
  simp_rw [hinner]
  rw [lintegral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr hsub]
  have hcoef : ((ENNReal.ofReal (T : ℝ))⁻¹*ENNReal.ofReal ε)⁻¹*
      (ENNReal.ofReal (T : ℝ))⁻¹ = (ENNReal.ofReal ε)⁻¹ := by
    have hT0 : ENNReal.ofReal (T : ℝ) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hT)
    rw [ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top)
      (Or.inl (ENNReal.inv_ne_top.mpr hT0)),inv_inv]
    calc
      _ = (ENNReal.ofReal (T : ℝ)*(ENNReal.ofReal (T : ℝ))⁻¹)*
          (ENNReal.ofReal ε)⁻¹ := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel hT0 ENNReal.ofReal_ne_top,one_mul]
  rw [← mul_assoc,hcoef,intervalUniform,lintegral_smul_measure,smul_eq_mul]

theorem smallMinimumLaw_eq_inverse_uniform_product (T : ℝ≥0) (hT : 0 < T) (ε : ℝ)
    (hε : 0 < ε) (hεT : ε ≤ (T : ℝ)) :
    smallMinimumLaw T ε =
      ((intervalUniform ε).prod (minimumShiftLaw T hT)).map (inversePath T hT) := by
  apply Measure.ext
  intro B hB
  have he := smallMinimumLaw_lintegral T hT ε hε hεT (B.indicator (fun _ ↦ 1))
    (measurable_const.indicator hB)
  rw [show (fun _ : Path ↦ (1 : ℝ≥0∞)) = (1 : Path → ℝ≥0∞) from rfl,
    lintegral_indicator_one hB] at he
  calc
    _ = ∫⁻ s, ∫⁻ e, B.indicator 1 (inversePath T hT (s,e))
        ∂minimumShiftLaw T hT ∂intervalUniform ε := he
    _ = ∫⁻ p, B.indicator 1 (inversePath T hT p)
        ∂((intervalUniform ε).prod (minimumShiftLaw T hT)) :=
      (lintegral_prod _ (((measurable_const.indicator hB).comp
        (continuous_inversePath T hT).measurable).aemeasurable)).symm
    _ = _ := by
      rw [← lintegral_map (f := B.indicator (1 : Path → ℝ≥0∞)) (measurable_const.indicator hB)
        (continuous_inversePath T hT).measurable,lintegral_indicator_one hB]

end PerronWright.BrownianBridgeMinimumTimeConditioning
