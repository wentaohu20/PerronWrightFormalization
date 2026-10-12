import PerronWright.Probability.BrownianBridgeMinimumAreaFirstMoment
import PerronWright.Probability.BrownianBridgeMinimumUniformProduct
import PerronWright.Enumeration.CubicCompensationInitialCoefficient
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Actual second minimum-shift area moment

The reverse minimum time samples the true shifted path uniformly,
independently of that entire path. Fubini therefore identifies the area
times its sampled height with the square of the area divided by duration.
Together with the exact minimum tail and actual Gaussian bridge variance,
this computes the genuine second moment, not an assumed excursion moment.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000

namespace PerronWright.BrownianBridgeMinimumAreaSecondMoment

open BrownianPathLaw BrownianPinnedBridgeArea BrownianBridgeMinimumTail
open BrownianBridgeMinimumArea BrownianBridgeMinimumAreaIntegrability
open BrownianBridgeMinimumShift BrownianBridgeCyclicPath BrownianBridgeCycleKernel
open BrownianBridgeCyclicArea BrownianCircleUniformTime BrownianBridgeMinimumUniformProduct

theorem negativeMinimum_square_tail (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | a ≤ negativeMinimum T f ^ 2} =
      ENNReal.ofReal (Real.exp (-2*a/(T : ℝ))) := by
  have he : {f : Path | a ≤ negativeMinimum T f ^ 2} =
      {f : Path | Real.sqrt a ≤ negativeMinimum T f} := by
    ext f
    change a ≤ negativeMinimum T f ^ 2 ↔ Real.sqrt a ≤ negativeMinimum T f
    have hm := negativeMinimum_nonneg T f
    have hs := Real.sqrt_nonneg a
    have hsq := Real.sq_sqrt ha.le
    constructor <;> intro h <;> nlinarith
  rw [he,negativeMinimum_tail (Real.sqrt a) (Real.sqrt_pos.mpr ha) T hT,
    Real.sq_sqrt ha.le]

theorem integral_negativeMinimum_square (T : ℝ≥0) (hT : 0 < T) :
    (∫ f : Path, negativeMinimum T f ^ 2 ∂pathLaw) = (T : ℝ)/2 := by
  rw [(integrable_pow_negativeMinimum T hT 2).integral_eq_integral_meas_le
    (Eventually.of_forall (fun f ↦ sq_nonneg (negativeMinimum T f)))]
  calc
    (∫ t in Ioi (0 : ℝ), pathLaw.real {f : Path | t ≤ negativeMinimum T f ^ 2}) =
        ∫ t in Ioi (0 : ℝ), Real.exp ((-2/(T : ℝ))*t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change (pathLaw {f : Path | t ≤ negativeMinimum T f ^ 2}).toReal = _
      rw [negativeMinimum_square_tail t ht T hT,ENNReal.toReal_ofReal (Real.exp_pos _).le]
      congr 1
      ring
    _ = (T : ℝ)/2 := by
      rw [integral_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num)
        (show 0 < (T : ℝ) from hT)) 0,mul_zero,
        Real.exp_zero]
      field_simp

theorem minimumShiftPath_reverse_minimumTime (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    minimumShiftPath T hT f (T-bridgeMinimumTime T f) = negativeMinimum T f := by
  have hm := bridgeMinimumTime_le T f
  change closedBridge T (cycleTime T (bridgeMinimumTime T f)
      (min (T-bridgeMinimumTime T f) T)) f-
      closedBridge T (bridgeMinimumTime T f) f = _
  rw [min_eq_left tsub_le_self,cycleTime,
    add_tsub_cancel_of_le hm,if_pos le_rfl,closedBridge_endpoint T hT f,
    bridgeMinimumTime_value,zero_sub]
  rfl

theorem pathArea_reverse_interval (T : ℝ≥0) (f : Path) :
    (∫ s in Ioc (0 : ℝ) (T : ℝ), f (Real.toNNReal ((T : ℝ)-s))) = pathArea T f := by
  rw [← intervalIntegral.integral_of_le T.coe_nonneg]
  simpa only [sub_self,sub_zero,pathArea] using
    intervalIntegral.integral_comp_sub_left (fun s : ℝ ↦ f (Real.toNNReal s)) (T : ℝ)
      (a := 0) (b := (T : ℝ))

def areaHeight (T : ℝ≥0) (p : ℝ × Path) : ℝ :=
  pathArea T p.2*p.2 (Real.toNNReal ((T : ℝ)-p.1))

theorem measurable_areaHeight (T : ℝ≥0) : Measurable (areaHeight T) :=
  ((measurable_pathArea T).comp measurable_snd).mul
    (continuous_joint_eval.measurable.comp
      (measurable_snd.prodMk (continuous_real_toNNReal.measurable.comp
        (measurable_const.sub measurable_fst))))

theorem areaHeight_realMinimumJointMap (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    areaHeight T (realMinimumJointMap T hT f) =
      minimumShiftArea T hT f*negativeMinimum T f := by
  unfold areaHeight realMinimumJointMap
  rw [← NNReal.coe_sub (bridgeMinimumTime_le T f),Real.toNNReal_coe,
    minimumShiftPath_reverse_minimumTime T hT f]
  rfl

theorem integrable_area_mul_negativeMinimum (T : ℝ≥0) (hT : 0 < T) :
    Integrable (fun f : Path ↦ minimumShiftArea T hT f*negativeMinimum T f) pathLaw := by
  have hm : MemLp (negativeMinimum T) (2 : ℝ≥0∞) pathLaw := by
    apply memLp_of_mem_interior_integrableExpSet (p := (2 : ℝ≥0))
    rw [integrableExpSet_negativeMinimum T hT,interior_univ]
    exact mem_univ _
  have hq : MemLp (minimumShiftArea T hT) (2 : ℝ≥0∞) pathLaw := by
    simpa using memLp_minimumShiftArea T hT 2
  exact hq.integrable_mul hm

/-- Uniform time and true full-path independence, not independence of
the Gaussian area and the minimum, identify this mixed moment. -/
theorem integral_area_mul_negativeMinimum (T : ℝ≥0) (hT : 0 < T) :
    (∫ f : Path, minimumShiftArea T hT f*negativeMinimum T f ∂pathLaw) =
      (T : ℝ)⁻¹ *∫ f : Path, minimumShiftArea T hT f ^ 2 ∂pathLaw := by
  let : Fact (0 < (T : ℝ)) := ⟨hT⟩
  have he : areaHeight T ∘ realMinimumJointMap T hT =
      fun f : Path ↦ minimumShiftArea T hT f*negativeMinimum T f :=
    funext (areaHeight_realMinimumJointMap T hT)
  have hi : Integrable (areaHeight T) (realMinimumJointLaw T hT) := by
    apply (integrable_map_measure (measurable_areaHeight T).aestronglyMeasurable
      (measurable_realMinimumJointMap T hT).aemeasurable).mpr
    rw [he]
    exact integrable_area_mul_negativeMinimum T hT
  rw [realMinimumJointLaw_eq_uniform_prod T hT] at hi
  calc
    (∫ f : Path, minimumShiftArea T hT f*negativeMinimum T f ∂pathLaw) =
        ∫ p, areaHeight T p ∂realMinimumJointLaw T hT := by
      rw [realMinimumJointLaw,integral_map (measurable_realMinimumJointMap T hT).aemeasurable
        (measurable_areaHeight T).aestronglyMeasurable]
      apply integral_congr_ae
      exact Eventually.of_forall (fun f ↦ (areaHeight_realMinimumJointMap T hT f).symm)
    _ = ∫ e, ∫ s, areaHeight T (s,e) ∂intervalUniform (T : ℝ) ∂minimumShiftLaw T hT := by
      rw [realMinimumJointLaw_eq_uniform_prod T hT,integral_prod_symm _ hi]
    _ = ∫ e, (T : ℝ)⁻¹ *pathArea T e ^ 2 ∂minimumShiftLaw T hT := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro e
      dsimp only
      rw [intervalUniform,integral_smul_measure]
      simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal T.coe_nonneg,smul_eq_mul]
      unfold areaHeight
      dsimp only
      rw [integral_const_mul,pathArea_reverse_interval]
      simp only [pow_two]
    _ = (T : ℝ)⁻¹ *∫ f : Path, minimumShiftArea T hT f ^ 2 ∂pathLaw := by
      rw [integral_const_mul,minimumShiftLaw,
        integral_map (measurable_minimumShiftPath T hT).aemeasurable
          ((measurable_pathArea T).pow_const 2).aestronglyMeasurable]
      rfl

theorem integral_gaussianArea_square (T : ℝ≥0) (hT : 0 < T) :
    (∫ f : Path, area T f ^ 2 ∂pathLaw) = (T : ℝ)^3/12 := by
  have h := variance_area T hT
  rw [variance_eq_integral (measurable_area T).aemeasurable,integral_area T hT] at h
  simpa only [sub_zero] using h

theorem integral_minimumShiftArea_square (T : ℝ≥0) (hT : 0 < T) :
    (∫ f : Path, minimumShiftArea T hT f ^ 2 ∂pathLaw) = 5*(T : ℝ)^3/12 := by
  have hq := integrable_pow_minimumShiftArea T hT 2
  have hm := integrable_pow_negativeMinimum T hT 2
  have hqm := integrable_area_mul_negativeMinimum T hT
  have hc : Integrable (fun f : Path ↦
      (2*(T : ℝ))*(minimumShiftArea T hT f*negativeMinimum T f)) pathLaw :=
    hqm.const_mul (2*(T : ℝ))
  have hsub : Integrable (fun f : Path ↦ minimumShiftArea T hT f ^ 2-
      (2*(T : ℝ))*(minimumShiftArea T hT f*negativeMinimum T f)) pathLaw := hq.sub hc
  have hms : Integrable (fun f : Path ↦ (T : ℝ)^2*negativeMinimum T f ^ 2) pathLaw :=
    hm.const_mul ((T : ℝ)^2)
  have he : (fun f : Path ↦ area T f ^ 2) =ᵐ[pathLaw]
      (fun f ↦ minimumShiftArea T hT f ^ 2-
        (2*(T : ℝ))*(minimumShiftArea T hT f*negativeMinimum T f)+
        (T : ℝ)^2*negativeMinimum T f ^ 2) := by
    filter_upwards [ae_minimumShiftArea_eq_area_sub_minimum T hT] with f hf
    rw [hf,negativeMinimum]
    ring
  have hv : (T : ℝ)^3/12 =
      (∫ f : Path, minimumShiftArea T hT f ^ 2 ∂pathLaw)-
        (2*(T : ℝ))*((T : ℝ)⁻¹ *∫ f : Path, minimumShiftArea T hT f ^ 2 ∂pathLaw)+
        (T : ℝ)^2*((T : ℝ)/2) := by
    rw [← integral_gaussianArea_square T hT,integral_congr_ae he,
      integral_add hsub hms,integral_sub hq hc,
      integral_const_mul,integral_const_mul,
      integral_area_mul_negativeMinimum T hT,integral_negativeMinimum_square T hT]
  have hne : (T : ℝ) ≠ 0 := ne_of_gt (show 0 < (T : ℝ) from hT)
  field_simp [hne] at hv
  nlinarith

/-- The actual normalized second area moment is the project's unchanged
literal connected-cubic Wright constant at surplus two. -/
theorem integral_unit_minimumShiftArea_square_div_factorial_eq_wrightConstant_two :
    (∫ f : Path, minimumShiftArea 1 zero_lt_one f ^ 2 ∂pathLaw) /
        ((2 : ℕ).factorial : ℝ) = PerronWrightFormulaMainTerm.wrightConstant 2 := by
  rw [integral_minimumShiftArea_square 1 zero_lt_one,GraphCore.wrightConstant_two]
  norm_num

end PerronWright.BrownianBridgeMinimumAreaSecondMoment
