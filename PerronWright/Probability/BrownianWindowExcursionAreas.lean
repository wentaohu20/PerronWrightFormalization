import PerronWright.Probability.BrownianActualWindowExcursions
import PerronWright.Probability.BrownianReflectedAreaCounts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Genuine measurable areas of actual clipped Brownian excursions

The endpoints are those of the proved connected components, and the area
is the literal Lebesgue integral over that component. Joint area
measurability uses the proved moving-interval integral on actual reflected
paths. Rational representatives give a nonrepeating countable family of
strictly positive actual areas, and a genuine probability law on this
measurable family. No excursion density or spatial Poisson process is
assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianWindowExcursionAreas

open BrownianPathLaw BrownianPathReflectionLaw BrownianWindowExcursions
open BrownianWindowExcursionEndpoints BrownianActualWindowExcursions
open BrownianGaussianSkeleton

theorem leftEndpoint_nonneg (H q : ℝ) (f : Path) : 0 ≤ leftEndpoint H q f := by
  by_cases hq : q ∈ positiveWindow H f
  · exact (endpoint_bounds hq).1
  · simp only [leftEndpoint,if_neg hq,le_refl]

theorem rightEndpoint_nonneg (H q : ℝ) (f : Path) : 0 ≤ rightEndpoint H q f := by
  by_cases hq : q ∈ positiveWindow H f
  · exact hq.1.1.le.trans (endpoint_bounds hq).2.2.1.le
  · simp only [rightEndpoint,if_neg hq,le_refl]

def leftTime (H q lambda : ℝ) (f : Path) : ℝ≥0 :=
  Real.toNNReal (leftEndpoint H q (driftedReflectionPath lambda f))

def rightTime (H q lambda : ℝ) (f : Path) : ℝ≥0 :=
  Real.toNNReal (rightEndpoint H q (driftedReflectionPath lambda f))

@[simp] theorem coe_leftTime (H q lambda : ℝ) (f : Path) :
    (leftTime H q lambda f : ℝ) = leftEndpoint H q (driftedReflectionPath lambda f) :=
  Real.coe_toNNReal _ (leftEndpoint_nonneg H q _)

@[simp] theorem coe_rightTime (H q lambda : ℝ) (f : Path) :
    (rightTime H q lambda f : ℝ) = rightEndpoint H q (driftedReflectionPath lambda f) :=
  Real.coe_toNNReal _ (rightEndpoint_nonneg H q _)

theorem measurable_leftTime_all_parameters (H q : ℝ) :
    Measurable (fun p : ℝ × Path ↦ leftTime H q p.1 p.2) :=
  continuous_real_toNNReal.measurable.comp
    ((measurable_leftEndpoint H q).comp continuous_driftedReflectionPath.measurable)

theorem measurable_rightTime_all_parameters (H q : ℝ) :
    Measurable (fun p : ℝ × Path ↦ rightTime H q p.1 p.2) :=
  continuous_real_toNNReal.measurable.comp
    ((measurable_rightEndpoint H q).comp continuous_driftedReflectionPath.measurable)

def excursionArea (H q lambda : ℝ) (f : Path) : ℝ≥0 :=
  BrownianReflectedAreaCounts.area lambda (leftTime H q lambda f) (rightTime H q lambda f) f

/-- Measurability includes the real drift parameter and the actual path. -/
theorem measurable_excursionArea_all_parameters (H q : ℝ) :
    Measurable (fun p : ℝ × Path ↦ excursionArea H q p.1 p.2) :=
  BrownianReflectedAreaCounts.measurable_area_all_parameters.comp
    (measurable_id.prodMk ((measurable_leftTime_all_parameters H q).prodMk
      (measurable_rightTime_all_parameters H q)))

set_option backward.isDefEq.respectTransparency true in
theorem measurable_excursionArea (H q lambda : ℝ) : Measurable (excursionArea H q lambda) := by
  have hm := (measurable_excursionArea_all_parameters H q).comp
    (f := fun f : Path ↦ (lambda,f))
    ((measurable_const : Measurable (fun _ : Path ↦ lambda)).prodMk measurable_id)
  simpa only [Function.comp_def] using hm

theorem integrableOn_component (H q : ℝ) (f : Path) :
    IntegrableOn (realEval f) (component H f q) :=
  (continuous_realEval f).integrableOn_Icc.mono_set
    (fun _t ht ↦ ⟨(component_subset H f q ht).1.1.le,(component_subset H f q ht).1.2.le⟩)

theorem excursionArea_eq_component_integral {H q lambda : ℝ} {f : Path}
    (hq : q ∈ positiveWindow H (driftedReflectionPath lambda f)) :
    (excursionArea H q lambda f : ℝ) =
      ∫ s in component H (driftedReflectionPath lambda f) q,
        realEval (driftedReflectionPath lambda f) s := by
  change (∫ s in Icc (leftTime H q lambda f : ℝ) (rightTime H q lambda f : ℝ),
    realEval (driftedReflectionPath lambda f) s) = _
  rw [coe_leftTime,coe_rightTime,component_eq_Ioo hq]
  exact integral_Icc_eq_integral_Ioc.trans integral_Ioc_eq_integral_Ioo

theorem excursionArea_pos {H q lambda : ℝ} {f : Path}
    (hq : q ∈ positiveWindow H (driftedReflectionPath lambda f)) :
    0 < excursionArea H q lambda f := by
  have hb := endpoint_bounds hq
  have hab := hb.2.1.trans hb.2.2.1
  have hp := intervalIntegral.integral_pos hab
    (BrownianReflectedAreaCounts.continuous_surface lambda f).continuousOn
    (fun t _ ↦ BrownianReflectedAreaCounts.surface_nonneg lambda f t)
    ⟨q,⟨hb.2.1.le,hb.2.2.1.le⟩,hq.2⟩
  apply NNReal.coe_lt_coe.mp
  change 0 < ∫ s in Icc (leftTime H q lambda f : ℝ) (rightTime H q lambda f : ℝ),
    BrownianReflectedAreaCounts.surface lambda f s
  rw [coe_leftTime,coe_rightTime,integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab.le]
  exact hp

theorem excursionArea_eq_zero_of_inactive {H q lambda : ℝ} {f : Path}
    (hq : q ∉ positiveWindow H (driftedReflectionPath lambda f)) : excursionArea H q lambda f = 0 := by
  apply NNReal.coe_injective
  change (∫ s in Icc (leftTime H q lambda f : ℝ) (rightTime H q lambda f : ℝ),
    BrownianReflectedAreaCounts.surface lambda f s) = 0
  rw [coe_leftTime,coe_rightTime]
  simp only [leftEndpoint,rightEndpoint,if_neg hq,Icc_self]
  simp

theorem excursionArea_eq_component_integral_all (H q lambda : ℝ) (f : Path) :
    (excursionArea H q lambda f : ℝ) =
      ∫ s in component H (driftedReflectionPath lambda f) q,
        realEval (driftedReflectionPath lambda f) s := by
  by_cases hq : q ∈ positiveWindow H (driftedReflectionPath lambda f)
  · exact excursionArea_eq_component_integral hq
  · rw [excursionArea_eq_zero_of_inactive hq]
    have he : component H (driftedReflectionPath lambda f) q = ∅ :=
      connectedComponentIn_eq_empty hq
    rw [he]
    simp

theorem excursionArea_eq_of_component_eq {H q r lambda : ℝ} {f : Path}
    (hq : q ∈ positiveWindow H (driftedReflectionPath lambda f))
    (hr : r ∈ positiveWindow H (driftedReflectionPath lambda f))
    (he : component H (driftedReflectionPath lambda f) q =
      component H (driftedReflectionPath lambda f) r) : excursionArea H q lambda f = excursionArea H r lambda f := by
  apply NNReal.coe_injective
  rw [excursionArea_eq_component_integral hq,excursionArea_eq_component_integral hr,he]

/-- Duplicates receive zero; every retained coordinate is the genuine
strictly positive area of its actual nonempty excursion component. -/
def retainedArea (H lambda : ℝ) (q : ℚ) (f : Path) : ℝ≥0 :=
  if Representative H (driftedReflectionPath lambda f) q then excursionArea H (q : ℝ) lambda f else 0

theorem measurable_retainedArea_all_parameters (H : ℝ) (q : ℚ) :
    Measurable (fun p : ℝ × Path ↦ retainedArea H p.1 q p.2) :=
  Measurable.ite ((measurableSet_representative H q).preimage continuous_driftedReflectionPath.measurable)
    (measurable_excursionArea_all_parameters H (q : ℝ)) measurable_const

theorem retainedArea_pos_iff (H lambda : ℝ) (q : ℚ) (f : Path) :
    0 < retainedArea H lambda q f ↔ Representative H (driftedReflectionPath lambda f) q := by
  by_cases hq : Representative H (driftedReflectionPath lambda f) q
  · simp only [retainedArea,hq,if_true,iff_true]
    exact excursionArea_pos hq.1
  · simp only [retainedArea,hq,if_false,lt_self_iff_false]

def areaData (H lambda : ℝ) (f : Path) (q : ℚ) : ℝ≥0 := retainedArea H lambda q f

theorem measurable_areaData_all_parameters (H : ℝ) : Measurable
    (fun p : ℝ × Path ↦ areaData H p.1 p.2) :=
  measurable_pi_lambda _ (fun q ↦ measurable_retainedArea_all_parameters H q)

set_option backward.isDefEq.respectTransparency true in
theorem measurable_areaData (H lambda : ℝ) : Measurable (areaData H lambda) := by
  have hm := (measurable_areaData_all_parameters H).comp
    (f := fun f : Path ↦ (lambda,f))
    ((measurable_const : Measurable (fun _ : Path ↦ lambda)).prodMk measurable_id)
  simpa only [Function.comp_def] using hm

def clippedExcursionAreaLaw (H lambda : ℝ) : Measure (ℚ → ℝ≥0) := pathLaw.map (areaData H lambda)

instance (H lambda : ℝ) : IsProbabilityMeasure (clippedExcursionAreaLaw H lambda) :=
  Measure.isProbabilityMeasure_map (measurable_areaData H lambda).aemeasurable

theorem hasLaw_actual_areaData (H lambda : ℝ) :
    HasLaw (fun x ↦ areaData H lambda (measurablePath x)) (clippedExcursionAreaLaw H lambda) rationalLaw :=
  (show HasLaw (areaData H lambda) (clippedExcursionAreaLaw H lambda) pathLaw from
    ⟨(measurable_areaData H lambda).aemeasurable,rfl⟩).fun_comp hasLaw_measurablePath

theorem clippedExcursionAreaLaw_eq_map_rationalLaw (H lambda : ℝ) :
    clippedExcursionAreaLaw H lambda = rationalLaw.map (fun x ↦ areaData H lambda (measurablePath x)) :=
  (hasLaw_actual_areaData H lambda).map_eq.symm

/-- Literal raw-process component areas agree simultaneously for every
window, drift parameter and real anchor on one actually proved full set. -/
theorem ae_all_excursionArea_eq_raw : ∀ᵐ x ∂rationalLaw, ∀ lambda H q : ℝ,
    (excursionArea H q lambda (measurablePath x) : ℝ) =
      ∫ s in connectedComponentIn (rawPositiveWindow H lambda x) q,
        ContinuousPathReflection.reflected
          (ContinuousPathReflection.parabolicDrift lambda
            (fun t ↦ BrownianContinuousModification.process t x)) (Real.toNNReal s) := by
  filter_upwards [ae_all_actual_component_eq_raw,ae_all_actual_driftedReflection_eq] with x hc hx
  intro lambda H q
  rw [excursionArea_eq_component_integral_all]
  change (∫ s in component H (actualPath lambda x) q, realEval (actualPath lambda x) s) = _
  rw [hc lambda H q]
  apply integral_congr_ae
  filter_upwards with s
  exact hx lambda (Real.toNNReal s)

theorem aemeasurable_raw_excursionArea (H q lambda : ℝ) : AEMeasurable
    (fun x : ℕ → ℝ ↦ ∫ s in connectedComponentIn (rawPositiveWindow H lambda x) q,
      ContinuousPathReflection.reflected
        (ContinuousPathReflection.parabolicDrift lambda
          (fun t ↦ BrownianContinuousModification.process t x)) (Real.toNNReal s)) rationalLaw := by
  have hm : Measurable (fun x : ℕ → ℝ ↦ (excursionArea H q lambda (measurablePath x) : ℝ)) :=
    NNReal.continuous_coe.measurable.comp
      ((measurable_excursionArea H q lambda).comp measurable_measurablePath)
  exact hm.aemeasurable.congr (ae_all_excursionArea_eq_raw.mono (fun _ hx ↦ hx lambda H q))

end PerronWright.BrownianWindowExcursionAreas
