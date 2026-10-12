import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Normalized circle Haar law and literal uniform interval law

The circle volume is normalized by its proved mass T. Unwrapping by the
measurable circle/interval equivalence gives exactly normalized Lebesgue
measure on (0,T], not a uniformity interface for a random minimum.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianCircleUniformTime

variable (T : ℝ) [hT : Fact (0 < T)]

def circleUniform : Measure (AddCircle T) := (ENNReal.ofReal T)⁻¹ • volume

instance : IsProbabilityMeasure (circleUniform T) := by
  refine ⟨?_⟩
  rw [circleUniform,Measure.smul_apply,AddCircle.measure_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hT.out)) ENNReal.ofReal_ne_top

instance : IsAddHaarMeasure (circleUniform T) :=
  IsAddHaarMeasure.smul (volume : Measure (AddCircle T))
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hT.out)))

def intervalUniform : Measure ℝ := (ENNReal.ofReal T)⁻¹ • volume.restrict (Ioc 0 T)

instance : IsProbabilityMeasure (intervalUniform T) := by
  refine ⟨?_⟩
  rw [intervalUniform,Measure.smul_apply,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hT.out)) ENNReal.ofReal_ne_top

def unwrapTime (x : AddCircle T) : ℝ := (AddCircle.equivIoc T 0 x : ℝ)

theorem measurable_unwrapTime : Measurable (unwrapTime T) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc T 0).measurable

theorem unwrapTime_coe (x : ℝ) (hx : x ∈ Ioc 0 T) : unwrapTime T (x : AddCircle T) = x := by
  exact AddCircle.equivIoc_coe_of_mem (by simpa only [zero_add] using hx)

theorem coe_toIcoMod_circle (x : ℝ) :
    ((toIcoMod hT.out 0 x : ℝ) : AddCircle T) = (x : AddCircle T) := by
  simpa only [AddCircle.equivIco,QuotientAddGroup.equivIcoMod_coe] using
    (AddCircle.coe_equivIco (p := T) (a := 0) (y := (x : AddCircle T)))

theorem volume_map_unwrapTime :
    (volume : Measure (AddCircle T)).map (unwrapTime T) = (volume : Measure ℝ).restrict (Ioc 0 T) := by
  have hm := (AddCircle.measurePreserving_equivIoc (T := T) (a := (0 : ℝ))).map_eq
  calc (volume : Measure (AddCircle T)).map (unwrapTime T) =
        ((volume : Measure (AddCircle T)).map (AddCircle.equivIoc T 0)).map Subtype.val := by
        rw [Measure.map_map measurable_subtype_coe
          (show Measurable (AddCircle.equivIoc T 0) from (AddCircle.measurableEquivIoc T 0).measurable)]
        rfl
    _ = (Measure.comap Subtype.val (volume : Measure ℝ)).map Subtype.val := by rw [hm]
    _ = (volume : Measure ℝ).restrict (Ioc 0 T) := by
      convert map_comap_subtype_coe
        (show MeasurableSet (Ioc (0 : ℝ) (0+T)) from measurableSet_Ioc) (volume : Measure ℝ) using 1
      rw [zero_add]

theorem circleUniform_map_unwrapTime : (circleUniform T).map (unwrapTime T) = intervalUniform T := by
  rw [circleUniform,Measure.map_smul,volume_map_unwrapTime]
  rfl

end PerronWright.BrownianCircleUniformTime
