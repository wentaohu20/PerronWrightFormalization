import PerronWright.Probability.BrownianExcursionPointProcessLaw
import PerronWright.Probability.GlobalPointSizeRescaling

/-! # Actual inverse size dilation of the Brownian excursion law

This is a literal proper point-measure pushforward of the constructed
Brownian law. Positive dilation and its inverse cancel on every locally
finite point measure, hence also on actual probability measures.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright.BrownianInverseSizeLaw

open ComponentGlobalPointProcess LocallyFinitePointMeasureVague GlobalPointSizeRescaling

theorem scalePoint_inv_scalePoint {c : ℝ} (hc : 0 < c)
    (η : LocalPointMeasure PositiveSizeSurplus) :
    scalePoint (inv_pos.mpr hc) (scalePoint hc η) = η := by
  apply Subtype.ext
  change ((η : Measure PositiveSizeSurplus).map (positiveSizeScale hc)).map
    (positiveSizeScale (inv_pos.mpr hc)) = (η : Measure PositiveSizeSurplus)
  rw [Measure.map_map (positiveSizeScale (inv_pos.mpr hc)).continuous.measurable
    (positiveSizeScale hc).continuous.measurable]
  have he : (positiveSizeScale (inv_pos.mpr hc)) ∘ (positiveSizeScale hc) = id := by
    funext z
    apply Prod.ext
    · apply Subtype.ext
      change c⁻¹*(c*z.1.val) = z.1.val
      rw [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]
    · rfl
  rw [he,Measure.map_id]

theorem scalePoint_scalePoint_inv {c : ℝ} (hc : 0 < c)
    (η : LocalPointMeasure PositiveSizeSurplus) :
    scalePoint hc (scalePoint (inv_pos.mpr hc) η) = η := by
  simpa only [inv_inv] using scalePoint_inv_scalePoint (inv_pos.mpr hc) η

def inverseScaledLaw (lambda : ℝ) {c : ℝ} (hc : 0 < c) :
    ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  (BrownianExcursionPointProcessLaw.law lambda).map
    (continuous_scalePoint (inv_pos.mpr hc)).measurable.aemeasurable

theorem inverseScaledLaw_map (lambda : ℝ) {c : ℝ} (hc : 0 < c) :
    (inverseScaledLaw lambda hc).map (continuous_scalePoint hc).measurable.aemeasurable =
      BrownianExcursionPointProcessLaw.law lambda := by
  apply ProbabilityMeasure.toMeasure_injective
  change (((BrownianExcursionPointProcessLaw.law lambda : Measure _).map
    (scalePoint (inv_pos.mpr hc))).map (scalePoint hc)) =
      (BrownianExcursionPointProcessLaw.law lambda : Measure _)
  rw [Measure.map_map (continuous_scalePoint hc).measurable
    (continuous_scalePoint (inv_pos.mpr hc)).measurable]
  have he : (scalePoint hc) ∘ (scalePoint (inv_pos.mpr hc)) = id :=
    funext (scalePoint_scalePoint_inv hc)
  rw [he,Measure.map_id]

end PerronWright.BrownianInverseSizeLaw
