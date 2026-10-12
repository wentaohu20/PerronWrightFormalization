import PerronWright.Probability.BrownianInverseWindowLaw
import PerronWright.Probability.CountableStarredTVWindowLaw

/-! # Literal cancellation of the Brownian inverse window dilation

The countable source uses the original model's positive size multiplier.
The inverse-dilated actual Brownian window, followed by that multiplier,
is exactly the actual Brownian closed window. This is a point-measure
identity with both endpoints and every atom multiplicity retained; it
does not assume any countable graph convergence or Brownian identity.
-/

open MeasureTheory Set
open scoped Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableActualBrownianWindowTransport

open ComponentGlobalPointProcess ComponentWindowPointMeasures FinitePointMeasureCompact FinitePointMeasureMarking
open WindowSizeRescaling InverseWindowSizeRescaling

theorem inverse_window_map_eq_actual (lambda a b : ℝ) (R : ℕ) {c : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
    (BrownianInverseWindowLaw.law lambda (a/c) (b/c) R hc (div_pos ha hc)
      ((div_le_div_iff_of_pos_right hc).mpr hab)).map
      (continuous_mapPoint (windowScaleMap a b R hc)
        (continuous_windowScaleMap a b R hc)).measurable.aemeasurable =
      BrownianArbitraryWindowLaw.law lambda a b R ha hab := by
  apply ProbabilityMeasure.toMeasure_injective
  have hha := mul_pos hc (div_pos ha hc)
  have hhab := mul_le_mul_of_nonneg_left
    ((div_le_div_iff_of_pos_right hc).mpr hab) hc.le
  have hsource := (BrownianArbitraryWindowLaw.measurable_pointMeasure
    lambda (c*(a/c)) (c*(b/c)) R hha hhab).comp
      BrownianExcursionPointProcessLaw.measurable_pathInput
  have hinverse := (continuous_mapPoint _
    (continuous_inverseWindowScaleMap (a/c) (b/c) R hc)).measurable
  have hscale := (continuous_mapPoint _ (continuous_windowScaleMap a b R hc)).measurable
  simp only [BrownianInverseWindowLaw.law,ProbabilityMeasure.toMeasure_map,
    BrownianArbitraryWindowLaw.law_eq_actual_map]
  rw [Measure.map_map hinverse hsource,Measure.map_map hscale (hinverse.comp hsource)]
  congr 1
  funext p
  simp only [Function.comp_apply]
  apply Subtype.ext
  apply FiniteMeasure.toMeasure_injective
  have he : MeasurableEmbedding (positiveWindowEmbedding a b R ha) := by
    apply (measurable_positiveWindowEmbedding a b R ha).measurableEmbedding
    intro x y h
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun z : PositiveSizeSurplus ↦ z.1.val) h)
    · exact Fin.ext (congrArg (fun z : PositiveSizeSurplus ↦ z.2) h)
  apply he.map_injective
  simp only [mapPoint_val,FiniteMeasure.toMeasure_map]
  rw [Measure.map_map he.measurable (continuous_windowScaleMap a b R hc).measurable,
    Measure.map_map (he.measurable.comp (continuous_windowScaleMap a b R hc).measurable)
      (continuous_inverseWindowScaleMap (a/c) (b/c) R hc).measurable]
  have hpoint : ((positiveWindowEmbedding a b R ha) ∘ (windowScaleMap a b R hc)) ∘
      (inverseWindowScaleMap (a/c) (b/c) R hc) =
      positiveWindowEmbedding (c*(a/c)) (c*(b/c)) R hha := by
    funext z
    apply Prod.ext
    · apply Subtype.ext
      exact mul_div_cancel₀ _ hc.ne'
    · rfl
  rw [hpoint,BrownianArbitraryWindowLaw.pointMeasure_embedded,
    BrownianArbitraryWindowLaw.pointMeasure_embedded]
  simp only [mul_div_cancel₀ a hc.ne',mul_div_cancel₀ b hc.ne']

end PerronWright.CountableActualBrownianWindowTransport
