import PerronWright.Probability.BrownianExcursionAtomicMeasure
import PerronWright.Probability.GlobalPointChartSurjective

/-!
# Genuine vague-Borel measurability of the full excursion point process

The actual finite charts are proved compatible. The existing continuous
Riesz--Markov integer-point assembly then proves measurability into the
existing vague-Borel space, and compact-test uniqueness identifies its
value with the literal countable full-excursion Dirac sum.
-/

open MeasureTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal CompactlySupported

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionPointProcess

open BrownianExcursionWindowPointMeasure BrownianExcursionAtomicMeasure
open ComponentGlobalPointProcess PositiveSizeSurplusExhaustion
open GlobalPointMeasureCharts GlobalPointChartAssembly GlobalPointChartAtomicAssembly
open GlobalPointChartSurjective LocallyFinitePointMeasureVague

theorem measure_integral_eq_window (lambda : ℝ) (m : ℕ) (p : Input)
    (f : C_c(PositiveSizeSurplus, ℝ)) (hf : tsupport f ⊆ window m) :
    (∫ z, f z ∂measure lambda p) = testIntegral m f (windowPointMeasure lambda m p) := by
  rw [← integral_restrict_test_eq _ (isCompact_window m).measurableSet f hf,
    measure_restrict_window]
  unfold testIntegral
  exact integral_map (measurable_positiveWindowEmbedding _ _ _ _).aemeasurable
    f.continuous.measurable.aestronglyMeasurable

def charts (lambda : ℝ) (p : Input) : ChartProduct := fun m ↦ windowPointMeasure lambda m p

theorem measurable_charts (lambda : ℝ) : Measurable (charts lambda) :=
  measurable_pi_lambda _ (fun m ↦ measurable_windowPointMeasure lambda m)

theorem charts_mem_compatible (lambda : ℝ) (p : Input) : charts lambda p ∈ compatible := by
  intro m n hmn f hf
  have hfm : tsupport f ⊆ window m := hf.trans interior_subset
  have hfn : tsupport f ⊆ window n := hfm.trans (exhaustion.subset hmn)
  exact (measure_integral_eq_window lambda m p f hfm).symm.trans
    (measure_integral_eq_window lambda n p f hfn)

def compatibleCharts (lambda : ℝ) (p : Input) : CompatibleCharts :=
  ⟨charts lambda p,charts_mem_compatible lambda p⟩

theorem measurable_compatibleCharts (lambda : ℝ) : Measurable (compatibleCharts lambda) := by
  change @Measurable Input {ζ : ChartProduct // ζ ∈ compatible} _
    (borel {ζ : ChartProduct // ζ ∈ compatible}) (fun p ↦ ⟨charts lambda p,charts_mem_compatible lambda p⟩)
  rw [borel_comap,← BorelSpace.measurable_eq]
  exact (measurable_charts lambda).subtype_mk

theorem assemble_compatibleCharts (lambda : ℝ) (p : Input) :
    assemble (compatibleCharts lambda p) = process lambda p := by
  apply Subtype.ext
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ z, f z ∂assembledMeasure (compatibleCharts lambda p)) = ∫ z, f z ∂measure lambda p
  rw [assembledMeasure_integral]
  exact (measure_integral_eq_window lambda (supportIndex f) p f
    ((support_subset_interior_index f).trans interior_subset)).symm

/-- The sigma structure here is the existing literal vague topology's
Borel sigma algebra, not merely the measure-evaluation sigma algebra. -/
theorem measurable_process (lambda : ℝ) : Measurable (process lambda) := by
  have he : process lambda = assemble ∘ compatibleCharts lambda := by
    funext p
    exact (assemble_compatibleCharts lambda p).symm
  rw [he]
  exact continuous_assemble.measurable.comp (measurable_compatibleCharts lambda)

theorem process_integral (lambda : ℝ) (p : Input) (f : C_c(PositiveSizeSurplus, ℝ)) :
    (∫ z, f z ∂(process lambda p : Measure PositiveSizeSurplus)) =
      testIntegral (supportIndex f) f (windowPointMeasure lambda (supportIndex f) p) :=
  measure_integral_eq_window lambda (supportIndex f) p f
    ((support_subset_interior_index f).trans interior_subset)

end PerronWright.BrownianExcursionPointProcess
