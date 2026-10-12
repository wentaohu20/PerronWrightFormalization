import PerronWright.Probability.MarkedGlobalPointMeasureCharts
import PerronWright.Probability.GlobalPointChartTightness

/-! # Genuine tightness and subsequential laws of empirical-marked charts

All coordinate laws are the actual graph window laws. Their proved
first-mass bounds and compact mark space give tightness. A proved
countable-product theorem and closed-embedding pullback give actual
compatible-chart probability tightness and Prokhorov subsequences.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical ENNReal
open scoped PerronWright.ComponentWindowMarkedLaw

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.MarkedGlobalPointChartTightness

open MarkedGlobalPointMeasureCharts ComponentWindowMarkedLaw GlobalPointChartTightness
open PositiveSizeSurplusExhaustion (lower upper lower_pos lower_le_upper)

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

def forgetCharts : CompatibleCharts S → ChartProduct S := Subtype.val

theorem continuous_forgetCharts : Continuous (forgetCharts (S := S)) := continuous_subtype_val

theorem measurable_forgetCharts : Measurable (forgetCharts (S := S)) :=
  continuous_forgetCharts.measurable

theorem isTight_chartLaws (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (hQP : M.QP) (lambda : ℝ) :
    IsTightMeasureSet (Set.range (fun n ↦ (chartLaw M lambda n : Measure (ChartProduct S)))) := by
  apply isTight_countable_product_of_marginals
  intro m
  simpa only [chartLaw_eval] using isTight_markedWindowLaws M hM hQP lambda
    (lower m) (upper m) (lower_pos m) (lower_le_upper m) m

theorem compatibleChartLaw_map_val (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    (compatibleChartLaw M lambda n).map measurable_forgetCharts.aemeasurable =
        chartLaw M lambda n := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [compatibleChartLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map measurable_forgetCharts (measurable_sourceCompatibleCharts n)]
  rfl

theorem isTight_compatibleChartLaws (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (hQP : M.QP) (lambda : ℝ) :
    IsTightMeasureSet (Set.range (fun n ↦
      (compatibleChartLaw M lambda n : Measure (CompatibleCharts S)))) := by
  apply isTight_of_isClosedEmbedding_map (compatibleChartLaw M lambda)
    forgetCharts isClosed_compatible.isClosedEmbedding_subtypeVal
  simpa only [compatibleChartLaw_map_val] using isTight_chartLaws M hM hQP lambda

theorem isCompact_closure_compatibleChartLaws (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    IsCompact (closure (Set.range (compatibleChartLaw M lambda))) := by
  apply isCompact_closure_of_isTightMeasureSet
  have he : {((ν : ProbabilityMeasure (CompatibleCharts S)) : Measure (CompatibleCharts S)) |
      ν ∈ Set.range (compatibleChartLaw M lambda)} =
      Set.range (fun n ↦ (compatibleChartLaw M lambda n : Measure (CompatibleCharts S))) := by
    ext μ
    simp
  rw [he]
  exact isTight_compatibleChartLaws M hM hQP lambda

theorem exists_compatibleChartLaw_subseq_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    ∃ ν : ProbabilityMeasure (CompatibleCharts S), ∃ N : ℕ → ℕ, StrictMono N ∧
      Tendsto (fun k ↦ compatibleChartLaw M lambda (N k)) atTop (𝓝 ν) := by
  let : MetricSpace (CompatibleCharts S) := TopologicalSpace.metrizableSpaceMetric _
  let : MetricSpace (ProbabilityMeasure (CompatibleCharts S)) := TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨ν, _, N, hN, hν⟩ := (isCompact_closure_compatibleChartLaws M hM hQP lambda).tendsto_subseq
    (fun n ↦ subset_closure (Set.mem_range_self n))
  exact ⟨ν, N, hN, hν⟩

end PerronWright.MarkedGlobalPointChartTightness
