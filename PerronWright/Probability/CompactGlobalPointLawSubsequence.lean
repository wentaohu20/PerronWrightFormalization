import PerronWright.Probability.GlobalPointChartAtomicAssembly
import PerronWright.Probability.GlobalPointChartTightness

/-!
# Actual global vague law tightness and subsequential convergence

The source is the literal component point measure on `(0, ∞) × ℕ`.
Its law is exactly the continuous assembly pushforward of the actual
compatible-chart graph law. The already proved countable-product
tightness therefore gives actual global vague-law tightness, and an
actual probability law is obtained along a strictly increasing
subsequence. No target law, measure-assembly, or tightness interface is
postulated. This file does not assert uniqueness of the global limit or
identify it with a Brownian construction.
-/

open MeasureTheory Filter Topology
open scoped Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CompactGlobalPointLawSubsequence

open GlobalPointMeasureCharts GlobalPointChartTightness
open GlobalPointChartAtomicAssembly ComponentGlobalPointProcess
open LocallyFinitePointMeasureVague

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- Exact all-size source identity, including the empty graph at `n = 0`. -/
theorem compatibleChartLaw_map_assemble (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    (compatibleChartLaw M lambda n).map continuous_assemble.measurable.aemeasurable =
      unmarkedProcessLaw M lambda n := by
  apply Subtype.ext
  change ((AnnealedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map sourceCompatibleCharts).map assemble =
      (AnnealedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n).map unmarkedProcess
  rw [Measure.map_map continuous_assemble.measurable (measurable_sourceCompatibleCharts n)]
  congr 1
  funext G
  exact assemble_sourceCompatibleCharts G

/-- Actual vague-Borel laws of the literal global component point
process form a tight family. -/
theorem isTight_unmarkedProcessLaws (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (hQP : M.QP) (lambda : ℝ) :
    IsTightMeasureSet (Set.range (fun n ↦
      (unmarkedProcessLaw M lambda n : Measure (LocalPointMeasure PositiveSizeSurplus)))) := by
  have hm (n : ℕ) :
      (compatibleChartLaw M lambda n : Measure CompatibleCharts).map assemble =
        (unmarkedProcessLaw M lambda n : Measure (LocalPointMeasure PositiveSizeSurplus)) := by
    simpa only [ProbabilityMeasure.toMeasure_map] using congrArg
      (fun ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) ↦
        (ν : Measure (LocalPointMeasure PositiveSizeSurplus)))
      (compatibleChartLaw_map_assemble M lambda n)
  have he : Set.range (fun n ↦
      (unmarkedProcessLaw M lambda n : Measure (LocalPointMeasure PositiveSizeSurplus))) =
      Measure.map assemble '' Set.range (fun n ↦
        (compatibleChartLaw M lambda n : Measure CompatibleCharts)) := by
    ext μ
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨n, rfl⟩, hm n⟩
    · rintro ⟨ν, ⟨n, rfl⟩, hν⟩
      exact ⟨n, (hm n).symm.trans hν⟩
  rw [he]
  exact (isTight_compatibleChartLaws M hM hQP lambda).map continuous_assemble

/-- Prokhorov compactness for the actual global-law family in its
literal weak topology induced by the vague point-measure topology. -/
theorem isCompact_closure_unmarkedProcessLaws (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    IsCompact (closure (Set.range (unmarkedProcessLaw M lambda))) := by
  apply isCompact_closure_of_isTightMeasureSet
  have he : {((ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus)) :
      Measure (LocalPointMeasure PositiveSizeSurplus)) |
      ν ∈ Set.range (unmarkedProcessLaw M lambda)} = Set.range (fun n ↦
        (unmarkedProcessLaw M lambda n : Measure (LocalPointMeasure PositiveSizeSurplus))) := by
    ext μ
    simp
  rw [he]
  exact isTight_unmarkedProcessLaws M hM hQP lambda

/-- Every reindexed actual graph sequence has a further genuinely weak
convergent subsequence. This uses the proved Polish chart space, rather
than assuming sequential compactness of the global vague space. -/
theorem exists_reindexed_unmarkedProcessLaw_subseq_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) (I : ℕ → ℕ) :
    ∃ ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      ∃ N : ℕ → ℕ, StrictMono N ∧
        Tendsto (fun k ↦ unmarkedProcessLaw M lambda (I (N k))) atTop (𝓝 ν) := by
  let : MetricSpace CompatibleCharts := TopologicalSpace.metrizableSpaceMetric _
  let : MetricSpace (ProbabilityMeasure CompatibleCharts) := TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨ξ, _, N, hN, hξ⟩ := (isCompact_closure_compatibleChartLaws M hM hQP lambda).tendsto_subseq
    (fun k ↦ subset_closure (Set.mem_range_self (I k)))
  refine ⟨ξ.map continuous_assemble.measurable.aemeasurable, N, hN, ?_⟩
  simpa only [compatibleChartLaw_map_assemble] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun k ↦ compatibleChartLaw M lambda (I (N k))) ξ hξ continuous_assemble

/-- An actual probability law of locally finite integer point measures
is obtained from the genuine graph process along a strictly increasing
subsequence. The convergence is weak law convergence for the proved
`C_c`-integral vague topology, not merely convergence of individual tests. -/
theorem exists_unmarkedProcessLaw_subseq_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    ∃ ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      ∃ N : ℕ → ℕ, StrictMono N ∧
        Tendsto (fun k ↦ unmarkedProcessLaw M lambda (N k)) atTop (𝓝 ν) := by
  obtain ⟨ξ, N, hN, hξ⟩ := exists_compatibleChartLaw_subseq_limit M hM hQP lambda
  refine ⟨ξ.map continuous_assemble.measurable.aemeasurable, N, hN, ?_⟩
  simpa only [compatibleChartLaw_map_assemble] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun k ↦ compatibleChartLaw M lambda (N k)) ξ hξ continuous_assemble

end PerronWright.CompactGlobalPointLawSubsequence
