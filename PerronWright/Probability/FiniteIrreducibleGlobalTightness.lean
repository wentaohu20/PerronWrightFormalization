import PerronWright.Probability.FiniteIrreducibleWindowCountLaw
import PerronWright.Probability.GlobalPointChartTightness
import PerronWright.Probability.GlobalPointChartAtomicAssembly

/-! # Actual deterministic finite global vague-law tightness

Actual graph charts and their proved closed compatibility are reused.
The new fixed-assignment law's coordinate tightness is derived from its
proved actual window moments. Continuous chart assembly then constructs
true global vague-law subsequential limits. No limiting-law existence or
compactness interface is assumed. Global uniqueness is not asserted yet.
-/

open MeasureTheory Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleGlobalTightness

open FiniteIrreducibleComponentProcess FiniteIrreducibleWindowCountLaw
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)
open GlobalPointMeasureCharts GlobalPointChartTightness GlobalPointChartAtomicAssembly
open ComponentGlobalPointProcess (PositiveSizeSurplus unmarkedProcess measurable_unmarkedProcess)
open PositiveSizeSurplusExhaustion LocallyFinitePointMeasureVague

variable {S : Type*} [Fintype S] [DecidableEq S]

def chartLaw (M : FiniteIrreducibleModel S) (lambda : ℝ) (n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure ChartProduct :=
  ⟨(graphLaw M lambda n x).map sourceCharts,
    Measure.isProbabilityMeasure_map (measurable_sourceCharts n).aemeasurable⟩

def compatibleChartLaw (M : FiniteIrreducibleModel S) (lambda : ℝ) (n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure CompatibleCharts :=
  ⟨(graphLaw M lambda n x).map sourceCompatibleCharts,
    Measure.isProbabilityMeasure_map (measurable_sourceCompatibleCharts n).aemeasurable⟩

theorem chartLaw_eval (M : FiniteIrreducibleModel S) (lambda : ℝ) (n m : ℕ) (x : Fin n → S) :
    (chartLaw M lambda n x).map (continuous_apply m).measurable.aemeasurable =
      unmarkedWindowLaw M lambda (lower m) (upper m) m n x := by
  apply Subtype.ext
  change ((graphLaw M lambda n x).map sourceCharts).map (fun ζ : ChartProduct ↦ ζ m) = _
  rw [Measure.map_map (continuous_apply m).measurable (measurable_sourceCharts n)]
  rfl

theorem compatibleChartLaw_map_val (M : FiniteIrreducibleModel S) (lambda : ℝ)
    (n : ℕ) (x : Fin n → S) :
    (compatibleChartLaw M lambda n x).map measurable_forgetCharts.aemeasurable = chartLaw M lambda n x := by
  apply Subtype.ext
  change ((graphLaw M lambda n x).map sourceCompatibleCharts).map forgetCharts = _
  rw [Measure.map_map measurable_forgetCharts (measurable_sourceCompatibleCharts n)]
  rfl

theorem compatibleChartLaw_map_assemble (M : FiniteIrreducibleModel S) (lambda : ℝ)
    (n : ℕ) (x : Fin n → S) :
    (compatibleChartLaw M lambda n x).map continuous_assemble.measurable.aemeasurable =
      unmarkedProcessLaw M lambda n x := by
  apply Subtype.ext
  change ((graphLaw M lambda n x).map sourceCompatibleCharts).map assemble =
    (graphLaw M lambda n x).map unmarkedProcess
  rw [Measure.map_map continuous_assemble.measurable (measurable_sourceCompatibleCharts n)]
  congr 1
  funext G
  exact assemble_sourceCompatibleCharts G

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem isTight_chartLaws (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (lambda : ℝ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    IsTightMeasureSet (Set.range (fun n ↦ (chartLaw M lambda n (x n) : Measure ChartProduct))) := by
  apply isTight_countable_product_of_marginals
  intro m
  simpa only [chartLaw_eval] using isTight_unmarkedWindowLaws M hM lambda
    (lower m) (upper m) (lower_pos m) (lower_le_upper m) m x D hD hround

theorem isTight_compatibleChartLaws (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (lambda : ℝ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    IsTightMeasureSet (Set.range (fun n ↦
      (compatibleChartLaw M lambda n (x n) : Measure CompatibleCharts))) := by
  apply isTight_of_isClosedEmbedding_map (fun n ↦ compatibleChartLaw M lambda n (x n))
    forgetCharts isClosed_compatible.isClosedEmbedding_subtypeVal
  simpa only [compatibleChartLaw_map_val] using isTight_chartLaws M hM lambda x D hD hround

theorem isCompact_closure_compatibleChartLaws (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    IsCompact (closure (Set.range (fun n ↦ compatibleChartLaw M lambda n (x n)))) := by
  apply isCompact_closure_of_isTightMeasureSet
  have he : {((ν : ProbabilityMeasure CompatibleCharts) : Measure CompatibleCharts) |
      ν ∈ Set.range (fun n ↦ compatibleChartLaw M lambda n (x n))} =
      Set.range (fun n ↦ (compatibleChartLaw M lambda n (x n) : Measure CompatibleCharts)) := by
    ext μ
    simp
  rw [he]
  exact isTight_compatibleChartLaws M hM lambda x D hD hround

/-- Every reindexed actual fixed-type graph sequence has a true weakly
convergent global vague-law subsequence, constructed through Polish charts. -/
theorem exists_reindexed_unmarkedProcessLaw_subseq_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D)
    (I : ℕ → ℕ) :
    ∃ ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      ∃ N : ℕ → ℕ, StrictMono N ∧
        Tendsto (fun k ↦ unmarkedProcessLaw M lambda (I (N k)) (x (I (N k)))) atTop (𝓝 ν) := by
  let : MetricSpace CompatibleCharts := TopologicalSpace.metrizableSpaceMetric _
  let : MetricSpace (ProbabilityMeasure CompatibleCharts) := TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨ξ, _, N, hN, hξ⟩ := (isCompact_closure_compatibleChartLaws M hM lambda x D hD hround).tendsto_subseq
    (fun k ↦ subset_closure (Set.mem_range_self (I k)))
  refine ⟨ξ.map continuous_assemble.measurable.aemeasurable, N, hN, ?_⟩
  simpa only [compatibleChartLaw_map_assemble] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun k ↦ compatibleChartLaw M lambda (I (N k)) (x (I (N k)))) ξ hξ continuous_assemble

theorem exists_unmarkedProcessLaw_subseq_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    ∃ ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      ∃ N : ℕ → ℕ, StrictMono N ∧
        Tendsto (fun k ↦ unmarkedProcessLaw M lambda (N k) (x (N k))) atTop (𝓝 ν) :=
  exists_reindexed_unmarkedProcessLaw_subseq_limit M hM lambda x D hD hround id

end PerronWright.FiniteIrreducibleGlobalTightness
