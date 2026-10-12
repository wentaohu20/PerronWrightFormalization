import PerronWright.Probability.FiniteIrreducibleMarkedComponentProcess
import PerronWright.Probability.FiniteIrreducibleWindowCountLaw
import PerronWright.Probability.MarkedGlobalPointChartAtomicAssembly
import PerronWright.Probability.MarkedGlobalPointChartTightness

/-! # Actual deterministic empirical-marked global law tightness

The actual fixed-assignment finite graph maps into genuine compatible
compact charts. Their mass bounds follow from the already proved
finite irreducible window moments. Compact weak marks, closed interior
compatibility and genuine integer-measure assembly give actual global
vague weak subsequences, with no B2 or target-law assumption.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleMarkedGlobalTightness

open FiniteIrreducibleComponentProcess FiniteIrreducibleMarkedComponentProcess
  FiniteIrreducibleWindowCountLaw FinitePointMeasureCompact
  ComponentWindowMarkedLaw ComponentGlobalMarkedProcess LocallyFinitePointMeasureVague
  MarkedGlobalPointMeasureCharts MarkedGlobalPointChartTightness
  MarkedGlobalPointChartAtomicAssembly
open GlobalPointChartTightness (isTight_countable_product_of_marginals
  isTight_of_isClosedEmbedding_map)
open PositiveSizeSurplusExhaustion (lower upper lower_pos lower_le_upper)
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def chartLaw (M : FiniteIrreducibleModel S) (lambda : ℝ) (n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure (ChartProduct S) :=
  ⟨(graphLaw M lambda n x).map (sourceCharts x),
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩

def compatibleChartLaw (M : FiniteIrreducibleModel S) (lambda : ℝ) (n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure (CompatibleCharts S) :=
  ⟨(graphLaw M lambda n x).map (sourceCompatibleCharts x),
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩

omit [DiscreteTopology S] in
theorem chartLaw_eval (M : FiniteIrreducibleModel S) (lambda : ℝ) (n m : ℕ) (x : Fin n → S) :
    (chartLaw M lambda n x).map (continuous_apply m).measurable.aemeasurable =
      FiniteIrreducibleMarkedComponentProcess.markedWindowLaw M lambda (lower m) (upper m) m n x := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((graphLaw M lambda n x).map (sourceCharts x)).map (fun ζ ↦ ζ m) = _
  rw [Measure.map_map (continuous_apply m).measurable (measurable_of_countable _)]
  rfl

theorem isTight_markedWindowLaws (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D) :
    IsTightMeasureSet (Set.range (fun n ↦
      (FiniteIrreducibleMarkedComponentProcess.markedWindowLaw M lambda a b R n (x n) :
        Measure (PointMeasure (MarkedWindow S a b R))))) := by
  obtain ⟨B,hB,hbound⟩ := exists_window_mass_bound M hM lambda a b ha hab R x D hD hround
  apply isTightMeasureSet_of_mass_moment_bound
    (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedWindowLaw M lambda a b R n (x n))
    (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedWindowLaw_integrable M lambda a b R n (x n)
      (NNReal.continuous_coe.measurable.comp measurable_mass)) B hB
  intro n
  rw [FiniteIrreducibleMarkedComponentProcess.markedWindowLaw_mass_integral_eq_unmarked]
  exact hbound n

theorem isTight_chartLaws (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (lambda : ℝ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D) :
    IsTightMeasureSet (Set.range (fun n ↦ (chartLaw M lambda n (x n) : Measure (ChartProduct S)))) := by
  apply isTight_countable_product_of_marginals
  intro m
  simpa only [chartLaw_eval] using isTight_markedWindowLaws M hM lambda
    (lower m) (upper m) (lower_pos m) (lower_le_upper m) m x D hD hround

omit [DiscreteTopology S] in
theorem compatibleChartLaw_map_val (M : FiniteIrreducibleModel S)
    (lambda : ℝ) (n : ℕ) (x : Fin n → S) :
    (compatibleChartLaw M lambda n x).map measurable_forgetCharts.aemeasurable = chartLaw M lambda n x := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((graphLaw M lambda n x).map (sourceCompatibleCharts x)).map forgetCharts = _
  rw [Measure.map_map measurable_forgetCharts (measurable_of_countable _)]
  rfl

theorem isTight_compatibleChartLaws (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (lambda : ℝ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D) :
    IsTightMeasureSet (Set.range (fun n ↦
      (compatibleChartLaw M lambda n (x n) : Measure (CompatibleCharts S)))) := by
  apply isTight_of_isClosedEmbedding_map (fun n ↦ compatibleChartLaw M lambda n (x n))
    forgetCharts isClosed_compatible.isClosedEmbedding_subtypeVal
  simpa only [compatibleChartLaw_map_val] using isTight_chartLaws M hM lambda x D hD hround

theorem isCompact_closure_compatibleChartLaws (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D) :
    IsCompact (closure (Set.range (fun n ↦ compatibleChartLaw M lambda n (x n)))) := by
  apply isCompact_closure_of_isTightMeasureSet
  have he : {((ν : ProbabilityMeasure (CompatibleCharts S)) : Measure (CompatibleCharts S)) |
      ν ∈ Set.range (fun n ↦ compatibleChartLaw M lambda n (x n))} =
      Set.range (fun n ↦ (compatibleChartLaw M lambda n (x n) : Measure (CompatibleCharts S))) := by
    ext μ
    simp
  rw [he]
  exact isTight_compatibleChartLaws M hM lambda x D hD hround

omit [DiscreteTopology S] in
theorem compatibleChartLaw_map_assemble (M : FiniteIrreducibleModel S)
    (lambda : ℝ) (n : ℕ) (x : Fin n → S) :
    (compatibleChartLaw M lambda n x).map continuous_assemble.measurable.aemeasurable =
      FiniteIrreducibleMarkedComponentProcess.markedProcessLaw M lambda n x := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((graphLaw M lambda n x).map (sourceCompatibleCharts x)).map assemble = _
  rw [Measure.map_map continuous_assemble.measurable (measurable_of_countable _)]
  congr 1
  funext G
  exact assemble_sourceCompatibleCharts x G

/-- Every reindexing of the actual fixed-assignment graph laws has a
true marked vague weak subsequence. Spatial uniqueness is not asserted. -/
theorem exists_reindexed_markedProcessLaw_subseq_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (I : ℕ → ℕ) :
    ∃ ν : ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)),
      ∃ N : ℕ → ℕ, StrictMono N ∧ Tendsto (fun k ↦
        FiniteIrreducibleMarkedComponentProcess.markedProcessLaw M lambda (I (N k)) (x (I (N k))))
          atTop (𝓝 ν) := by
  let : MetricSpace (CompatibleCharts S) := TopologicalSpace.metrizableSpaceMetric _
  let : MetricSpace (ProbabilityMeasure (CompatibleCharts S)) := TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨ξ,_,N,hN,hξ⟩ := (isCompact_closure_compatibleChartLaws M hM lambda x D hD hround).tendsto_subseq
    (fun k ↦ subset_closure (Set.mem_range_self (I k)))
  refine ⟨ξ.map continuous_assemble.measurable.aemeasurable,N,hN,?_⟩
  simpa only [compatibleChartLaw_map_assemble] using ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun k ↦ compatibleChartLaw M lambda (I (N k)) (x (I (N k)))) ξ hξ continuous_assemble

end PerronWright.FiniteIrreducibleMarkedGlobalTightness
