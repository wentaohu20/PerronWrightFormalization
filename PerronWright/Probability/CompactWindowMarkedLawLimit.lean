import PerronWright.Probability.ComponentWindowMarkedConvergence
import PerronWright.Probability.CompactWindowPointLawLimit

/-!
# The genuine marked sampled-graph compact-window weak limit

The true typed graph law, with the actual component empirical type
measures attached to its atoms, converges weakly on the genuine
weak-Borel marked integer point-measure space. The limit is the
constant-Perron marking of the proved actual unmarked window limit.
Neither source convergence nor an empirical-mark concentration
interface is an assumption of these terminal theorems.

This is a compact-window theorem. It does not identify the unmarked
limit with a Brownian point process or claim local-vague convergence.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Topology
open scoped PerronWright.ComponentWindowMarkedLaw

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.CompactWindowMarkedLawLimit

open FinitePointMeasureCompact ComponentWindowPointMeasures ComponentWindowMarkedLaw
  ComponentWindowMarkedConvergence CompactWindowPointLawLimit

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- The unique actual unmarked limit simultaneously yields the actual
empirical-mark point-process limit, by canonical Perron marking. All
probabilities here are genuine push-forwards of the sampled graph law. -/
theorem exists_unique_unmarked_and_markedWindowLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (unmarkedWindowLaw M lambda a b R) atTop (𝓝 ν) ∧
        Tendsto (markedWindowLaw M lambda a b R) atTop
          (𝓝 (canonicalPerronMarkedLaw M hM a b R ν)) := by
  obtain ⟨ν,hν,hunique⟩ :=
    exists_unique_unmarkedWindowLaw_limit M hM hQP lambda a b ha hab R
  have hmarked : Tendsto (markedWindowLaw M lambda a b R) atTop
      (𝓝 (canonicalPerronMarkedLaw M hM a b R ν)) := by
    simpa only [id_eq] using markedWindowLaw_tendsto_of_unmarked
      M hM hQP lambda a b ha hab R id tendsto_id ν (by simpa only [id_eq] using hν)
  exact ⟨ν,⟨hν,hmarked⟩,fun ρ hρ ↦ hunique ρ hρ.1⟩

/-- Full-sequence weak convergence to a unique genuine marked
point-process law. Only the paper's natural regular-critical and QP
model conditions and a positive compact size window are assumed. -/
theorem exists_unique_markedWindowLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃! ρ : ProbabilityMeasure (PointMeasure (MarkedWindow S a b R)),
      Tendsto (markedWindowLaw M lambda a b R) atTop (𝓝 ρ) := by
  let : PolishSpace (PointMeasure (MarkedWindow S a b R)) :=
    markedPointMeasure_polishSpace M a b hab R
  let : MetricSpace (PointMeasure (MarkedWindow S a b R)) :=
    TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨ν,⟨_,hmarked⟩,_⟩ :=
    exists_unique_unmarked_and_markedWindowLaw_limit M hM hQP lambda a b ha hab R
  exact ⟨canonicalPerronMarkedLaw M hM a b R ν,hmarked,
    fun ρ hρ ↦ tendsto_nhds_unique hρ hmarked⟩

/-- The actual sampled typed-graph expectations of every bounded
continuous marked point-measure test converge to the canonical
Perron-marked actual unmarked limit. The integrals are over the real
typed-graph sampling space, not a selected-component auxiliary law. -/
theorem exists_actual_marked_test_expectation_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃ ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (unmarkedWindowLaw M lambda a b R) atTop (𝓝 ν) ∧
        ∀ F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ,
          Tendsto (fun n ↦ ∫ p, F (markedWindowPointMeasure p.1 (AnnealedTypedGraph.graph p) a b R)
            ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
              (CriticalScaling.time_nonneg lambda n) n) atTop
            (𝓝 (∫ η, F η ∂(canonicalPerronMarkedLaw M hM a b R ν : Measure _))) := by
  obtain ⟨ν,⟨hν,hmarked⟩,_⟩ :=
    exists_unique_unmarked_and_markedWindowLaw_limit M hM hQP lambda a b ha hab R
  refine ⟨ν,hν,?_⟩
  intro F
  have hF := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmarked F
  simpa only [markedWindowLaw_integral M lambda a b R _ F.continuous.measurable] using hF

end PerronWright.CompactWindowMarkedLawLimit
