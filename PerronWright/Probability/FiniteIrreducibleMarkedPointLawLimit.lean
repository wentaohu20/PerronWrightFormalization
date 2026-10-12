import PerronWright.Probability.FiniteIrreducibleMarkedGlobalConvergence
import PerronWright.Probability.FiniteIrreducibleWindowPointLawLimit
import PerronWright.Probability.FiniteIrreducibleGlobalPointLawLimit

/-! # Actual finite irreducible marked window and global vague weak limits

The source is the literal graph law with its deterministic vertex-type
assignment and actual component empirical probability marks. The
unmarked spatial law is genuinely constructed from that graph sequence;
the marked limit is its proved proper constant-Perron pushforward.
Only literal irreducible criticality (including period two) and bounded
O(1) type-count errors are used. No convergence, profile, tightness,
target-law existence or law-determination interface is assumed.
Brownian identification remains a separate theorem.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical CompactlySupported
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleMarkedPointLawLimit

open FiniteIrreducibleMarkedWindowConvergence FiniteIrreducibleMarkedGlobalTests
  FiniteIrreducibleMarkedGlobalConvergence ComponentWindowMarkedLaw
  ComponentWindowPointMeasures ComponentGlobalPointProcess ComponentGlobalMarkedProcess
  LocallyFinitePointMeasureVague FinitePointMeasureCompact
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Unique genuine spatial window limit and full empirical-marked weak
convergence to its actual finite Perron marking, simultaneously. -/
theorem exists_unique_unmarked_and_markedWindowLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D) :
    ∃! μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedWindowLaw
        M lambda a b R n (x n)) atTop (𝓝 μ) ∧
      Tendsto (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedWindowLaw
        M lambda a b R n (x n)) atTop (𝓝 (canonicalPerronMarkedLaw M hM a b R μ)) := by
  obtain ⟨μ,hμ,hunique⟩ :=
    FiniteIrreducibleWindowPointLawLimit.exists_unique_unmarkedWindowLaw_limit
      M hM lambda a b ha hab R x D hD hround
  have hmarked := markedWindowLaw_tendsto_of_unmarked M hM lambda a b ha hab R
    x D hD hround id tendsto_id μ hμ
  exact ⟨μ,⟨hμ,hmarked⟩,fun ρ hρ ↦ hunique ρ hρ.1⟩

theorem exists_unique_markedWindowLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D) :
    ∃! ν : ProbabilityMeasure (PointMeasure (MarkedWindow S a b R)),
      Tendsto (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedWindowLaw
        M lambda a b R n (x n)) atTop (𝓝 ν) := by
  let : PolishSpace (PointMeasure (MarkedWindow S a b R)) :=
    markedPointMeasure_polishSpace M.bjrModel a b hab R
  let : MetricSpace (PointMeasure (MarkedWindow S a b R)) :=
    TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨μ,⟨_,hmarked⟩,_⟩ := exists_unique_unmarked_and_markedWindowLaw_limit
    M hM lambda a b ha hab R x D hD hround
  exact ⟨canonicalPerronMarkedLaw M hM a b R μ,hmarked,
    fun ρ hρ ↦ tendsto_nhds_unique hρ hmarked⟩

/-- The canonical law uses the unique genuine unmarked graph limit,
not a separately supplied candidate or a Brownian-law interface. -/
def canonicalGlobalMarkedLimitLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D) :
    ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  canonicalGlobalMarkedLaw M hM
    (FiniteIrreducibleGlobalPointLawLimit.unmarkedProcessLimitLaw M hM lambda x D hD hround)

/-- Full-sequence actual empirical-marked weak convergence in the
proved global `C_c`-integral vague topology, with only model hypotheses. -/
theorem tendsto_markedProcessLaw_canonical (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D) :
    Tendsto (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedProcessLaw M lambda n (x n))
      atTop (𝓝 (canonicalGlobalMarkedLimitLaw M hM lambda x D hD hround)) :=
  markedProcessLaw_tendsto_of_unmarked M hM lambda x D hD hround id tendsto_id
    (FiniteIrreducibleGlobalPointLawLimit.unmarkedProcessLimitLaw M hM lambda x D hD hround)
    (FiniteIrreducibleGlobalPointLawLimit.tendsto_unmarkedProcessLimitLaw M hM lambda x D hD hround)

theorem exists_unique_markedProcessLaw_limit (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)),
      Tendsto (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedProcessLaw
        M lambda n (x n)) atTop (𝓝 ν) := by
  have hlim := tendsto_markedProcessLaw_canonical M hM lambda x D hD hround
  exact ⟨canonicalGlobalMarkedLimitLaw M hM lambda x D hD hround,hlim,
    fun ρ hρ ↦ tendsto_nhds_unique hρ hlim⟩

theorem exists_unique_unmarked_and_markedProcessLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D) :
    ∃! μ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      Tendsto (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedProcessLaw
        M lambda n (x n)) atTop (𝓝 μ) ∧
      Tendsto (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedProcessLaw
        M lambda n (x n)) atTop (𝓝 (canonicalGlobalMarkedLaw M hM μ)) := by
  obtain ⟨μ,hμ,hunique⟩ := FiniteIrreducibleGlobalPointLawLimit.exists_unique_unmarkedProcessLaw_limit
    M hM lambda x D hD hround
  exact ⟨μ,⟨hμ,markedProcessLaw_tendsto_of_unmarked M hM lambda x D hD hround id tendsto_id μ hμ⟩,
    fun ρ hρ ↦ hunique ρ hρ.1⟩

/-- The weak-law theorem evaluates actual graph observables, not
connected-law auxiliary states or a newly postulated marked measure. -/
theorem marked_graph_test_expectation_tendsto (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (F : LocalPointMeasure (MarkedPositiveSizeSurplus S) →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ G, F (markedProcess (x n) G)
      ∂FiniteIrreducibleComponentProcess.graphLaw M lambda n (x n)) atTop
      (𝓝 (∫ η, F η ∂(canonicalGlobalMarkedLimitLaw M hM lambda x D hD hround : Measure _))) := by
  have hF := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_markedProcessLaw_canonical M hM lambda x D hD hround) F
  simpa only [FiniteIrreducibleMarkedComponentProcess.markedProcessLaw_integral
    M lambda _ _ F.continuous.measurable] using hF

end PerronWright.FiniteIrreducibleMarkedPointLawLimit
