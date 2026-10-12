import PerronWright.Probability.GraphGlobalSpatialLimit
import PerronWright.Probability.CompactAnnealedFactorialUniform
import PerronWright.Probability.FiniteIrreducibleLocalMainTerminal
import PerronWright.Probability.FiniteIrreducibleComponentProcess

/-! # Actual model graph sources for the uniform-local spatial bridge

The generic graph source has exactly n+1 vertices. Both model sources
are the already constructed graph measures at that size, and their
window and global pushforwards are definitionally the existing model
laws. The actual uniform local theorems prove the generic local condition
on the successor tail. Finite assignments remain arbitrary with bounded
literal fibre-count errors; no positive-kernel assumption is added.
-/

open MeasureTheory Filter Topology
open scoped Real BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ModelGraphUniformLocalBridge

open GraphWindowFactorialLimits
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

section Finite

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The literal deterministic finite graph source, indexed by n+1. -/
def finiteGraphSource (M : FiniteIrreducibleModel S) (lambda : ℝ)
    (x : (n : ℕ) → Fin n → S) : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))) :=
  fun n ↦ FiniteIrreducibleComponentProcess.graphLaw M lambda (n+1) (x (n+1))

private instance finiteGraphSource_isProbability (M : FiniteIrreducibleModel S)
    (lambda : ℝ) (x : (n : ℕ) → Fin n → S) :
    ∀ n, IsProbabilityMeasure (finiteGraphSource M lambda x n) := fun n ↦
  inferInstanceAs (IsProbabilityMeasure
    (FiniteIrreducibleComponentProcess.graphLaw M lambda (n+1) (x (n+1))))

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- The generic local condition is a consequence of the proved genuine
finite irreducible local formula for every bounded-error assignment. -/
theorem finite_hasUniformLocalLimit (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    HasUniformLocalLimit (finiteGraphSource M lambda x) (M.alpha hM) (M.beta hM) lambda := by
  intro q R hq a b ha hab ε hε
  have ht := FiniteIrreducibleLocalMainTerminal.eventually_uniform_floor_factorial_density_of_assignment
    M hM q R hq lambda a b ha (ha.le.trans hab) x D hD hround hε
  filter_upwards [(tendsto_add_atTop_nat 1).eventually ht] with n hn
  simpa only [GraphWindowSource.localExpectation,finiteGraphSource,
    FiniteIrreducibleComponentProcess.graphLaw] using hn

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
/-- The generic window is exactly the existing actual model window at
n+1, without any asymptotic or criticality premise. -/
theorem finite_windowLaw_eq (M : FiniteIrreducibleModel S) (lambda a b : ℝ)
    (x : (n : ℕ) → Fin n → S) (R n : ℕ) :
    GraphWindowSource.windowLaw (finiteGraphSource M lambda x) a b R n =
      FiniteIrreducibleComponentProcess.unmarkedWindowLaw M lambda a b R (n+1) (x (n+1)) := rfl

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
/-- The generic global law is the literal deterministic model
component-process law at n+1. -/
theorem finite_processLaw_eq (M : FiniteIrreducibleModel S) (lambda : ℝ)
    (x : (n : ℕ) → Fin n → S) (n : ℕ) :
    GraphGlobalSpatialLimit.processLaw (finiteGraphSource M lambda x) n =
      FiniteIrreducibleComponentProcess.unmarkedProcessLaw M lambda (n+1) (x (n+1)) := rfl

end Finite

section Compact

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

/-- The literal annealed compact graph source, indexed by n+1. -/
def compactGraphSource (M : CompactBJRModel S) (lambda : ℝ) :
    (n : ℕ) → Measure (SimpleGraph (Fin (n+1))) := fun n ↦
  AnnealedGraph.law M (CriticalScaling.time lambda (n+1))
    (CriticalScaling.time_nonneg lambda (n+1)) (n+1)

private instance compactGraphSource_isProbability (M : CompactBJRModel S) (lambda : ℝ) :
    ∀ n, IsProbabilityMeasure (compactGraphSource M lambda n) := fun n ↦
  inferInstanceAs (IsProbabilityMeasure (AnnealedGraph.law M
    (CriticalScaling.time lambda (n+1)) (CriticalScaling.time_nonneg lambda (n+1)) (n+1)))

/-- The proved regular-compact factorial formula discharges the generic
uniform local condition under the actual model's regularity and QP. -/
theorem compact_hasUniformLocalLimit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    HasUniformLocalLimit (compactGraphSource M lambda) (M.alpha hM) (M.beta hM) lambda := by
  intro q R hq a b ha hab ε hε
  have ht := CompactAnnealedFactorialUniform.factorial_uniform_bounded_surplus
    M hM hQP hq R lambda a b ha hab ε hε
  filter_upwards [(tendsto_add_atTop_nat 1).eventually ht] with n hn y r hya hyb hr
  have he := hn r hr y (FactorialDensity.mem_sizeWindow.mpr (fun i ↦ ⟨hya i,hyb i⟩))
  simpa only [GraphWindowSource.localExpectation,compactGraphSource,
    CompactAnnealedFactorialLocal.localExpectation] using he

/-- The generic window is exactly the already constructed actual
annealed compact window at n+1. -/
theorem compact_windowLaw_eq (M : CompactBJRModel S) (lambda a b : ℝ) (R n : ℕ) :
    GraphWindowSource.windowLaw (compactGraphSource M lambda) a b R n =
      ComponentWindowPointMeasures.unmarkedWindowLaw M lambda a b R (n+1) := rfl

/-- The generic global law is exactly the actual annealed compact
component-process law at n+1. -/
theorem compact_processLaw_eq (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    GraphGlobalSpatialLimit.processLaw (compactGraphSource M lambda) n =
      ComponentGlobalPointProcess.unmarkedProcessLaw M lambda (n+1) := rfl

end Compact

end PerronWright.ModelGraphUniformLocalBridge
