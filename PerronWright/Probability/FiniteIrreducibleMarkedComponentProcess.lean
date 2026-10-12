import PerronWright.Probability.FiniteIrreducibleComponentProcess
import PerronWright.Probability.ComponentGlobalMarkedProcess
import PerronWright.Probability.GlobalPointMeasureMarking
import PerronWright.Probability.FiniteIrreducibleConnectedTypeLaw

/-! # Actual empirical-marked deterministic finite graph laws

The type assignment is fixed, not averaged. The marked atoms and their
weak/vague topology are the genuine constructions already proved for
individual finite graphs. No spectral regularity is used in these laws.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported
open scoped PerronWright.ComponentWindowMarkedLaw

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FiniteIrreducibleMarkedComponentProcess

open ComponentGlobalMarkedProcess ComponentGlobalPointProcess
  ComponentWindowMarkedLaw ComponentWindowPointMeasures
  LocallyFinitePointMeasureVague WeakProbabilityMarks FinitePointMeasureCompact
  FiniteIrreducibleComponentProcess

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- The canonical mark uses the actual finite irreducible Perron law. -/
def perronWeakMark (M : FiniteIrreducibleModel S) (hM : M.IsCritical) : WeakMark S :=
  ofProbability (FiniteIrreducibleConnectedTypeLaw.perronLaw M hM)

omit [DecidableEq S] [DiscreteTopology S] in
theorem measurable_markedWindowPointMeasure {n : ℕ} (x : Fin n → S)
    (a b : ℝ) (R : ℕ) :
    Measurable (fun G : SimpleGraph (Fin n) ↦ markedWindowPointMeasure x G a b R) :=
  measurable_of_countable _

omit [DecidableEq S] [DiscreteTopology S] in
theorem measurable_markedProcess {n : ℕ} (x : Fin n → S) :
    Measurable (fun G : SimpleGraph (Fin n) ↦ markedProcess x G) :=
  measurable_of_countable _

/-- Actual empirical-marked window law of the fixed-assignment graph. -/
def markedWindowLaw (M : FiniteIrreducibleModel S) (lambda a b : ℝ)
    (R n : ℕ) (x : Fin n → S) : ProbabilityMeasure (PointMeasure (MarkedWindow S a b R)) :=
  ⟨(graphLaw M lambda n x).map (fun G ↦ markedWindowPointMeasure x G a b R),
    Measure.isProbabilityMeasure_map (measurable_markedWindowPointMeasure x a b R).aemeasurable⟩

/-- Actual global empirical-marked component law on positive size/surplus. -/
def markedProcessLaw (M : FiniteIrreducibleModel S) (lambda : ℝ)
    (n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  ⟨(graphLaw M lambda n x).map (fun G ↦ markedProcess x G),
    Measure.isProbabilityMeasure_map (measurable_markedProcess x).aemeasurable⟩

omit [DiscreteTopology S] in
@[simp] theorem markedWindowLaw_toMeasure (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S) :
    (markedWindowLaw M lambda a b R n x : Measure (PointMeasure (MarkedWindow S a b R))) =
      (graphLaw M lambda n x).map (fun G ↦ markedWindowPointMeasure x G a b R) := rfl

omit [DiscreteTopology S] in
@[simp] theorem markedProcessLaw_toMeasure (M : FiniteIrreducibleModel S)
    (lambda : ℝ) (n : ℕ) (x : Fin n → S) :
    (markedProcessLaw M lambda n x : Measure (LocalPointMeasure (MarkedPositiveSizeSurplus S))) =
      (graphLaw M lambda n x).map (fun G ↦ markedProcess x G) := rfl

omit [DiscreteTopology S] in
theorem markedWindowLaw_integral (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S)
    {f : PointMeasure (MarkedWindow S a b R) → ℝ} (hf : Measurable f) :
    (∫ η, f η ∂(markedWindowLaw M lambda a b R n x : Measure _)) =
      ∫ G, f (markedWindowPointMeasure x G a b R) ∂graphLaw M lambda n x := by
  rw [markedWindowLaw_toMeasure]
  exact integral_map (measurable_markedWindowPointMeasure x a b R).aemeasurable
    hf.aestronglyMeasurable

omit [DiscreteTopology S] in
theorem markedWindowLaw_integrable (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S)
    {f : PointMeasure (MarkedWindow S a b R) → ℝ} (hf : Measurable f) :
    Integrable f (markedWindowLaw M lambda a b R n x : Measure _) := by
  rw [markedWindowLaw_toMeasure]
  exact (integrable_map_measure hf.aestronglyMeasurable
    (measurable_markedWindowPointMeasure x a b R).aemeasurable).mpr Integrable.of_finite

omit [DiscreteTopology S] in
theorem markedWindowLaw_mass_integral_eq_unmarked (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S) :
    (∫ η, (mass η : ℝ) ∂(markedWindowLaw M lambda a b R n x :
      Measure (PointMeasure (MarkedWindow S a b R)))) =
      ∫ η, (mass η : ℝ) ∂(FiniteIrreducibleComponentProcess.unmarkedWindowLaw
        M lambda a b R n x : Measure (PointMeasure (SurplusWindow a b R))) := by
  rw [markedWindowLaw_integral M lambda a b R n x
    (f := fun η ↦ (mass η : ℝ))
    (NNReal.continuous_coe.measurable.comp measurable_mass),
    FiniteIrreducibleComponentProcess.windowLaw_integral M lambda a b R n x
    (f := fun η ↦ (mass η : ℝ))
    (NNReal.continuous_coe.measurable.comp measurable_mass)]
  simp only [markedWindowPointMeasure_mass, windowPointMeasure_mass]

omit [DiscreteTopology S] in
theorem markedProcessLaw_integral (M : FiniteIrreducibleModel S)
    (lambda : ℝ) (n : ℕ) (x : Fin n → S)
    {f : LocalPointMeasure (MarkedPositiveSizeSurplus S) → ℝ} (hf : Measurable f) :
    (∫ η, f η ∂(markedProcessLaw M lambda n x : Measure _)) =
      ∫ G, f (markedProcess x G) ∂graphLaw M lambda n x := by
  rw [markedProcessLaw_toMeasure]
  exact integral_map (measurable_markedProcess x).aemeasurable hf.aestronglyMeasurable

end PerronWright.FiniteIrreducibleMarkedComponentProcess
