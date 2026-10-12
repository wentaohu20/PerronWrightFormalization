import PerronWright.Probability.FinitePointMeasureCounts
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Borel measurability of actual point counts

Closed-cell evaluations are upper semicontinuous by actual finite-measure
Portmanteau. The proved finite-measure pi-system induction then extends
measurability to every Borel cell. No equality of Giry and weak Borel
sigma algebras is imposed as an assumption.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FinitePointMeasureMeasurable

open FiniteAtomicPointMeasure FinitePointMeasureCompact FinitePointMeasureCounts

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [BorelSpace E] [HasOuterApproxClosed E]

/-- The literal evaluation of a closed cell is upper semicontinuous
for the actual weak point-measure topology. -/
theorem upperSemicontinuous_eval_closed {A : Set E} (hA : IsClosed A) :
    UpperSemicontinuous (fun η : PointMeasure E ↦
      ((η : FiniteMeasure E) : Measure E) A) := by
  apply upperSemicontinuous_iff_limsup_le.mpr
  intro η
  exact FiniteMeasure.limsup_measure_closed_le_of_tendsto
    (continuous_val.tendsto η) hA

/-- The map from the weak-Borel point-measure space to actual measures
with the evaluation sigma algebra is genuinely measurable. -/
theorem measurable_toMeasure : Measurable (fun η : PointMeasure E ↦
    ((η : FiniteMeasure E) : Measure E)) := by
  apply Measurable.measure_of_isPiSystem
    (μ := fun η : PointMeasure E ↦ ((η : FiniteMeasure E) : Measure E))
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
  · intro A hA
    exact (upperSemicontinuous_eval_closed hA).measurable
  · simpa only [Function.comp_def, mass, FiniteMeasure.ennreal_mass] using
      ENNReal.continuous_coe.measurable.comp (measurable_mass (E := E))

/-- Every actual Borel cell has a measurable literal measure
evaluation on the weak-Borel point-measure space. -/
theorem measurable_eval {A : Set E} (hA : MeasurableSet A) :
    Measurable (fun η : PointMeasure E ↦ ((η : FiniteMeasure E) : Measure E) A) :=
  (Measure.measurable_coe hA).comp measurable_toMeasure

theorem measurable_eval_real {A : Set E} (hA : MeasurableSet A) :
    Measurable (fun η : PointMeasure E ↦
      ((η : FiniteMeasure E) : Measure E).real A) :=
  (measurable_eval hA).ennreal_toReal

/-- General Borel cell counts are measurable in the already-defined
weak-Borel sigma algebra, without assuming a Giry-Borel identification. -/
theorem measurable_count {A : Set E} (hA : MeasurableSet A) :
    Measurable (fun η : PointMeasure E ↦ count η A) := by
  have he : (fun η : PointMeasure E ↦ count η A) =
      fun η : PointMeasure E ↦ ⌊((η : FiniteMeasure E) : Measure E).real A⌋₊ := rfl
  rw [he]
  exact Nat.measurable_floor.comp (measurable_eval_real hA)

theorem measurable_count_vector {T : Type*} (A : T → Set E)
    (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (fun η : PointMeasure E ↦ fun i ↦ count η (A i)) :=
  measurable_pi_lambda _ (fun i ↦ measurable_count (hA i))

theorem measurable_cellCounts {d : ℕ} {p : E → Fin d} (hp : Measurable p) :
    Measurable (fun η : PointMeasure E ↦ cellCounts η p) :=
  measurable_count_vector _ (fun i ↦ hp (measurableSet_singleton i))

/-- The actual probability law of a finite family of point counts. -/
def countLaw {T : Type*} (ν : ProbabilityMeasure (PointMeasure E))
    (A : T → Set E) (hA : ∀ i, MeasurableSet (A i)) : ProbabilityMeasure (T → ℕ) :=
  ν.map (measurable_count_vector A hA).aemeasurable

theorem countLaw_toMeasure {T : Type*} (ν : ProbabilityMeasure (PointMeasure E))
    (A : T → Set E) (hA : ∀ i, MeasurableSet (A i)) :
    (countLaw ν A hA : Measure (T → ℕ)) =
      (ν : Measure (PointMeasure E)).map (fun η i ↦ count η (A i)) := rfl

end PerronWright.FinitePointMeasureMeasurable
