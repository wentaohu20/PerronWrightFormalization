import PerronWright.Probability.FinitePointMeasureMeasurable
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Joint measurability of genuine moving-cell point counts

A moving Borel cell is evaluated on the actual weak-Borel finite point
measure. Kernel measurability is proved for each genuinely finite fiber;
no uniform mass bound, finite-kernel witness, or Giry/Borel identification
is assumed. The literal integer count is its already-defined real floor.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true

namespace PerronWright.MeasurableMovingPointCounts

open FinitePointMeasureCompact

variable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
  [TopologicalSpace E] [BorelSpace E] [HasOuterApproxClosed E]

/-- Evaluate the actual finite point measure, with its already proved
weak-Borel measurability, as a genuine measure-valued kernel. -/
def evaluationKernel : Kernel (S × PointMeasure E) E :=
  ⟨fun p ↦ ((p.2 : FiniteMeasure E) : Measure E),
    FinitePointMeasureMeasurable.measurable_toMeasure.comp measurable_snd⟩

theorem evaluationKernel_isFiniteMeasure (p : S × PointMeasure E) :
    IsFiniteMeasure (evaluationKernel p) := by
  change IsFiniteMeasure ((p.2 : FiniteMeasure E) : Measure E)
  infer_instance

/-- Moving-set evaluation is jointly measurable in the real parameter
and the actual atomic point measure. -/
theorem measurable_moving_eval (D : S → Set E)
    (hD : MeasurableSet {p : S × E | p.2 ∈ D p.1}) :
    Measurable (fun p : S × PointMeasure E ↦
      ((p.2 : FiniteMeasure E) : Measure E) (D p.1)) := by
  have ht : MeasurableSet {p : (S × PointMeasure E) × E | p.2 ∈ D p.1.1} :=
    hD.preimage (measurable_fst.fst.prodMk measurable_snd)
  have hm := Kernel.measurable_kernel_prodMk_left_of_finite
    (κ := (evaluationKernel : Kernel (S × PointMeasure E) E)) ht
    evaluationKernel_isFiniteMeasure
  exact hm

theorem measurable_moving_count (D : S → Set E)
    (hD : MeasurableSet {p : S × E | p.2 ∈ D p.1}) :
    Measurable (fun p : S × PointMeasure E ↦ count p.2 (D p.1)) :=
  Nat.measurable_floor.comp (measurable_moving_eval D hD).ennreal_toReal

end PerronWright.MeasurableMovingPointCounts
