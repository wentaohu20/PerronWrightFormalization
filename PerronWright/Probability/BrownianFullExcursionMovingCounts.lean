import PerronWright.Probability.BrownianFullExcursionSpatialCells
import PerronWright.Probability.MeasurableMovingPointCounts

/-!
# Jointly measurable counts in genuine full excursion cells

The full atomic measure is evaluated in actual path-dependent endpoint
cells. Joint measurability is proved as a countable sum of the finite
strip evaluations, not assumed as a random excursion-count interface.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullExcursionMovingCounts

open BrownianPathLaw BrownianFullExcursionSpatialCells BrownianFullHorizonSpatialKernel
open BrownianFullHorizonSpatialCounts BrownianGaussianSkeleton FinitePointMeasureCompact

theorem measurable_moving_spatialMeasure (lambda : ℝ) (q : ℚ) :
    Measurable (fun p : Path × SpatialAtoms ↦ spatialMeasure p.2 (retainedCell lambda q p.1)) := by
  have he : (fun p : Path × SpatialAtoms ↦ spatialMeasure p.2 (retainedCell lambda q p.1)) =
      (fun p ↦ ∑' j : ℕ, ((p.2 j : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ))
        (retainedCell lambda q p.1)) := by
    funext p
    exact Measure.sum_apply _ (measurableSet_retainedCell lambda q p.1)
  rw [he]
  apply Measurable.tsum
  intro j
  exact (MeasurableMovingPointCounts.measurable_moving_eval (retainedCell lambda q)
    (measurableSet_joint_retainedCell lambda q)).comp
    (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

def spatialCounts (lambda : ℝ) (p : Path × SpatialAtoms) (q : ℚ) : ℕ :=
  spatialCount p.2 (retainedCell lambda q p.1)

theorem measurable_spatialCounts (lambda : ℝ) : Measurable (spatialCounts lambda) :=
  measurable_pi_lambda _ (fun q ↦ Nat.measurable_floor.comp
    (measurable_moving_spatialMeasure lambda q).ennreal_toReal)

def actualSpatialCounts (lambda : ℝ) (p : (ℕ → ℝ) × SpatialAtoms) : ℚ → ℕ :=
  spatialCounts lambda (measurablePath p.1,p.2)

theorem measurable_actualSpatialCounts (lambda : ℝ) : Measurable (actualSpatialCounts lambda) :=
  (measurable_spatialCounts lambda).comp
    ((measurable_measurablePath.comp measurable_fst).prodMk measurable_snd)

/-- The actual spatial-source joint law uses genuine full component cells
on one common full-measure source set, for all parameters and anchors. -/
theorem ae_actual_joint_retainedTimes_eq_component (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda, ∀ mu : ℝ, ∀ q : ℚ,
      retainedTimes mu q (measurablePath p.1) =
        if FullHorizonExcursionSection.Representative
            (BrownianActualWindowExcursions.actualPath mu p.1) q then
          FullHorizonExcursionComponents.component
            (BrownianActualWindowExcursions.actualPath mu p.1) (q : ℝ) else ∅ := by
  have h : ∀ᵐ x ∂(actualJointLaw lambda).map Prod.fst, ∀ mu : ℝ, ∀ q : ℚ,
      retainedTimes mu q (measurablePath x) =
        if FullHorizonExcursionSection.Representative
            (BrownianActualWindowExcursions.actualPath mu x) q then
          FullHorizonExcursionComponents.component
            (BrownianActualWindowExcursions.actualPath mu x) (q : ℝ) else ∅ := by
    rw [actualJointLaw_source]
    exact ae_all_retainedTimes_eq_component
  exact ae_of_ae_map measurable_fst.aemeasurable h

end PerronWright.BrownianFullExcursionMovingCounts
