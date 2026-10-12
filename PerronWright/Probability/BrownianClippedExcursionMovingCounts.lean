import PerronWright.Probability.MeasurableMovingPointCounts
import PerronWright.Probability.BrownianClippedExcursionSpatialCells

/-!
# Actual clipped Brownian excursion spatial counts are jointly measurable

The literal retained connected components are proved equal to their actual
endpoint intervals. Their spatial membership is therefore jointly Borel
in path and position. Actual point counts in these moving, nonrepeating
cells are measurable, not a new excursion enumeration interface.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

namespace PerronWright.BrownianClippedExcursionMovingCounts

open BrownianPathLaw BrownianPathReflectionLaw BrownianWindowExcursions
open BrownianWindowExcursionEndpoints BrownianClippedExcursionSpatialCells
open FinitePointMeasureCompact BrownianGaussianSkeleton

theorem mem_retainedCell_iff (H lambda : ℝ) (q : ℚ) (f : Path) (z : ℝ × ℝ) :
    z ∈ retainedCell H lambda q f ↔
      Representative H (driftedReflectionPath lambda f) q ∧
        z.1 ∈ Ioo (leftEndpoint H (q : ℝ) (driftedReflectionPath lambda f))
          (rightEndpoint H (q : ℝ) (driftedReflectionPath lambda f)) := by
  by_cases hq : Representative H (driftedReflectionPath lambda f) q
  · simp only [retainedCell,retainedTimes,mem_prod,mem_univ,and_true,
      component_eq_Ioo hq.1,hq,true_and,if_true]
  · simp [retainedCell,retainedTimes,hq]

/-- Genuine joint Borel membership in a retained actual component cell. -/
theorem measurableSet_joint_retainedCell (H lambda : ℝ) (q : ℚ) :
    MeasurableSet {p : Path × (ℝ × ℝ) | p.2 ∈ retainedCell H lambda q p.1} := by
  have hrep : MeasurableSet {f : Path | Representative H (driftedReflectionPath lambda f) q} :=
    (measurableSet_representative H q).preimage (measurable_driftedReflectionPath lambda)
  have hl : Measurable (fun f : Path ↦ leftEndpoint H (q : ℝ) (driftedReflectionPath lambda f)) :=
    (measurable_leftEndpoint H (q : ℝ)).comp (measurable_driftedReflectionPath lambda)
  have hr : Measurable (fun f : Path ↦ rightEndpoint H (q : ℝ) (driftedReflectionPath lambda f)) :=
    (measurable_rightEndpoint H (q : ℝ)).comp (measurable_driftedReflectionPath lambda)
  have he : {p : Path × (ℝ × ℝ) | p.2 ∈ retainedCell H lambda q p.1} =
      {p | Representative H (driftedReflectionPath lambda p.1) q ∧
        leftEndpoint H (q : ℝ) (driftedReflectionPath lambda p.1) < p.2.1 ∧
          p.2.1 < rightEndpoint H (q : ℝ) (driftedReflectionPath lambda p.1)} := by
    ext p
    exact mem_retainedCell_iff H lambda q p.1 p.2
  rw [he]
  exact (hrep.preimage measurable_fst).inter
    ((measurableSet_lt (hl.comp measurable_fst) measurable_snd.fst).inter
      (measurableSet_lt measurable_snd.fst (hr.comp measurable_fst)))

def spatialCounts (H lambda : ℝ) (p : Path × PointMeasure (ℝ × ℝ)) : ℚ → ℕ :=
  fun q ↦ count p.2 (retainedCell H lambda q p.1)

theorem measurable_spatialCounts (H lambda : ℝ) : Measurable (spatialCounts H lambda) :=
  measurable_pi_lambda _ (fun q ↦ MeasurableMovingPointCounts.measurable_moving_count
    (retainedCell H lambda q) (measurableSet_joint_retainedCell H lambda q))

def actualSpatialCounts (H lambda : ℝ) (p : (ℕ → ℝ) × PointMeasure (ℝ × ℝ)) : ℚ → ℕ :=
  spatialCounts H lambda (measurablePath p.1,p.2)

theorem measurable_actualSpatialCounts (H lambda : ℝ) : Measurable (actualSpatialCounts H lambda) :=
  (measurable_spatialCounts H lambda).comp
    (f := fun p : (ℕ → ℝ) × PointMeasure (ℝ × ℝ) ↦ (measurablePath p.1,p.2))
    ((measurable_measurablePath.comp measurable_fst).prodMk measurable_snd)

end PerronWright.BrownianClippedExcursionMovingCounts
