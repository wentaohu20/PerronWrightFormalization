import PerronWright.Probability.BrownianFullExcursionSpatialMarkIdentification
import PerronWright.Probability.BrownianClippedSpatialJointMarkLaw

/-!
# Full spatial atoms realize the actual full Brownian joint marking law

The genuine countable spatial construction, evaluated in actual moving
full excursion cells, has the same complete source/count joint law as
the true full-area Poisson marking kernel. Conditional law identification
and moving-cell measurability are proved in the imported leaves.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullExcursionSpatialJointMarkLaw

open BrownianPathLaw BrownianFullExcursionMovingCounts BrownianFullExcursionSpatialMarkIdentification
open BrownianFullHorizonSpatialKernel BrownianClippedSpatialJointMarkLaw

theorem pathJointLaw_map_counts_eq_markJointLaw (lambda : ℝ) :
    (pathJointLaw lambda).map
      (fun p : Path × SpatialAtoms ↦ (p.1,spatialCounts lambda p)) =
    (BrownianFullHorizonPoissonMarks.pathJointLaw lambda).map
      (fun p : Path × (ℕ → ℕ) ↦ (p.1,BrownianFullHorizonPoissonMarks.rationalCount p.2)) := by
  apply joint_pair_map_eq pathLaw (spatialKernel lambda)
    (CountablePoissonKernel.rateKernel
      (BrownianFullHorizonPoissonMarks.naturalRates lambda)
      (BrownianFullHorizonPoissonMarks.measurable_naturalRates lambda))
    (spatialCounts lambda)
    (fun p : Path × (ℕ → ℕ) ↦ BrownianFullHorizonPoissonMarks.rationalCount p.2)
    (measurable_spatialCounts lambda) (measurable_rationalCount.comp measurable_snd)
  intro f
  exact spatial_count_law_eq_markLaw lambda f

/-- Terminal actual-source identity: full spatial points counted in full
moving excursion cells realize the genuine entire full-area mark law. -/
theorem actualJointLaw_map_counts_eq_markJointLaw (lambda : ℝ) :
    (actualJointLaw lambda).map
      (fun p : (ℕ → ℝ) × SpatialAtoms ↦ (p.1,actualSpatialCounts lambda p)) =
    (BrownianFullHorizonPoissonMarks.actualJointLaw lambda).map
      (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ (p.1,BrownianFullHorizonPoissonMarks.rationalCount p.2)) := by
  apply joint_pair_map_eq BrownianGaussianSkeleton.rationalLaw (actualSpatialKernel lambda)
    (CountablePoissonKernel.rateKernel
      (BrownianFullHorizonPoissonMarks.actualRates lambda)
      (BrownianFullHorizonPoissonMarks.measurable_actualRates lambda))
    (actualSpatialCounts lambda)
    (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ BrownianFullHorizonPoissonMarks.rationalCount p.2)
    (measurable_actualSpatialCounts lambda) (measurable_rationalCount.comp measurable_snd)
  intro x
  exact spatial_count_law_eq_markLaw lambda (measurablePath x)

theorem hasLaw_actual_source_spatial_counts (lambda : ℝ) :
    HasLaw (fun p : (ℕ → ℝ) × SpatialAtoms ↦ (p.1,actualSpatialCounts lambda p))
      ((BrownianFullHorizonPoissonMarks.actualJointLaw lambda).map
        (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ (p.1,BrownianFullHorizonPoissonMarks.rationalCount p.2)))
      (actualJointLaw lambda) :=
  ⟨(measurable_fst.prodMk (measurable_actualSpatialCounts lambda)).aemeasurable,
    actualJointLaw_map_counts_eq_markJointLaw lambda⟩

end PerronWright.BrownianFullExcursionSpatialJointMarkLaw
