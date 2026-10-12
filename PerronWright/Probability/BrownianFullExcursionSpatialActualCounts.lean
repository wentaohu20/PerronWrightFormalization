import PerronWright.Probability.BrownianFullExcursionSpatialJointMarkLaw

/-!
# Literal full connected-component counts on the actual Brownian source

The terminal observable uses the actual full connected components, not
their measurable endpoint wrapper. Proved almost-sure full-return and
strip support discharge its finiteness and measurability and identify its
complete source/count joint law with the full excursion-area marks.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullExcursionSpatialActualCounts

open BrownianFullHorizonSpatialKernel BrownianFullHorizonSpatialSupport
open BrownianFullHorizonSpatialCounts BrownianFullExcursionSpatialCells
open BrownianFullExcursionMovingCounts BrownianFullExcursionSpatialJointMarkLaw BrownianPathLaw

def actualComponentCell (lambda : ℝ) (q : ℚ) (x : ℕ → ℝ) : Set (ℝ × ℝ) :=
  (if FullHorizonExcursionSection.Representative
      (BrownianActualWindowExcursions.actualPath lambda x) q then
    FullHorizonExcursionComponents.component
      (BrownianActualWindowExcursions.actualPath lambda x) (q : ℝ) else ∅) ×ˢ univ

def actualComponentCounts (lambda : ℝ) (p : (ℕ → ℝ) × SpatialAtoms) (q : ℚ) : ℕ :=
  spatialCount p.2 (actualComponentCell lambda q p.1)

theorem ae_actualComponentCell_eq_retainedCell (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda, ∀ mu : ℝ, ∀ q : ℚ,
      actualComponentCell mu q p.1 = retainedCell mu q (measurablePath p.1) := by
  filter_upwards [ae_actual_joint_retainedTimes_eq_component lambda] with p hp
  intro mu q
  exact congrArg (fun A : Set ℝ ↦ A ×ˢ (univ : Set ℝ)) (hp mu q).symm

theorem ae_actualComponentCounts_eq_spatialCounts (lambda : ℝ) :
    actualComponentCounts lambda =ᵐ[actualJointLaw lambda] actualSpatialCounts lambda := by
  filter_upwards [ae_actualComponentCell_eq_retainedCell lambda] with p hp
  funext q
  exact congrArg (spatialCount p.2) (hp lambda q)

theorem aemeasurable_actualComponentCounts (lambda : ℝ) :
    AEMeasurable (actualComponentCounts lambda) (actualJointLaw lambda) :=
  (measurable_actualSpatialCounts lambda).aemeasurable.congr
    (ae_actualComponentCounts_eq_spatialCounts lambda).symm

/-- Every actual full retained component contains finitely many spatial
atoms, simultaneously for every drift parameter and rational anchor. -/
theorem ae_actualComponentCell_mass_ne_top (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda, ∀ mu : ℝ, ∀ q : ℚ,
      spatialMeasure p.2 (actualComponentCell mu q p.1) ≠ ∞ := by
  filter_upwards [ae_actualComponentCell_eq_retainedCell lambda,
    ae_actualJointLaw_stripSupported lambda] with p he hp
  intro mu q
  rw [he mu q]
  obtain ⟨N,hN⟩ := exists_retainedCell_subset_timeCut mu q (measurablePath p.1)
  exact spatialMeasure_ne_top_of_subset hp N
    (measurableSet_retainedCell mu q (measurablePath p.1)) hN

/-- Actual spatial counts in the literal full connected-component cells
realize the complete genuine full-area mark law jointly with the Gaussian
source, with no assumed excursion-measurability or independence interface. -/
theorem actualJointLaw_map_componentCounts_eq_markJointLaw (lambda : ℝ) :
    (actualJointLaw lambda).map
      (fun p : (ℕ → ℝ) × SpatialAtoms ↦ (p.1,actualComponentCounts lambda p)) =
    (BrownianFullHorizonPoissonMarks.actualJointLaw lambda).map
      (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ (p.1,BrownianFullHorizonPoissonMarks.rationalCount p.2)) := by
  have he : (fun p : (ℕ → ℝ) × SpatialAtoms ↦ (p.1,actualComponentCounts lambda p)) =ᵐ[actualJointLaw lambda]
      (fun p ↦ (p.1,actualSpatialCounts lambda p)) :=
    (ae_actualComponentCounts_eq_spatialCounts lambda).mono (fun p hp ↦ congrArg (Prod.mk p.1) hp)
  rw [Measure.map_congr he]
  exact actualJointLaw_map_counts_eq_markJointLaw lambda

theorem hasLaw_actual_source_componentCounts (lambda : ℝ) :
    HasLaw (fun p : (ℕ → ℝ) × SpatialAtoms ↦ (p.1,actualComponentCounts lambda p))
      ((BrownianFullHorizonPoissonMarks.actualJointLaw lambda).map
        (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ (p.1,BrownianFullHorizonPoissonMarks.rationalCount p.2)))
      (actualJointLaw lambda) :=
  ⟨measurable_fst.aemeasurable.prodMk (aemeasurable_actualComponentCounts lambda),
    actualJointLaw_map_componentCounts_eq_markJointLaw lambda⟩

end PerronWright.BrownianFullExcursionSpatialActualCounts
