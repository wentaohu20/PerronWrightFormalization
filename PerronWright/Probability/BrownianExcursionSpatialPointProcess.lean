import PerronWright.Probability.BrownianExcursionPointProcessLaw
import PerronWright.Probability.BrownianFullExcursionSpatialActualCounts

/-!
# Full spatial PPP counts realize the genuine excursion point process

Both the endpoint-coordinate moving counts and counts in the literal
full connected-component cells push to the actual vague-Borel law.
The equality uses the already proved complete source/count joint law;
no conditional independence or measurable counting interface is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionSpatialPointProcess

open BrownianPathLaw BrownianExcursionWindowPointMeasure BrownianExcursionAtomicMeasure
open BrownianExcursionPointProcess BrownianExcursionPointProcessLaw
open BrownianFullHorizonSpatialKernel BrownianFullExcursionMovingCounts
open BrownianFullExcursionSpatialJointMarkLaw BrownianFullExcursionSpatialActualCounts
open ComponentGlobalPointProcess LocallyFinitePointMeasureVague

def pathSpatialProcess (lambda : ℝ) (p : Path × SpatialAtoms) :
    LocalPointMeasure PositiveSizeSurplus := process lambda (p.1,spatialCounts lambda p)

theorem measurable_pathSpatialProcess (lambda : ℝ) : Measurable (pathSpatialProcess lambda) :=
  (measurable_process lambda).comp (measurable_fst.prodMk (measurable_spatialCounts lambda))

theorem pathSpatialProcess_law (lambda : ℝ) :
    (pathJointLaw lambda).map (pathSpatialProcess lambda) =
      (law lambda : Measure (LocalPointMeasure PositiveSizeSurplus)) := by
  have hmMark : Measurable (fun p : Path × (ℕ → ℕ) ↦
      (p.1,BrownianFullHorizonPoissonMarks.rationalCount p.2)) :=
    BrownianExcursionPointProcessLaw.measurable_pathInput
  change (pathJointLaw lambda).map (process lambda ∘ (fun p ↦ (p.1,spatialCounts lambda p))) = _
  rw [← Measure.map_map (measurable_process lambda)
      (measurable_fst.prodMk (measurable_spatialCounts lambda)),
    pathJointLaw_map_counts_eq_markJointLaw,
    Measure.map_map (measurable_process lambda) hmMark]
  rfl

def actualSpatialProcess (lambda : ℝ) (p : (ℕ → ℝ) × SpatialAtoms) :
    LocalPointMeasure PositiveSizeSurplus := process lambda (measurablePath p.1,actualSpatialCounts lambda p)

theorem measurable_actualSpatialProcess (lambda : ℝ) : Measurable (actualSpatialProcess lambda) :=
  (measurable_process lambda).comp
    ((measurable_measurablePath.comp measurable_fst).prodMk (measurable_actualSpatialCounts lambda))

def sourceInput (p : (ℕ → ℝ) × (ℚ → ℕ)) : Input := (measurablePath p.1,p.2)

theorem measurable_sourceInput : Measurable sourceInput :=
  (measurable_measurablePath.comp measurable_fst).prodMk measurable_snd

theorem actualSpatialProcess_law (lambda : ℝ) :
    (actualJointLaw lambda).map (actualSpatialProcess lambda) =
      (law lambda : Measure (LocalPointMeasure PositiveSizeSurplus)) := by
  have hmPair : Measurable (fun p : (ℕ → ℝ) × SpatialAtoms ↦ (p.1,actualSpatialCounts lambda p)) :=
    measurable_fst.prodMk (measurable_actualSpatialCounts lambda)
  have hmMark : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦
      (p.1,BrownianFullHorizonPoissonMarks.rationalCount p.2)) :=
    measurable_fst.prodMk (BrownianExcursionPointProcessLaw.measurable_countField.comp measurable_snd)
  change (actualJointLaw lambda).map
    ((process lambda ∘ sourceInput) ∘ (fun p ↦ (p.1,actualSpatialCounts lambda p))) = _
  rw [← Measure.map_map ((measurable_process lambda).comp measurable_sourceInput)
      hmPair,
    actualJointLaw_map_counts_eq_markJointLaw,
    Measure.map_map ((measurable_process lambda).comp measurable_sourceInput)
      hmMark]
  exact actualJointLaw_map_process lambda

/-- Surplus coordinates here are counts in the literal full connected
component cells, not just a proxy coordinate or a supplied count field. -/
def actualComponentProcess (lambda : ℝ) (p : (ℕ → ℝ) × SpatialAtoms) :
    LocalPointMeasure PositiveSizeSurplus := process lambda (measurablePath p.1,actualComponentCounts lambda p)

theorem ae_actualComponentProcess_eq_spatial (lambda : ℝ) :
    actualComponentProcess lambda =ᵐ[actualJointLaw lambda] actualSpatialProcess lambda := by
  filter_upwards [ae_actualComponentCounts_eq_spatialCounts lambda] with p hp
  exact congrArg (fun c : ℚ → ℕ ↦ process lambda (measurablePath p.1,c)) hp

theorem aemeasurable_actualComponentProcess (lambda : ℝ) :
    AEMeasurable (actualComponentProcess lambda) (actualJointLaw lambda) :=
  (measurable_actualSpatialProcess lambda).aemeasurable.congr
    (ae_actualComponentProcess_eq_spatial lambda).symm

/-- Terminal full-horizon spatial realization in the actual vague-Borel
locally finite size--surplus point-measure space. -/
theorem actualComponentProcess_law (lambda : ℝ) :
    (actualJointLaw lambda).map (actualComponentProcess lambda) =
      (law lambda : Measure (LocalPointMeasure PositiveSizeSurplus)) := by
  rw [Measure.map_congr (ae_actualComponentProcess_eq_spatial lambda)]
  exact actualSpatialProcess_law lambda

theorem hasLaw_actualComponentProcess (lambda : ℝ) :
    HasLaw (actualComponentProcess lambda)
      (law lambda : Measure (LocalPointMeasure PositiveSizeSurplus)) (actualJointLaw lambda) :=
  ⟨aemeasurable_actualComponentProcess lambda,actualComponentProcess_law lambda⟩

end PerronWright.BrownianExcursionSpatialPointProcess
