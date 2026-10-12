import PerronWright.Probability.BrownianExcursionPointProcess
import PerronWright.Probability.BrownianFullHorizonMarkJointLaw

/-!
# The actual full Brownian size--surplus point-process probability law

The source is the constructed continuous Brownian path jointly with the
genuine full-area independent Poisson marking kernel. The target sigma
algebra is the existing vague-Borel point space; finite window laws use
the existing weak-Borel compact point spaces. The exceptional gate is
proved irrelevant under the actual original Gaussian-source joint law.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal CompactlySupported

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionPointProcessLaw

open BrownianPathLaw BrownianGaussianSkeleton BrownianPathReflectionLaw
open BrownianExcursionWindowPointMeasure BrownianExcursionAtomicMeasure BrownianExcursionPointProcess
open BrownianFullHorizonExcursions FullHorizonExcursionComponents FullHorizonExcursionSection
open BrownianFullHorizonPoissonMarks BrownianFullHorizonMarkJointLaw
open ComponentGlobalPointProcess LocallyFinitePointMeasureVague GlobalPointMeasureCharts
open PositiveSizeSurplusExhaustion

def pathInput (p : Path × (ℕ → ℕ)) : Input := (p.1,rationalCount p.2)

theorem measurable_countField : Measurable rationalCount :=
  measurable_pi_lambda _ (fun q ↦ measurable_pi_apply (Encodable.encode q))

theorem measurable_pathInput : Measurable pathInput :=
  measurable_fst.prodMk (measurable_countField.comp measurable_snd)

def actualInput (p : (ℕ → ℝ) × (ℕ → ℕ)) : Input := (measurablePath p.1,rationalCount p.2)

theorem measurable_actualInput : Measurable actualInput :=
  (measurable_measurablePath.comp measurable_fst).prodMk
    (measurable_countField.comp measurable_snd)

def law (lambda : ℝ) : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  ⟨(pathJointLaw lambda).map (process lambda ∘ pathInput),
    Measure.isProbabilityMeasure_map ((measurable_process lambda).comp measurable_pathInput).aemeasurable⟩

@[simp] theorem law_toMeasure (lambda : ℝ) :
    (law lambda : Measure (LocalPointMeasure PositiveSizeSurplus)) =
      (pathJointLaw lambda).map (process lambda ∘ pathInput) := rfl

def windowLaw (lambda : ℝ) (m : ℕ) : ProbabilityMeasure (Chart m) :=
  ⟨(pathJointLaw lambda).map (windowPointMeasure lambda m ∘ pathInput),
    Measure.isProbabilityMeasure_map
      ((measurable_windowPointMeasure lambda m).comp measurable_pathInput).aemeasurable⟩

theorem actualJointLaw_map_process (lambda : ℝ) :
    (actualJointLaw lambda).map (process lambda ∘ actualInput) =
      (law lambda : Measure (LocalPointMeasure PositiveSizeSurplus)) := by
  have hm : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ (measurablePath p.1,p.2)) :=
    (measurable_measurablePath.comp measurable_fst).prodMk measurable_snd
  rw [law_toMeasure,← actualJointLaw_map_to_path lambda,
    Measure.map_map ((measurable_process lambda).comp measurable_pathInput) hm]
  rfl

theorem hasLaw_actual_process (lambda : ℝ) :
    HasLaw (process lambda ∘ actualInput)
      (law lambda : Measure (LocalPointMeasure PositiveSizeSurplus)) (actualJointLaw lambda) :=
  ⟨((measurable_process lambda).comp measurable_actualInput).aemeasurable,
    actualJointLaw_map_process lambda⟩

theorem actualJointLaw_map_window (lambda : ℝ) (m : ℕ) :
    (actualJointLaw lambda).map (windowPointMeasure lambda m ∘ actualInput) =
      (windowLaw lambda m : Measure (Chart m)) := by
  have hm : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ (measurablePath p.1,p.2)) :=
    (measurable_measurablePath.comp measurable_fst).prodMk measurable_snd
  change _ = (pathJointLaw lambda).map (windowPointMeasure lambda m ∘ pathInput)
  rw [← actualJointLaw_map_to_path lambda,
    Measure.map_map ((measurable_windowPointMeasure lambda m).comp measurable_pathInput) hm]
  rfl

theorem ae_actual_good (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda, Good lambda (measurablePath p.1) := by
  apply ae_actualJointLaw_of_ae_source lambda (P := fun x ↦ Good lambda (measurablePath x))
  filter_upwards [BrownianLongExcursionLocalFiniteness.ae_all_actual_long_excursions_finite]
    with x hx
  intro m
  exact (hx lambda (lower m) (lower_pos m)).1

/-- Under the original Gaussian-source joint law the process is exactly
the untruncated, ungated full-excursion representative Dirac sum. -/
theorem ae_actual_process_eq_full_sum (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda,
      (process lambda (actualInput p) : Measure PositiveSizeSurplus) =
        Measure.sum (fun q : ℚ ↦
          if Representative (driftedReflectionPath lambda (measurablePath p.1)) q then
            Measure.dirac (atom lambda (actualInput p) q) else 0) := by
  have hp := ae_actualJointLaw_of_ae_source lambda ae_all_actual_excursion_properties
  filter_upwards [ae_actual_good lambda,hp] with p hg hp
  change BrownianExcursionAtomicMeasure.measure lambda (actualInput p) = _
  unfold BrownianExcursionAtomicMeasure.measure
  congr 1
  funext q
  by_cases hq : Representative (driftedReflectionPath lambda (measurablePath p.1)) q
  · have hl : 0 < lengthValue lambda q (measurablePath p.1) :=
      (hp lambda (q : ℝ) hq.1).2.2.2.2.2.2
    simp only [active,actualInput,hg,hq,hl,true_and,mem_ofPred_eq,if_pos]
  · simp only [active,actualInput,hq,and_false,false_and,mem_ofPred_eq]

theorem ae_actual_atom_size (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda, ∀ q : ℚ,
      Representative (driftedReflectionPath lambda (measurablePath p.1)) q →
        (atom lambda (actualInput p) q).1.val = lengthValue lambda q (measurablePath p.1) := by
  filter_upwards [ae_actualJointLaw_of_ae_source lambda ae_all_actual_excursion_properties] with p hp
  intro q hq
  have hl : 0 < lengthValue lambda q (measurablePath p.1) :=
    (hp lambda (q : ℝ) hq.1).2.2.2.2.2.2
  simp only [atom,positiveSize,actualInput,dif_pos hl]

theorem actual_atom_surplus (lambda : ℝ) (p : (ℕ → ℝ) × (ℕ → ℕ)) (q : ℚ) :
    (atom lambda (actualInput p) q).2 = rationalCount p.2 q := rfl

end PerronWright.BrownianExcursionPointProcessLaw
