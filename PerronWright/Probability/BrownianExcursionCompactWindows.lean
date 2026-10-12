import PerronWright.Probability.BrownianExcursionPointProcessLaw

/-!
# Every genuine compact window is a measurable finite point process

These windows may be any compact Borel subset of positive size times
surplus, not just the canonical exhaustion. Their actual weak-Borel
finite point measures equal the literal global measure restrictions.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionCompactWindows

open BrownianExcursionWindowPointMeasure BrownianExcursionAtomicMeasure BrownianExcursionPointProcess
open BrownianExcursionPointProcessLaw BrownianPathReflectionLaw FullHorizonExcursionSection
open ComponentGlobalPointProcess PositiveSizeSurplusExhaustion CountableFiniteAtomSampling
open FinitePointMeasureCompact BrownianFullHorizonPoissonMarks

def selection (lambda : ℝ) (K : Set PositiveSizeSurplus) (p : Input) : Set ℚ :=
  {q | q ∈ active lambda p ∧ atom lambda p q ∈ K}

theorem measurable_selection (lambda : ℝ) (K : Set PositiveSizeSurplus) (hK : MeasurableSet K) :
    Measurable (selection lambda K) := by
  apply measurable_set_iff.mpr
  intro q
  apply measurableSet_setOfPred.mp
  exact (((measurableSet_good lambda).preimage measurable_fst).inter
    (((measurableSet_representative q).preimage
      ((measurable_driftedReflectionPath lambda).comp measurable_fst)).inter
      (measurableSet_lt measurable_const ((measurable_lengthValue lambda q).comp measurable_fst)))).inter
        ((measurable_atom lambda q) hK)

theorem finite_selection (lambda : ℝ) (K : Set PositiveSizeSurplus) (hK : IsCompact K)
    (p : Input) : (selection lambda K p).Finite := by
  obtain ⟨m,hm⟩ := exists_compact_subset_window hK
  apply (finite_selected lambda m p).subset
  intro q hq
  rw [selected_eq_active_window]
  exact ⟨hq.1,hm hq.2⟩

def window (lambda : ℝ) (K : Set PositiveSizeSurplus) (p : Input) : PointMeasure PositiveSizeSurplus :=
  pointMeasure (selection lambda K) (atom lambda) p

/-- The target has the already defined finite-measure weak Borel sigma
structure, not a newly stipulated evaluation sigma structure. -/
theorem measurable_window (lambda : ℝ) (K : Set PositiveSizeSurplus) (hK : MeasurableSet K) :
    Measurable (window lambda K) :=
  measurable_pointMeasure _ (measurable_selection lambda K hK) _
    (measurable_pi_lambda _ (fun q ↦ measurable_atom lambda q))

theorem window_eq_restrict_process (lambda : ℝ) (K : Set PositiveSizeSurplus) (hK : IsCompact K)
    (p : Input) :
    ((window lambda K p : FiniteMeasure PositiveSizeSurplus) : Measure PositiveSizeSurplus) =
      (process lambda p : Measure PositiveSizeSurplus).restrict K := by
  have hf := finite_selection lambda K hK p
  have ht : selection lambda K p = (hf.toFinset : Set ℚ) := by ext q; simp
  unfold window
  rw [pointMeasure_eq_ofFinset _ _ _ _ ht]
  exact (restrict_sum_dirac_eq_ofFinset (active lambda p) (atom lambda p) K hK.measurableSet hf).symm

theorem window_size (lambda : ℝ) (K : Set PositiveSizeSurplus) (hK : IsCompact K) (p : Input) :
    size (window lambda K p) = (finite_selection lambda K hK p).toFinset.card :=
  size_pointMeasure _ _ _ _

def law (lambda : ℝ) (K : Set PositiveSizeSurplus) (hK : IsCompact K) :
    ProbabilityMeasure (PointMeasure PositiveSizeSurplus) :=
  ⟨(pathJointLaw lambda).map (window lambda K ∘ pathInput),
    Measure.isProbabilityMeasure_map
      ((measurable_window lambda K hK.measurableSet).comp measurable_pathInput).aemeasurable⟩

theorem actualJointLaw_map_window (lambda : ℝ) (K : Set PositiveSizeSurplus) (hK : IsCompact K) :
    (actualJointLaw lambda).map (window lambda K ∘ actualInput) =
      (law lambda K hK : Measure (PointMeasure PositiveSizeSurplus)) := by
  have hm : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ (BrownianPathLaw.measurablePath p.1,p.2)) :=
    (BrownianPathLaw.measurable_measurablePath.comp measurable_fst).prodMk measurable_snd
  change _ = (pathJointLaw lambda).map (window lambda K ∘ pathInput)
  rw [← BrownianFullHorizonMarkJointLaw.actualJointLaw_map_to_path lambda,
    Measure.map_map ((measurable_window lambda K hK.measurableSet).comp measurable_pathInput) hm]
  rfl

end PerronWright.BrownianExcursionCompactWindows
