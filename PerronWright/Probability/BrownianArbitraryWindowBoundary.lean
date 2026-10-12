import PerronWright.Probability.BrownianArbitraryWindowLaw
import PerronWright.Probability.BrownianActualFactorialDensity
import PerronWright.Probability.CompactWindowBoundary

/-!
# Genuine boundary nullity of arbitrary Brownian windows

The proved actual first factorial density gives zero expected mass at
each fixed positive size and surplus. Countable surplus exchange and
the literal closed-window restriction then give actual boundary nullity.
-/

open MeasureTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianArbitraryWindowBoundary

open BrownianExcursionAtomicMeasure BrownianExcursionPointProcessLaw
open BrownianFullHorizonPoissonMarks ComponentGlobalPointProcess ComponentWindowPointMeasures
open FinitePointMeasureCompact FinitePointMeasureFactorialKernel
open FinitePointMeasureFactorialMeasure FinitePointMeasureRectangleFactorials
open FinitePointMeasureMeasurable BrownianExcursionFactorialTests
open BrownianExcursionRectangleFactorials CompactWindowBoundary

private theorem factorialTest_one_eq_eval (c : ℝ) (r : ℕ)
    (η : PointMeasure PositiveSizeSurplus) :
    factorialTest (fun _ : Fin 1 ↦ c) (fun _ ↦ c) (fun _ ↦ r) 1 η =
      ((η : FiniteMeasure PositiveSizeSurplus) : Measure PositiveSizeSurplus)
        (BrownianExcursionCampbellWeights.cell c c r) := by
  unfold factorialTest rectangleTest testStatistic
  rw [lintegral_indicator_one (MeasurableSet.pi countable_univ
    (fun i _ ↦ measurableSet_cells (fun _ ↦ c) (fun _ ↦ c) (fun _ ↦ r) i)),
    factorialMeasure_rectangle]
  · change (rectangleFactorial η (fun _ : Fin 1 ↦
      BrownianExcursionCampbellWeights.cell c c r) : ℝ≥0∞) = _
    rw [rectangleFactorial_constant η _ (BrownianExcursionCampbellWeights.measurableSet_cell c c r)]
    simp only [Fintype.card_fin, Nat.descFactorial_one]
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.natCast_ne_top _) (measure_ne_top _ _)).mp
    simpa only [ENNReal.toReal_natCast, measureReal_def] using
      (measure_real_eq_count η (BrownianExcursionCampbellWeights.measurableSet_cell c c r)).symm
  · intro i
    exact measurableSet_cells (fun _ ↦ c) (fun _ ↦ c) (fun _ ↦ r) i

theorem singleton_cell_lintegral_eq_zero (lambda c : ℝ) (hc : 0 < c) (r : ℕ) :
    (∫⁻ η : PointMeasure PositiveSizeSurplus,
      ((η : FiniteMeasure PositiveSizeSurplus) : Measure PositiveSizeSurplus)
      (BrownianExcursionCampbellWeights.cell c c r)
      ∂(BrownianExcursionCompactWindows.law lambda
        (BrownianExcursionCampbellWeights.cell c c r)
        (BrownianExcursionCampbellWeights.isCompact_cell c c r hc) : Measure _)) = 0 := by
  have h := BrownianActualFactorialDensity.actual_window_factorial_density lambda
    (fun _ : Fin 1 ↦ c) (fun _ ↦ c) (fun _ ↦ r) (fun _ ↦ hc) 1 measurable_const
  have hK : windowSet (fun _ : Fin 1 ↦ c) (fun _ ↦ c) (fun _ ↦ r) =
      BrownianExcursionCampbellWeights.cell c c r := by
    ext z
    simp [BrownianExcursionRectangleFactorials.windowSet, cells]
  have hB : {xs : Fin 1 → ℝ | ∀ i, xs i ∈ Icc c c} = {fun _ ↦ c} := by
    ext xs
    simp only [mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun h ↦ funext (fun i ↦ le_antisymm (h i).2 (h i).1),
      fun h i ↦ by rw [h]; exact ⟨le_rfl, le_rfl⟩⟩
  change (∫⁻ η : PointMeasure PositiveSizeSurplus,
    factorialTest (fun _ : Fin 1 ↦ c) (fun _ ↦ c) (fun _ ↦ r) 1 η
    ∂(BrownianExcursionCompactWindows.law lambda
      (windowSet (fun _ : Fin 1 ↦ c) (fun _ ↦ c) (fun _ ↦ r)) _ : Measure _)) = _ at h
  simp_rw [hK, factorialTest_one_eq_eval] at h
  simpa only [hB, Measure.restrict_singleton', lintegral_zero_measure] using h

theorem ae_process_singleton_cell_eq_zero (lambda c : ℝ) (hc : 0 < c) (r : ℕ) :
    ∀ᵐ p ∂pathJointLaw lambda,
      (process lambda (pathInput p) : Measure PositiveSizeSurplus)
        (BrownianExcursionCampbellWeights.cell c c r) = 0 := by
  have h := singleton_cell_lintegral_eq_zero lambda c hc r
  change (∫⁻ η, _ ∂((pathJointLaw lambda).map
    (BrownianExcursionCompactWindows.window lambda
      (BrownianExcursionCampbellWeights.cell c c r) ∘ pathInput))) = 0 at h
  rw [lintegral_map (measurable_eval (BrownianExcursionCampbellWeights.measurableSet_cell c c r))
    ((BrownianExcursionCompactWindows.measurable_window lambda _
      (BrownianExcursionCampbellWeights.measurableSet_cell c c r)).comp measurable_pathInput)] at h
  have he (p : BrownianPathLaw.Path × (ℕ → ℕ)) :
      ((BrownianExcursionCompactWindows.window lambda
        (BrownianExcursionCampbellWeights.cell c c r) (pathInput p) :
          FiniteMeasure PositiveSizeSurplus) : Measure PositiveSizeSurplus)
        (BrownianExcursionCampbellWeights.cell c c r) =
      (process lambda (pathInput p) : Measure PositiveSizeSurplus)
        (BrownianExcursionCampbellWeights.cell c c r) := by
    rw [BrownianExcursionCompactWindows.window_eq_restrict_process lambda _
      (BrownianExcursionCampbellWeights.isCompact_cell c c r hc),
      Measure.restrict_apply (BrownianExcursionCampbellWeights.measurableSet_cell c c r),
      inter_self]
  simp only [Function.comp_apply, he] at h
  have hm : Measurable (fun p ↦ (process lambda (pathInput p) : Measure PositiveSizeSurplus)
      (BrownianExcursionCampbellWeights.cell c c r)) := by
    have hm0 := ((measurable_eval (BrownianExcursionCampbellWeights.measurableSet_cell c c r)).comp
      ((BrownianExcursionCompactWindows.measurable_window lambda _
        (BrownianExcursionCampbellWeights.measurableSet_cell c c r)).comp measurable_pathInput))
    change Measurable (fun p : BrownianPathLaw.Path × (ℕ → ℕ) ↦
      ((BrownianExcursionCompactWindows.window lambda
        (BrownianExcursionCampbellWeights.cell c c r) (pathInput p) :
          FiniteMeasure PositiveSizeSurplus) : Measure PositiveSizeSurplus)
        (BrownianExcursionCampbellWeights.cell c c r)) at hm0
    simpa only [he] using hm0
  exact (lintegral_eq_zero_iff hm).mp h

theorem ae_process_size_eq_zero (lambda c : ℝ) :
    ∀ᵐ p ∂pathJointLaw lambda,
      (process lambda (pathInput p) : Measure PositiveSizeSurplus)
        {z | z.1.val = c} = 0 := by
  by_cases hc : 0 < c
  · filter_upwards [ae_all_iff.mpr (fun r : ℕ ↦
      ae_process_singleton_cell_eq_zero lambda c hc r)] with p hp
    have hB : {z : PositiveSizeSurplus | z.1.val = c} =
        ⋃ r : ℕ, BrownianExcursionCampbellWeights.cell c c r := by
      ext z
      constructor
      · intro hz
        refine mem_iUnion.mpr ⟨z.2, ?_⟩
        change ((c ≤ z.1.val ∧ z.1.val ≤ c) ∧ z.2 ≤ z.2) ∧ z.2 = z.2
        exact ⟨⟨⟨hz.ge, hz.le⟩, le_rfl⟩, rfl⟩
      · intro hz
        obtain ⟨r, hr⟩ := mem_iUnion.mp hz
        exact le_antisymm hr.1.1.2 hr.1.1.1
    rw [hB]
    exact measure_iUnion_null hp
  · have hB : {z : PositiveSizeSurplus | z.1.val = c} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hc (hz ▸ z.1.property)
    simp only [hB, measure_empty]
    exact Eventually.of_forall (fun _ ↦ trivial)

theorem ae_boundary_eq_zero (lambda a b : ℝ) (R : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (c : ℝ) :
    ∀ᵐ η : PointMeasure (SurplusWindow a b R)
      ∂(BrownianArbitraryWindowLaw.law lambda a b R ha hab :
      Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (boundary a b R c) = 0 := by
  rw [BrownianArbitraryWindowLaw.law_eq_actual_map]
  apply (ae_map_iff
    ((BrownianArbitraryWindowLaw.measurable_pointMeasure lambda a b R ha hab).comp
      measurable_pathInput).aemeasurable
    ((measurable_eval (measurableSet_boundary a b R c)).eq measurable_const).setOf).mpr
  filter_upwards [ae_process_size_eq_zero lambda c] with p hp
  let B : Set PositiveSizeSurplus := {z | z.1.val = c}
  have hB : MeasurableSet B :=
    ((measurable_subtype_coe.comp measurable_fst).eq measurable_const).setOf
  have he := congrArg (fun μ : Measure PositiveSizeSurplus ↦ μ B)
    (BrownianArbitraryWindowLaw.pointMeasure_embedded lambda a b R ha (pathInput p))
  rw [Measure.map_apply (measurable_positiveWindowEmbedding a b R ha) hB,
    Measure.restrict_apply hB] at he
  change ((BrownianArbitraryWindowLaw.pointMeasure lambda a b R ha (pathInput p) :
    FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
    (boundary a b R c) = 0
  exact he.trans (measure_mono_null inter_subset_left hp)

theorem ae_sizeSurplusCell_frontier_eq_zero (lambda a b : ℝ) (R : ℕ)
    (ha : 0 < a) (hab : a ≤ b) (J : Set ℝ) (S : Set ℕ) (lo hi : ℝ)
    (hJ : frontier J ⊆ {lo, hi}) :
    ∀ᵐ η : PointMeasure (SurplusWindow a b R)
      ∂(BrownianArbitraryWindowLaw.law lambda a b R ha hab :
      Measure (PointMeasure (SurplusWindow a b R))),
      ((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (frontier (windowEmbedding a b R ⁻¹' (J ×ˢ S))) = 0 := by
  filter_upwards [ae_boundary_eq_zero lambda a b R ha hab lo,
    ae_boundary_eq_zero lambda a b R ha hab hi] with η hl hh
  exact measure_mono_null (frontier_sizeSurplusCell_subset a b R J S lo hi hJ)
    (measure_union_null hl hh)

end PerronWright.BrownianArbitraryWindowBoundary
