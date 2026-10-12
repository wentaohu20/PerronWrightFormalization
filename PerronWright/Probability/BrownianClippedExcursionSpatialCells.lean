import PerronWright.Probability.BrownianWindowExcursionAreas
import PerronWright.Probability.BrownianUnderGraphDisjointCounts

/-!
# Literal spatial cells under nonrepeating clipped excursion components

Each retained component supplies its actual horizontal strip. The
intersection with the reflected under-graph region has planar volume
equal to the proved excursion integral. Distinct retained components
give disjoint cells, including the zero-rate inactive coordinates.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianClippedExcursionSpatialCells

open BrownianPathLaw BrownianPathReflectionLaw BrownianWindowExcursions
  BrownianWindowExcursionAreas BrownianReflectedAreaCounts
  BrownianUnderGraphIntensity BrownianUnderGraphPoissonLaw
  BrownianUnderGraphDisjointCounts FinitePointMeasureCompact

/-- Unit planar intensity over a literal measurable time subset. -/
theorem volume_time_strip_inter_region (lambda : ℝ) (a b : ℝ≥0) (f : Path)
    (A : Set ℝ) (hA : MeasurableSet A)
    (hsub : A ⊆ Icc (a : ℝ) (b : ℝ)) :
    volume ((A ×ˢ univ) ∩ region lambda a b f) =
      ENNReal.ofReal (∫ s in A, surface lambda f s) := by
  have hm := (hA.prod MeasurableSet.univ).inter (measurableSet_region lambda a b f)
  rw [Measure.volume_eq_prod, Measure.prod_apply hm]
  have hv (s : ℝ) : Prod.mk s ⁻¹' ((A ×ˢ univ) ∩ region lambda a b f) =
      if s ∈ A then Ioo 0 (surface lambda f s) else ∅ := by
    ext y
    by_cases hs : s ∈ A
    · simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true,
        region, mem_ofPred_eq, hs, if_true, mem_Ioo, true_and]
      exact and_iff_right (hsub hs)
    · simp only [mem_preimage, mem_inter_iff, mem_prod, hs, false_and,
        if_false, mem_empty_iff_false]
  simp only [hv]
  have hf : (fun s : ℝ ↦ volume (if s ∈ A then Ioo 0 (surface lambda f s) else ∅)) =
      A.indicator (fun s ↦ ENNReal.ofReal (surface lambda f s)) := by
    funext s
    by_cases hs : s ∈ A
    · simp [hs, Real.volume_Ioo]
    · simp [hs]
  rw [hf, lintegral_indicator hA]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((integrableOn_surface lambda a b f).mono_set hsub)
    (Filter.Eventually.of_forall (surface_nonneg lambda f))).symm

def retainedTimes (H lambda : ℝ) (q : ℚ) (f : Path) : Set ℝ :=
  if Representative H (driftedReflectionPath lambda f) q then
    component H (driftedReflectionPath lambda f) (q : ℝ) else ∅

def retainedCell (H lambda : ℝ) (q : ℚ) (f : Path) : Set (ℝ × ℝ) :=
  retainedTimes H lambda q f ×ˢ univ

theorem measurableSet_retainedTimes (H lambda : ℝ) (q : ℚ) (f : Path) :
    MeasurableSet (retainedTimes H lambda q f) := by
  unfold retainedTimes
  split_ifs
  · exact (isOpen_component _ _ _).measurableSet
  · exact MeasurableSet.empty

theorem measurableSet_retainedCell (H lambda : ℝ) (q : ℚ) (f : Path) :
    MeasurableSet (retainedCell H lambda q f) :=
  (measurableSet_retainedTimes H lambda q f).prod MeasurableSet.univ

theorem retainedTimes_subset_Icc (H : ℝ≥0) (lambda : ℝ) (q : ℚ) (f : Path) :
    retainedTimes H lambda q f ⊆ Icc 0 (H : ℝ) := by
  unfold retainedTimes
  split_ifs
  · intro s hs
    exact ⟨(component_subset _ _ _ hs).1.1.le, (component_subset _ _ _ hs).1.2.le⟩
  · exact empty_subset _

theorem retainedTimes_pairwise_disjoint (H lambda : ℝ) (f : Path) :
    Pairwise (fun q r : ℚ ↦ Disjoint (retainedTimes H lambda q f)
      (retainedTimes H lambda r f)) := by
  intro q r hqr
  unfold retainedTimes
  split_ifs with hq hr hr
  · exact representative_components_disjoint hq hr hqr
  · simp
  · simp
  · simp

theorem retainedCell_pairwise_disjoint (H lambda : ℝ) (f : Path) :
    Pairwise (fun q r : ℚ ↦ Disjoint (retainedCell H lambda q f)
      (retainedCell H lambda r f)) := by
  intro q r hqr
  apply disjoint_left.mpr
  intro p hp hr
  exact disjoint_left.mp (retainedTimes_pairwise_disjoint H lambda f hqr) hp.1 hr.1

/-- Every literal retained spatial cell has its actual excursion area as intensity. -/
theorem volume_retainedCell_inter_region (H : ℝ≥0) (lambda : ℝ) (q : ℚ) (f : Path) :
    volume (retainedCell H lambda q f ∩ region lambda 0 H f) =
      (retainedArea H lambda q f : ℝ≥0∞) := by
  rw [retainedCell, volume_time_strip_inter_region lambda 0 H f _
    (measurableSet_retainedTimes H lambda q f) (retainedTimes_subset_Icc H lambda q f)]
  by_cases hq : Representative H (driftedReflectionPath lambda f) q
  · simp only [retainedTimes, retainedArea, if_pos hq]
    change ENNReal.ofReal (∫ s in component (H : ℝ) (driftedReflectionPath lambda f) (q : ℝ),
      realEval (driftedReflectionPath lambda f) s) = _
    rw [← excursionArea_eq_component_integral_all]
    exact ENNReal.ofReal_coe_nnreal
  · simp [retainedTimes, retainedArea, hq]

theorem intensity_retainedCell (H : ℝ≥0) (lambda : ℝ) (q : ℚ) (f : Path) :
    intensity lambda 0 H f (retainedCell H lambda q f) = retainedArea H lambda q f := by
  rw [intensity_apply _ _ _ _ (measurableSet_retainedCell H lambda q f),
    volume_retainedCell_inter_region]
  exact ENNReal.toNNReal_coe _

/-- The finite family of actual spatial excursion counts has the true area-rate product law. -/
theorem law_finite_retained_counts (H : ℝ≥0) (lambda : ℝ) (f : Path) (I : Finset ℚ) :
    (law lambda 0 H f).map (fun (η : PointMeasure (ℝ × ℝ)) (q : I) ↦
      count η (retainedCell H lambda q.1 f)) =
      PoissonCountKernel.finiteCountLaw (fun q : I ↦ retainedArea H lambda q.1 f) := by
  have hd : Pairwise (fun q r : I ↦ Disjoint (retainedCell H lambda q.1 f)
      (retainedCell H lambda r.1 f)) := by
    intro q r hqr
    exact retainedCell_pairwise_disjoint H lambda f (fun h ↦ hqr (Subtype.ext h))
  have he := FinitePoissonDisjointCellCounts.countLaw_eq_finitePoisson
    (intensity lambda 0 H f) (fun q : I ↦ retainedCell H lambda q.1 f) hd
    (fun q ↦ measurableSet_retainedCell H lambda q.1 f)
  simpa only [FinitePoissonDisjointCellCounts.countLaw, law, intensity_retainedCell] using he

end PerronWright.BrownianClippedExcursionSpatialCells
