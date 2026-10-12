import PerronWright.Probability.BrownianFullHorizonSpatialCounts
import PerronWright.Probability.BrownianFullHorizonExcursionAreas
import PerronWright.Probability.BrownianClippedExcursionSpatialCells

/-!
# Actual full-excursion spatial cells and their true area intensities

The measurable endpoint cells agree almost surely with the entire genuine
full excursion, not with an excursion clipped to a fixed horizon. They
are disjoint and each has exactly its actual retained excursion area as
the full under-graph intensity. Exceptional unbounded components use the
already explicit zero-area branch; actual Brownian paths never use it.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullExcursionSpatialCells

open BrownianPathLaw BrownianPathReflectionLaw BrownianGaussianSkeleton
open FullHorizonExcursionComponents FullHorizonExcursionSection FullHorizonExcursionEndpoints
open BrownianFullHorizonExcursionAreas BrownianFullHorizonExcursions
open BrownianFullHorizonSpatialKernel BrownianFullHorizonSpatialIntensity BrownianFullHorizonSpatialSupport

def retainedTimes (lambda : ℝ) (q : ℚ) (f : Path) : Set ℝ :=
  if Representative (driftedReflectionPath lambda f) q then
    Ioo (leftEndpoint (q : ℝ) (driftedReflectionPath lambda f))
      (rightEndpoint (q : ℝ) (driftedReflectionPath lambda f)) else ∅

def retainedCell (lambda : ℝ) (q : ℚ) (f : Path) : Set (ℝ × ℝ) := retainedTimes lambda q f ×ˢ univ

theorem measurableSet_retainedTimes (lambda : ℝ) (q : ℚ) (f : Path) :
    MeasurableSet (retainedTimes lambda q f) := by
  unfold retainedTimes
  split_ifs
  · exact measurableSet_Ioo
  · exact MeasurableSet.empty

theorem measurableSet_retainedCell (lambda : ℝ) (q : ℚ) (f : Path) :
    MeasurableSet (retainedCell lambda q f) :=
  (measurableSet_retainedTimes lambda q f).prod MeasurableSet.univ

theorem retainedTimes_subset_component (lambda : ℝ) (q : ℚ) (f : Path) :
    retainedTimes lambda q f ⊆ component (driftedReflectionPath lambda f) (q : ℝ) := by
  by_cases hq : Representative (driftedReflectionPath lambda f) q
  · rw [retainedTimes,if_pos hq]
    by_cases hb : BddAbove (component (driftedReflectionPath lambda f) (q : ℝ))
    · rw [component_eq_Ioo hq.1 hb]
    · have hr : rightEndpoint (q : ℝ) (driftedReflectionPath lambda f) = 0 := by
        simp only [rightEndpoint,if_pos hq.1,Real.sSup_of_not_bddAbove hb]
      rw [hr,Ioo_eq_empty_of_le (leftEndpoint_nonneg (q : ℝ) _)]
      exact empty_subset _
  · rw [retainedTimes,if_neg hq]
    exact empty_subset _

theorem retainedTimes_pairwise_disjoint (lambda : ℝ) (f : Path) :
    Pairwise (fun q r : ℚ ↦ Disjoint (retainedTimes lambda q f) (retainedTimes lambda r f)) := by
  intro q r hqr
  by_cases hq : Representative (driftedReflectionPath lambda f) q
  · by_cases hr : Representative (driftedReflectionPath lambda f) r
    · exact (representative_components_disjoint hq hr hqr).mono
        (retainedTimes_subset_component lambda q f) (retainedTimes_subset_component lambda r f)
    · simp [retainedTimes,hr]
  · simp [retainedTimes,hq]

theorem retainedCell_pairwise_disjoint (lambda : ℝ) (f : Path) :
    Pairwise (fun q r : ℚ ↦ Disjoint (retainedCell lambda q f) (retainedCell lambda r f)) := by
  intro q r hqr
  apply disjoint_left.mpr
  intro p hp hr
  exact disjoint_left.mp (retainedTimes_pairwise_disjoint lambda f hqr) hp.1 hr.1

theorem retainedTimes_subset_Icc (lambda : ℝ) (q : ℚ) (f : Path) :
    retainedTimes lambda q f ⊆ Icc (leftTime (q : ℝ) lambda f : ℝ)
      (rightTime (q : ℝ) lambda f : ℝ) := by
  rw [coe_leftTime,coe_rightTime]
  unfold retainedTimes
  split_ifs
  · exact Ioo_subset_Icc_self
  · exact empty_subset _

theorem exists_retainedCell_subset_timeCut (lambda : ℝ) (q : ℚ) (f : Path) :
    ∃ N : ℕ, retainedCell lambda q f ⊆ timeCut N := by
  obtain ⟨N,hN⟩ := exists_nat_gt (rightEndpoint (q : ℝ) (driftedReflectionPath lambda f))
  refine ⟨N,fun z hz ↦ ?_⟩
  have ht := (retainedTimes_subset_Icc lambda q f hz.1).2
  rw [coe_rightTime] at ht
  exact ht.trans_lt hN

theorem ae_all_retainedTimes_eq_component : ∀ᵐ x ∂rationalLaw, ∀ lambda : ℝ, ∀ q : ℚ,
    retainedTimes lambda q (measurablePath x) =
      if Representative (BrownianActualWindowExcursions.actualPath lambda x) q then
        component (BrownianActualWindowExcursions.actualPath lambda x) (q : ℝ) else ∅ := by
  filter_upwards [ae_all_actual_components_bddAbove] with x hx
  intro lambda q
  by_cases hq : Representative (BrownianActualWindowExcursions.actualPath lambda x) q
  · simp only [retainedTimes,BrownianActualWindowExcursions.actualPath] at hq ⊢
    rw [if_pos hq,if_pos hq]
    exact (component_eq_Ioo hq.1 (hx lambda (q : ℝ))).symm
  · simp only [retainedTimes,BrownianActualWindowExcursions.actualPath] at hq ⊢
    rw [if_neg hq,if_neg hq]

theorem mem_retainedCell_iff (lambda : ℝ) (q : ℚ) (f : Path) (z : ℝ × ℝ) :
    z ∈ retainedCell lambda q f ↔ Representative (driftedReflectionPath lambda f) q ∧
      leftEndpoint (q : ℝ) (driftedReflectionPath lambda f) < z.1 ∧
      z.1 < rightEndpoint (q : ℝ) (driftedReflectionPath lambda f) := by
  by_cases hq : Representative (driftedReflectionPath lambda f) q <;>
    simp [retainedCell,retainedTimes,hq]

theorem measurableSet_joint_retainedCell (lambda : ℝ) (q : ℚ) :
    MeasurableSet {p : Path × (ℝ × ℝ) | p.2 ∈ retainedCell lambda q p.1} := by
  have hr : MeasurableSet {p : Path × (ℝ × ℝ) | Representative (driftedReflectionPath lambda p.1) q} :=
    (measurableSet_representative q).preimage ((measurable_driftedReflectionPath lambda).comp measurable_fst)
  have hl : Measurable (fun p : Path × (ℝ × ℝ) ↦ leftEndpoint (q : ℝ) (driftedReflectionPath lambda p.1)) :=
    (measurable_leftEndpoint (q : ℝ)).comp ((measurable_driftedReflectionPath lambda).comp measurable_fst)
  have hu : Measurable (fun p : Path × (ℝ × ℝ) ↦ rightEndpoint (q : ℝ) (driftedReflectionPath lambda p.1)) :=
    (measurable_rightEndpoint (q : ℝ)).comp ((measurable_driftedReflectionPath lambda).comp measurable_fst)
  convert hr.inter ((measurableSet_lt hl measurable_snd.fst).inter
    (measurableSet_lt measurable_snd.fst hu)) using 1
  ext p
  exact mem_retainedCell_iff lambda q p.1 p.2

/-- The full spatial cell has exactly the genuine full excursion-area rate. -/
theorem intensity_retainedCell (lambda : ℝ) (q : ℚ) (f : Path) :
    intensity lambda f (retainedCell lambda q f) = (retainedArea q lambda f : ℝ≥0∞) := by
  let a := leftTime (q : ℝ) lambda f
  let b := rightTime (q : ℝ) lambda f
  have he : retainedCell lambda q f ∩ fullRegion lambda f =
      retainedCell lambda q f ∩ BrownianUnderGraphIntensity.region lambda a b f := by
    ext z
    constructor
    · rintro ⟨hz,hr⟩
      exact ⟨hz,retainedTimes_subset_Icc lambda q f hz.1,hr.2⟩
    · rintro ⟨hz,hr⟩
      exact ⟨hz,(a : ℝ≥0).coe_nonneg.trans hr.1.1,hr.2⟩
  rw [intensity,Measure.restrict_apply (measurableSet_retainedCell lambda q f),he,
    retainedCell,BrownianClippedExcursionSpatialCells.volume_time_strip_inter_region lambda a b f _
      (measurableSet_retainedTimes lambda q f) (retainedTimes_subset_Icc lambda q f)]
  by_cases hq : Representative (driftedReflectionPath lambda f) q
  · simp only [retainedTimes,retainedArea,if_pos hq]
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    change (∫ s in Ioo (leftEndpoint (q : ℝ) (driftedReflectionPath lambda f))
      (rightEndpoint (q : ℝ) (driftedReflectionPath lambda f)), BrownianReflectedAreaCounts.surface lambda f s) =
      ∫ s in Icc (leftTime (q : ℝ) lambda f : ℝ) (rightTime (q : ℝ) lambda f : ℝ),
        BrownianReflectedAreaCounts.surface lambda f s
    rw [coe_leftTime,coe_rightTime]
    exact (integral_Icc_eq_integral_Ioc.trans integral_Ioc_eq_integral_Ioo).symm
  · simp [retainedTimes,retainedArea,hq]

end PerronWright.BrownianFullExcursionSpatialCells
