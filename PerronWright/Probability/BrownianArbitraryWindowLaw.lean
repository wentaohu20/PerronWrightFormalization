import PerronWright.Probability.BrownianExcursionPointProcessLaw
import PerronWright.Probability.BrownianExcursionCompactWindows
import PerronWright.Probability.FinitePointMeasureMarking
import PerronWright.Probability.WindowCountGenerators

/-!
# Actual Brownian laws in arbitrary closed size--surplus windows

The restriction of a canonical finite point chart is constructed by
filtering its actual integer atoms. Its weak-Borel measurability follows
from the proved measurable count encoding, not continuity of restriction.
The resulting Brownian law is exactly the closed-window restriction of
the actual full Brownian excursion process, including boundary atoms.
-/

open MeasureTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal CompactlySupported

noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianArbitraryWindowLaw

open BrownianPathLaw BrownianExcursionWindowPointMeasure
open ComponentGlobalPointProcess FinitePointMeasureCompact FinitePointMeasureFintype
open GlobalPointMeasureCharts GlobalPointChartSurjective PositiveSizeSurplusExhaustion
open FinitePointMeasureMeasurable FinitePointMeasureCountDeterminacy WindowCountGenerators
open FinitePointMeasureMarking

private theorem embedding_measurableEmbedding (a b : ℝ) (R : ℕ) (ha : 0 < a) :
    MeasurableEmbedding (positiveWindowEmbedding a b R ha) := by
  apply (measurable_positiveWindowEmbedding a b R ha).measurableEmbedding
  intro x y h
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun z : PositiveSizeSurplus ↦ z.1.val) h)
  · exact Fin.ext (congrArg (fun z : PositiveSizeSurplus ↦ z.2) h)

private theorem exists_chartRestriction (a b : ℝ) (R : ℕ) (ha : 0 < a)
    (m : ℕ) (η : Chart m) :
    ∃ ξ : PointMeasure (SurplusWindow a b R),
      (((ξ : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R)).map
        (positiveWindowEmbedding a b R ha)) =
        (embeddedMeasure m η).restrict (positiveWindowSet a b R) := by
  obtain ⟨n, x, hx⟩ := η.property
  let I := {i : Fin n // positiveWindowEmbedding (lower m) (upper m) m (lower_pos m)
    (x i) ∈ positiveWindowSet a b R}
  let y : I → SurplusWindow a b R := fun i ↦
    (⟨(x i.val).1.val, i.property.1⟩,
      ⟨(x i.val).2.val, Nat.lt_succ_iff.mpr i.property.2⟩)
  have hy (i : I) : positiveWindowEmbedding a b R ha (y i) =
      positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) (x i.val) := rfl
  refine ⟨ofFintype y, ?_⟩
  rw [ofFintype_toMeasure, Measure.map_finset_sum'
    (measurable_positiveWindowEmbedding a b R ha).aemeasurable]
  simp only [Measure.map_dirac' (measurable_positiveWindowEmbedding a b R ha), hy]
  rw [embeddedMeasure, hx, FiniteAtomicPointMeasure.ofAtoms_toMeasure,
    Measure.map_finset_sum'
      (measurable_positiveWindowEmbedding (lower m) (upper m) m (lower_pos m)).aemeasurable]
  simp only [Measure.map_dirac'
    (measurable_positiveWindowEmbedding (lower m) (upper m) m (lower_pos m))]
  change (∑ i : I, Measure.dirac
      (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) (x i.val))) =
    Measure.restrictₗ (positiveWindowSet a b R) (∑ i : Fin n, Measure.dirac
      (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) (x i)))
  rw [map_sum]
  change (∑ i : I, Measure.dirac
      (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) (x i.val))) =
    ∑ i : Fin n, (Measure.dirac
      (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) (x i))).restrict
        (positiveWindowSet a b R)
  simp only [restrict_dirac]
  exact (Finset.sum_congr_set
    {i : Fin n | positiveWindowEmbedding (lower m) (upper m) m (lower_pos m)
      (x i) ∈ positiveWindowSet a b R}
    (fun i ↦ if positiveWindowEmbedding (lower m) (upper m) m (lower_pos m)
      (x i) ∈ positiveWindowSet a b R then Measure.dirac
        (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) (x i)) else 0)
    (fun i : I ↦ Measure.dirac
      (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) (x i.val)))
    (fun _ hi ↦ if_pos hi) (fun _ hi ↦ if_neg hi)).symm

def chartRestriction (a b : ℝ) (R : ℕ) (ha : 0 < a) (m : ℕ)
    (η : Chart m) : PointMeasure (SurplusWindow a b R) :=
  (exists_chartRestriction a b R ha m η).choose

theorem chartRestriction_embedded (a b : ℝ) (R : ℕ) (ha : 0 < a)
    (m : ℕ) (η : Chart m) :
    (((chartRestriction a b R ha m η : FiniteMeasure (SurplusWindow a b R)) :
      Measure (SurplusWindow a b R)).map
      (positiveWindowEmbedding a b R ha)) =
        (embeddedMeasure m η).restrict (positiveWindowSet a b R) :=
  (exists_chartRestriction a b R ha m η).choose_spec

theorem chartRestriction_apply (a b : ℝ) (R : ℕ) (ha : 0 < a)
    (m : ℕ) (η : Chart m) {A : Set (SurplusWindow a b R)} (hA : MeasurableSet A) :
    ((chartRestriction a b R ha m η : FiniteMeasure (SurplusWindow a b R)) :
      Measure (SurplusWindow a b R)) A =
      ((η : FiniteMeasure (SurplusWindow (lower m) (upper m) m)) :
        Measure (SurplusWindow (lower m) (upper m) m))
        (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) ⁻¹'
          (positiveWindowEmbedding a b R ha '' A)) := by
  have he := embedding_measurableEmbedding a b R ha
  have himage : MeasurableSet (positiveWindowEmbedding a b R ha '' A) :=
    he.measurableSet_image.mpr hA
  have hsub : positiveWindowEmbedding a b R ha '' A ⊆ positiveWindowSet a b R := by
    rintro _ ⟨z, _, rfl⟩
    rw [← range_positiveWindowEmbedding a b R ha]
    exact mem_range_self z
  have hh := congrArg (fun μ : Measure PositiveSizeSurplus ↦
    μ (positiveWindowEmbedding a b R ha '' A)) (chartRestriction_embedded a b R ha m η)
  rw [Measure.map_apply he.measurable himage, he.injective.preimage_image,
    Measure.restrict_apply himage, inter_eq_left.mpr hsub,
    embeddedMeasure, Measure.map_apply
      (measurable_positiveWindowEmbedding (lower m) (upper m) m (lower_pos m)) himage] at hh
  exact hh

theorem measurable_chartRestriction (a b : ℝ) (R : ℕ) (ha : 0 < a)
    (hab : a ≤ b) (m : ℕ) : Measurable (chartRestriction a b R ha m) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  apply (measurableEmbedding_countEncoding (cell a b R)
    (measurable_eq_generateFrom_cell a b R) (isPiSystem_range_cell a b R)
    (univ_mem_range_cell a b R)).measurable_comp_iff.mp
  apply measurable_pi_lambda
  intro i
  have hi := measurableSet_cell a b R i
  have he := embedding_measurableEmbedding a b R ha
  have hpre : MeasurableSet
      (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) ⁻¹'
        (positiveWindowEmbedding a b R ha '' cell a b R i)) :=
    (measurable_positiveWindowEmbedding (lower m) (upper m) m (lower_pos m))
      (he.measurableSet_image.mpr hi)
  have hc (η : Chart m) : count (chartRestriction a b R ha m η) (cell a b R i) =
      count η (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) ⁻¹'
        (positiveWindowEmbedding a b R ha '' cell a b R i)) := by
    unfold count
    exact congrArg (fun x : ℝ≥0∞ ↦ ⌊x.toReal⌋₊)
      (chartRestriction_apply a b R ha m η hi)
  simpa only [Function.comp_def, countEncoding, hc] using measurable_count hpre

private def coverIndex (a b : ℝ) (R : ℕ) (ha : 0 < a) : ℕ :=
  (exists_compact_subset_window (isCompact_positiveWindowSet a b R ha)).choose

private theorem subset_coverIndex (a b : ℝ) (R : ℕ) (ha : 0 < a) :
    positiveWindowSet a b R ⊆ window (coverIndex a b R ha) :=
  (exists_compact_subset_window (isCompact_positiveWindowSet a b R ha)).choose_spec

def pointMeasure (lambda a b : ℝ) (R : ℕ) (ha : 0 < a) (p : Input) :
    PointMeasure (SurplusWindow a b R) :=
  chartRestriction a b R ha (coverIndex a b R ha)
    (BrownianExcursionWindowPointMeasure.windowPointMeasure lambda (coverIndex a b R ha) p)

theorem measurable_pointMeasure (lambda a b : ℝ) (R : ℕ) (ha : 0 < a)
    (hab : a ≤ b) : Measurable (pointMeasure lambda a b R ha) :=
  (measurable_chartRestriction a b R ha hab _).comp
    (BrownianExcursionWindowPointMeasure.measurable_windowPointMeasure lambda _)

theorem pointMeasure_embedded (lambda a b : ℝ) (R : ℕ) (ha : 0 < a) (p : Input) :
    (((pointMeasure lambda a b R ha p : FiniteMeasure (SurplusWindow a b R)) :
      Measure (SurplusWindow a b R)).map
      (positiveWindowEmbedding a b R ha)) =
        (BrownianExcursionAtomicMeasure.process lambda p : Measure PositiveSizeSurplus).restrict
          (positiveWindowSet a b R) := by
  rw [pointMeasure, chartRestriction_embedded]
  rw [embeddedMeasure, ← BrownianExcursionAtomicMeasure.measure_restrict_window]
  exact Measure.restrict_restrict_of_subset (subset_coverIndex a b R ha)

theorem actualmeasure_integral_eq_window (lambda a b : ℝ) (R : ℕ)
    (ha : 0 < a) (p : Input) (f : C_c(PositiveSizeSurplus, ℝ))
    (hf : tsupport f ⊆ positiveWindowSet a b R) :
    (∫ z, f z ∂(BrownianExcursionAtomicMeasure.process lambda p :
      Measure PositiveSizeSurplus)) =
      ∫ z, f (positiveWindowEmbedding a b R ha z)
        ∂((pointMeasure lambda a b R ha p : FiniteMeasure (SurplusWindow a b R)) :
          Measure (SurplusWindow a b R)) := by
  rw [← integral_restrict_test_eq _ (measurableSet_positiveWindowSet a b R) f hf,
    ← pointMeasure_embedded]
  exact integral_map (measurable_positiveWindowEmbedding a b R ha).aemeasurable
    f.continuous.measurable.aestronglyMeasurable

def law (lambda a b : ℝ) (R : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    ProbabilityMeasure (PointMeasure (SurplusWindow a b R)) :=
  (BrownianExcursionPointProcessLaw.windowLaw lambda (coverIndex a b R ha)).map
    (measurable_chartRestriction a b R ha hab _).aemeasurable

theorem law_eq_actual_map (lambda a b : ℝ) (R : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    (law lambda a b R ha hab : Measure (PointMeasure (SurplusWindow a b R))) =
      (BrownianFullHorizonPoissonMarks.pathJointLaw lambda).map
        (pointMeasure lambda a b R ha ∘ BrownianExcursionPointProcessLaw.pathInput) := by
  rw [law, ProbabilityMeasure.toMeasure_map]
  change ((BrownianFullHorizonPoissonMarks.pathJointLaw lambda).map
    (BrownianExcursionWindowPointMeasure.windowPointMeasure lambda (coverIndex a b R ha) ∘
      BrownianExcursionPointProcessLaw.pathInput)).map _ = _
  rw [Measure.map_map (measurable_chartRestriction a b R ha hab _)
    ((BrownianExcursionWindowPointMeasure.measurable_windowPointMeasure lambda _).comp
      BrownianExcursionPointProcessLaw.measurable_pathInput)]
  rfl

theorem law_eq_chart_map (lambda a b : ℝ) (R : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (m : ℕ) (hsub : positiveWindowSet a b R ⊆ window m) :
    law lambda a b R ha hab =
      (BrownianExcursionPointProcessLaw.windowLaw lambda m).map
        (measurable_chartRestriction a b R ha hab m).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [law_eq_actual_map, ProbabilityMeasure.toMeasure_map]
  change _ = ((BrownianFullHorizonPoissonMarks.pathJointLaw lambda).map
    (BrownianExcursionWindowPointMeasure.windowPointMeasure lambda m ∘
      BrownianExcursionPointProcessLaw.pathInput)).map _
  rw [Measure.map_map (measurable_chartRestriction a b R ha hab m)
    ((BrownianExcursionWindowPointMeasure.measurable_windowPointMeasure lambda m).comp
      BrownianExcursionPointProcessLaw.measurable_pathInput)]
  congr 1
  funext p
  apply Subtype.ext
  apply FiniteMeasure.toMeasure_injective
  apply (embedding_measurableEmbedding a b R ha).map_injective
  simp only [Function.comp_apply]
  rw [pointMeasure_embedded, chartRestriction_embedded, embeddedMeasure,
    ← BrownianExcursionAtomicMeasure.measure_restrict_window,
    Measure.restrict_restrict_of_subset hsub]
  rfl

theorem law_map_embedding_eq_compactLaw (lambda a b : ℝ) (R : ℕ)
    (ha : 0 < a) (hab : a ≤ b) :
    (law lambda a b R ha hab).map
      (continuous_mapPoint (positiveWindowEmbedding a b R ha)
        (continuous_positiveWindowEmbedding a b R ha)).measurable.aemeasurable =
      BrownianExcursionCompactWindows.law lambda (positiveWindowSet a b R)
        (isCompact_positiveWindowSet a b R ha) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, law_eq_actual_map]
  rw [Measure.map_map
    (continuous_mapPoint _ (continuous_positiveWindowEmbedding a b R ha)).measurable
    ((measurable_pointMeasure lambda a b R ha hab).comp
      BrownianExcursionPointProcessLaw.measurable_pathInput)]
  change _ = (BrownianFullHorizonPoissonMarks.pathJointLaw lambda).map
    (BrownianExcursionCompactWindows.window lambda (positiveWindowSet a b R) ∘
      BrownianExcursionPointProcessLaw.pathInput)
  congr 1
  funext p
  apply Subtype.ext
  apply FiniteMeasure.toMeasure_injective
  simp only [Function.comp_apply, mapPoint_val, FiniteMeasure.toMeasure_map]
  rw [pointMeasure_embedded,
    BrownianExcursionCompactWindows.window_eq_restrict_process lambda _
      (isCompact_positiveWindowSet a b R ha)]

theorem law_canonical (lambda : ℝ) (m : ℕ) :
    law lambda (lower m) (upper m) m (lower_pos m) (lower_le_upper m) =
      BrownianExcursionPointProcessLaw.windowLaw lambda m := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [law_eq_actual_map]
  change _ = (BrownianFullHorizonPoissonMarks.pathJointLaw lambda).map
    (BrownianExcursionWindowPointMeasure.windowPointMeasure lambda m ∘
      BrownianExcursionPointProcessLaw.pathInput)
  congr 1
  funext p
  apply Subtype.ext
  apply FiniteMeasure.toMeasure_injective
  apply (embedding_measurableEmbedding (lower m) (upper m) m (lower_pos m)).map_injective
  simp only [Function.comp_apply]
  rw [pointMeasure_embedded, ← BrownianExcursionAtomicMeasure.measure_restrict_window]
  rfl

theorem law_lintegral (lambda a b : ℝ) (R : ℕ) (ha : 0 < a) (hab : a ≤ b)
    (F : PointMeasure (SurplusWindow a b R) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ η, F η ∂(law lambda a b R ha hab : Measure (PointMeasure (SurplusWindow a b R))) =
      ∫⁻ p, F (pointMeasure lambda a b R ha
        (BrownianExcursionPointProcessLaw.pathInput p))
        ∂BrownianFullHorizonPoissonMarks.pathJointLaw lambda := by
  rw [law_eq_actual_map]
  exact lintegral_map hF
    ((measurable_pointMeasure lambda a b R ha hab).comp
      BrownianExcursionPointProcessLaw.measurable_pathInput)

end PerronWright.BrownianArbitraryWindowLaw
