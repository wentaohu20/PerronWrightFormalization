import PerronWright.Probability.BrownianUnderGraphPoissonLaw
import PerronWright.Probability.FinitePoissonDisjointCellCounts

/-!
# Actual disjoint-cell Poisson counts under bounded reflected paths

The rates below are literal planar Lebesgue intensities. Independence
and exact joint probabilities follow from the proved iid-atom spatial
construction, not from a postulated spatial Poisson process.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

noncomputable section

namespace PerronWright.BrownianUnderGraphDisjointCounts

open BrownianPathLaw BrownianUnderGraphIntensity BrownianUnderGraphPoissonLaw
  FinitePointMeasureCompact

theorem intensity_apply (lambda : ℝ) (a b : ℝ≥0) (f : Path)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    intensity lambda a b f A = (volume (A ∩ region lambda a b f)).toNNReal := by
  change (volume.restrict (region lambda a b f) A).toNNReal = _
  rw [Measure.restrict_apply hA]

variable {D : Type*} [Fintype D]

/-- Literal Borel-cell counts have the exact independent planar-intensity law. -/
theorem law_count_vector (lambda : ℝ) (a b : ℝ≥0) (f : Path)
    (A : D → Set (ℝ × ℝ))
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) :
    (law lambda a b f).map (fun η i ↦ count η (A i)) =
      PoissonCountKernel.finiteCountLaw
        (fun i ↦ (volume (A i ∩ region lambda a b f)).toNNReal) := by
  have he := FinitePoissonDisjointCellCounts.countLaw_eq_finitePoisson
    (intensity lambda a b f) A hAd hA
  simpa only [FinitePoissonDisjointCellCounts.countLaw, law, intensity_apply _ _ _ _ (hA _)]
    using he

theorem law_count_hasLaw (lambda : ℝ) (a b : ℝ≥0) (f : Path)
    (A : D → Set (ℝ × ℝ))
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) (i : D) :
    HasLaw (fun η : PointMeasure (ℝ × ℝ) ↦ count η (A i))
      (poissonMeasure ((volume (A i ∩ region lambda a b f)).toNNReal))
      (law lambda a b f) := by
  simpa only [law, intensity_apply _ _ _ _ (hA i)] using
    FinitePoissonDisjointCellCounts.intensityLaw_count_hasLaw
      (intensity lambda a b f) A hAd hA i

theorem law_counts_independent (lambda : ℝ) (a b : ℝ≥0) (f : Path)
    (A : D → Set (ℝ × ℝ))
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) :
    iIndepFun (fun i (η : PointMeasure (ℝ × ℝ)) ↦ count η (A i))
      (law lambda a b f) :=
  FinitePoissonDisjointCellCounts.intensityLaw_counts_independent
    (intensity lambda a b f) A hAd hA

/-- Exact actual finite cell-event probabilities, at genuine unit planar rates. -/
theorem law_count_event (lambda : ℝ) (a b : ℝ≥0) (f : Path)
    (A : D → Set (ℝ × ℝ))
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) (m : D → ℕ) :
    law lambda a b f {η | ∀ i, count η (A i) = m i} =
      ∏ i, ENNReal.ofReal (Real.exp
        (-((volume (A i ∩ region lambda a b f)).toNNReal : ℝ)) *
        ((volume (A i ∩ region lambda a b f)).toNNReal : ℝ) ^ m i /
          ((m i).factorial : ℝ)) := by
  have hm := Measure.map_apply
    (FinitePointMeasureMeasurable.measurable_count_vector A hA)
    (measurableSet_singleton m) (μ := law lambda a b f)
  rw [law_count_vector lambda a b f A hAd hA,
    PoissonCountKernel.finiteCountLaw_singleton] at hm
  rw [hm]
  congr 1
  ext η
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff]

end PerronWright.BrownianUnderGraphDisjointCounts
