import PerronWright.Probability.CountableTVWindowProfile

/-! # The actual TV-marked window-law bad-mark probability

The weak-Borel bad-point event is pulled back to its literal component
event under the actual graph source. Its probability is consequently
bounded by the actual sum of variation distances divided by the radius.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section

namespace PerronWright.CountableKernel

open CountableVariationMarks CountableTVWindowProfile CountableComponentWindowLaw
open FinitePointMeasureCompact

theorem empiricalMarkedWindowLaw_badProbability_eq
    (M : CountableKernel) (level : ℕ → ℕ) (lambda a b : ℝ) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (n : ℕ) (p : VariationMark) (δ : ℝ) :
    (M.empiricalMarkedWindowLaw level lambda a b R hlower hlo n :
      Measure (PointMeasure (MarkedWindow a b R))).real
        {η | 0 < count η (badMarkCell a b R p δ)} =
    (M.empiricalNormalizedGraphLaw level lambda hlower hlo n).real
      (badTVEvent (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) a b R p δ) := by
  rw [measureReal_def, measureReal_def]
  change ((M.empiricalNormalizedGraphLaw level lambda hlower hlo n).map
    (fun G ↦ markedWindowPointMeasure
      (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) G a b R)
      {η | 0 < count η (badMarkCell a b R p δ)}).toReal = _
  rw [Measure.map_apply (measurable_markedWindowPointMeasure _ a b R)
    (measurableSet_badPointEvent a b R p δ)]
  have he : (fun G ↦ markedWindowPointMeasure
      (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) G a b R) ⁻¹'
      {η | 0 < count η (badMarkCell a b R p δ)} =
      badTVEvent (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) a b R p δ := by
    ext G
    exact (badTVEvent_iff_badPointCount _ G a b R p δ).symm
  rw [he]

theorem empiricalMarkedWindowLaw_badProbability_le
    (M : CountableKernel) (level : ℕ → ℕ) (lambda a b : ℝ) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (n : ℕ) (p : VariationMark) (δ : ℝ) (hδ : 0 < δ) :
    (M.empiricalMarkedWindowLaw level lambda a b R hlower hlo n :
      Measure (PointMeasure (MarkedWindow a b R))).real
        {η | 0 < count η (badMarkCell a b R p δ)} ≤
      (∫ G, windowDistance
        (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) G a b R p
        ∂M.empiricalNormalizedGraphLaw level lambda hlower hlo n) / δ := by
  rw [M.empiricalMarkedWindowLaw_badProbability_eq level lambda a b R hlower hlo n p δ]
  exact badTVEvent_probability_le _ a b R p δ hδ _

end PerronWright.CountableKernel
