import PerronWright.Probability.BrownianEntranceStoppedSampling

/-! # The countable sampling law uniquely determines a stopped path law

This is equality of the literal compact-open Borel measures on continuous
paths, not merely uniqueness of finite-dimensional distributions as a
definition. The closed stopped-path set is used to pull back each measure
to its subtype, on which sampling is a proved measurable embedding.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceSamplingUniqueness

open BrownianPathLaw BrownianEntranceContinuousRealization BrownianEntranceStoppedSampling

theorem sampling_map_injective_of_stopped (T : ℝ≥0) {μ ν : Measure Path}
    (hμ : ∀ᵐ f ∂μ, f ∈ stoppedPaths T) (hν : ∀ᵐ f ∂ν, f ∈ stoppedPaths T)
    (h : μ.map (pathSampling T) = ν.map (pathSampling T)) : μ = ν := by
  let ι : stoppedPaths T → Path := Subtype.val
  have hι : MeasurableEmbedding ι :=
    MeasurableEmbedding.subtype_coe (measurableSet_stoppedPaths T)
  have hμ' : (μ.comap ι).map ι = μ := by
    rw [hι.map_comap]
    simpa only [ι,Subtype.range_coe] using Measure.restrict_eq_self_of_ae_mem hμ
  have hν' : (ν.comap ι).map ι = ν := by
    rw [hι.map_comap]
    simpa only [ι,Subtype.range_coe] using Measure.restrict_eq_self_of_ae_mem hν
  have hsub : μ.comap ι = ν.comap ι := by
    apply (stoppedSampling_measurableEmbedding T).map_injective
    change (μ.comap ι).map (pathSampling T ∘ ι) = (ν.comap ι).map (pathSampling T ∘ ι)
    rw [← Measure.map_map (measurable_pathSampling T) hι.measurable,
      ← Measure.map_map (measurable_pathSampling T) hι.measurable,hμ',hν']
    exact h
  rw [← hμ',← hν',hsub]

theorem sampling_map_injective_of_stopped_zero (T : ℝ≥0) {μ ν : Measure Path}
    (hμ : ∀ᵐ f ∂μ, ∀ t, T ≤ t → f t = 0)
    (hν : ∀ᵐ f ∂ν, ∀ t, T ≤ t → f t = 0)
    (h : μ.map (pathSampling T) = ν.map (pathSampling T)) : μ = ν := by
  apply sampling_map_injective_of_stopped T _ _ h
  · filter_upwards [hμ] with f hf
    intro t ht
    rw [hf t ht,hf T le_rfl]
  · filter_upwards [hν] with f hf
    intro t ht
    rw [hf t ht,hf T le_rfl]

theorem stopped_law_eq_entrance_of_sampling (T : ℝ≥0) (hT : 0 < T) (μ : Measure Path)
    (hμ : ∀ᵐ f ∂μ, f ∈ stoppedPaths T)
    (hs : μ.map (pathSampling T) = BrownianEntranceDyadicSamples.law T hT) :
    μ = pathLaw T hT :=
  sampling_map_injective_of_stopped T hμ (ae_pathLaw_stopped T hT)
    (hs.trans (pathLaw_sampling_eq_source T hT).symm)

theorem stopped_zero_law_eq_entrance_of_sampling (T : ℝ≥0) (hT : 0 < T) (μ : Measure Path)
    (hμ : ∀ᵐ f ∂μ, ∀ t, T ≤ t → f t = 0)
    (hs : μ.map (pathSampling T) = BrownianEntranceDyadicSamples.law T hT) :
    μ = pathLaw T hT :=
  sampling_map_injective_of_stopped_zero T hμ (ae_pathLaw_stopped_zero T hT)
    (hs.trans (pathLaw_sampling_eq_source T hT).symm)

theorem exists_unique_stopped_law_with_sampling (T : ℝ≥0) (hT : 0 < T) :
    ∃! μ : Measure Path, IsProbabilityMeasure μ ∧
      (∀ᵐ f ∂μ, f ∈ stoppedPaths T) ∧
      μ.map (pathSampling T) = BrownianEntranceDyadicSamples.law T hT := by
  refine ⟨pathLaw T hT,⟨pathLaw_isProbability T hT,ae_pathLaw_stopped T hT,
    pathLaw_sampling_eq_source T hT⟩,?_⟩
  intro μ hμ
  exact stopped_law_eq_entrance_of_sampling T hT μ hμ.2.1 hμ.2.2

end PerronWright.BrownianEntranceSamplingUniqueness
