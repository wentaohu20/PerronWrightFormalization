import PerronWright.Probability.BrownianPositiveBridgeWeakClusterSupport
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! # Actual small-endpoint bridge laws have a common weak compact closure

This is the genuine Prokhorov consequence of the proved dyadic compact
good-set bounds. No compactness of a path-law family is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeWeakCompactness

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianPositiveBridgeWeakClusterSupport
open BrownianPositiveBridgePathTightness

def smallProbabilityFamily (T : ℝ≥0) (δ : ℝ) : Set (ProbabilityMeasure Path) :=
  {μ | (μ : Measure Path) ∈ smallEndpointFamily T δ}

theorem exists_compact_closure_smallProbabilityFamily (T : ℝ≥0) (hT : 0 < T) :
    ∃ δ : ℝ, 0 < δ ∧ IsCompact (closure (smallProbabilityFamily T δ)) := by
  obtain ⟨δ,hδ,htight⟩ := exists_small_endpoint_tightFamily T hT
  refine ⟨δ,hδ,isCompact_closure_of_isTightMeasureSet ?_⟩
  apply htight.subset
  rintro μ ⟨ν,hν,rfl⟩
  exact hν

theorem eventually_mem_compact_closure (T : ℝ≥0) (hT : 0 < T)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, bridgeProbability T hT a ∈ closure (smallProbabilityFamily T δ) := by
  have hlt : ∀ᶠ a : ℝ in 𝓝[>] 0, a < δ :=
    (tendsto_id.mono_right nhdsWithin_le_nhds).eventually_lt_const hδ
  filter_upwards [self_mem_nhdsWithin,hlt] with a ha haδ
  apply subset_closure
  exact ⟨a,ha,haδ,bridgeProbability_toMeasure T hT a ha⟩

theorem exists_common_weak_compact_set (T : ℝ≥0) (hT : 0 < T) :
    ∃ K : Set (ProbabilityMeasure Path), IsCompact K ∧
      ∀ᶠ a : ℝ in 𝓝[>] 0, bridgeProbability T hT a ∈ K := by
  obtain ⟨δ,hδ,hK⟩ := exists_compact_closure_smallProbabilityFamily T hT
  exact ⟨closure (smallProbabilityFamily T δ),hK,eventually_mem_compact_closure T hT δ hδ⟩

end PerronWright.BrownianPositiveBridgeWeakCompactness
