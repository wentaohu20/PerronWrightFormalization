import PerronWright.Probability.BrownianPositiveBridgeWeakClusterMarginals
import PerronWright.Probability.BrownianPositiveBridgeWeakCompactness
import PerronWright.Probability.BrownianEntranceSamplingUniqueness
import Mathlib.Topology.Ultrafilter

/-! # Directed path weak convergence of actual positive pinned bridges

The true small-endpoint conditioned bridge family is tight. Every path
weak cluster has the constructed entrance law's dense finite marginals
and its zero stopped support. The proved measurable sampling embedding
therefore identifies every cluster, and compactness gives full directed
weak convergence as the positive endpoint decreases to zero.

No Vervaat, standard-excursion, Palm, or Wright identity is asserted here.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgePathConvergence

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianPositiveBridgeWeakClusterSupport
open BrownianPositiveBridgeWeakClusterMarginals BrownianPositiveBridgeWeakCompactness

def entranceProbability (T : ℝ≥0) (hT : 0 < T) : ProbabilityMeasure Path :=
  ⟨BrownianEntranceContinuousRealization.pathLaw T hT,
    BrownianEntranceContinuousRealization.pathLaw_isProbability T hT⟩

theorem weak_cluster_eq_entrance {ι : Type*} {L : Filter ι} [L.NeBot]
    (T : ℝ≥0) (hT : 0 < T) (a : ι → ℝ)
    (ha : Tendsto a L (𝓝[>] 0)) (μ : ProbabilityMeasure Path)
    (hμ : Tendsto (fun i ↦ bridgeProbability T hT (a i)) L (𝓝 μ)) :
    μ = entranceProbability T hT := by
  apply Subtype.ext
  exact BrownianEntranceSamplingUniqueness.stopped_zero_law_eq_entrance_of_sampling T hT
    (μ : Measure Path) (ae_weak_cluster_stopped_zero T hT a ha μ hμ)
    (weak_cluster_sampling_eq_source T hT a ha μ hμ)

theorem tendsto_positiveBridgeProbability (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (bridgeProbability T hT) (𝓝[>] 0) (𝓝 (entranceProbability T hT)) := by
  obtain ⟨K,hK,hmem⟩ := exists_common_weak_compact_set T hT
  apply hK.tendsto_nhds_of_unique_mapClusterPt hmem
  intro μ _hμK hcluster
  obtain ⟨U,hU,hlim⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  exact weak_cluster_eq_entrance T hT id (tendsto_id.mono_left hU) μ hlim

theorem tendsto_actual_positiveBridge_bounded_lintegral (T : ℝ≥0) (hT : 0 < T)
    (Ψ : Path →ᵇ ℝ≥0) :
    Tendsto (fun a : ℝ ↦ ∫⁻ f, (Ψ f : ℝ≥0∞) ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (∫⁻ f, (Ψ f : ℝ≥0∞) ∂BrownianEntranceContinuousRealization.pathLaw T hT)) := by
  have he := ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp
    (tendsto_positiveBridgeProbability T hT) Ψ
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [bridgeProbability_toMeasure T hT a ha]

theorem tendsto_actual_positiveBridge_bounded_integral (T : ℝ≥0) (hT : 0 < T)
    (Ψ : Path →ᵇ ℝ) :
    Tendsto (fun a : ℝ ↦ ∫ f, Ψ f ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (∫ f, Ψ f ∂BrownianEntranceContinuousRealization.pathLaw T hT)) := by
  have he := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_positiveBridgeProbability T hT) Ψ
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [bridgeProbability_toMeasure T hT a ha]

theorem tendsto_positiveBridgeProbability_of_tendsto {ι : Type*} {L : Filter ι}
    (T : ℝ≥0) (hT : 0 < T) (a : ι → ℝ) (ha : Tendsto a L (𝓝[>] 0)) :
    Tendsto (fun i ↦ bridgeProbability T hT (a i)) L (𝓝 (entranceProbability T hT)) :=
  (tendsto_positiveBridgeProbability T hT).comp ha

end PerronWright.BrownianPositiveBridgePathConvergence
