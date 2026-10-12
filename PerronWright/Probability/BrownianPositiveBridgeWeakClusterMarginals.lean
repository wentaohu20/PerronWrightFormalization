import PerronWright.Probability.BrownianPositiveBridgeWeakClusterSupport
import PerronWright.Probability.BrownianEntranceContinuousRealization

/-! # Genuine entrance marginals of every actual path weak cluster

Fixed padded finite evaluations are continuous maps on the path space.
Their actual bounded-test limits identify every weak cluster marginal.
The already proved zero stopped support then removes the padding.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeWeakClusterMarginals

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianPositiveBridgeWeakClusterSupport
open BrownianEntranceCountableLaw BrownianEntranceDyadicSamples

theorem continuous_sampleEval (T : ℝ≥0) (σ : ℕ → ℝ≥0) (J : Finset ℕ) :
    Continuous (sampleEval T σ J) := by
  apply continuous_pi
  intro j
  by_cases h : 0 < σ j.val ∧ σ j.val < T
  · simp only [sampleEval,if_pos h]
    exact continuous_eval _
  · simp only [sampleEval,if_neg h]
    exact continuous_const

def sampleProbability (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) (J : Finset ℕ) :
    ProbabilityMeasure (J → ℝ) :=
  ⟨sampleLaw T σ J,sampleLaw_isProbability T hT σ J⟩

theorem actual_sampleProbability_tendsto (T : ℝ≥0) (hT : 0 < T)
    (σ : ℕ → ℝ≥0) (J : Finset ℕ) :
    Tendsto (fun a : ℝ ↦ (bridgeProbability T hT a).map
      (continuous_sampleEval T σ J).measurable.aemeasurable)
      (𝓝[>] 0) (𝓝 (sampleProbability T hT σ J)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mpr
  intro g
  have hg : Measurable (fun v ↦ (g v : ℝ≥0∞)) :=
    ENNReal.continuous_coe.measurable.comp g.continuous.measurable
  have hb (v : J → ℝ) : (g v : ℝ≥0∞) ≤ ENNReal.ofReal (nndist g 0 : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact ENNReal.coe_le_coe.mpr (BoundedContinuousFunction.NNReal.upper_bound g v)
  have he := actual_sample_bounded_test_tendsto T hT σ J (nndist g 0 : ℝ)
    (fun v ↦ (g v : ℝ≥0∞)) hg hb
  change Tendsto _ _ (𝓝 (∫⁻ v, (g v : ℝ≥0∞) ∂sampleLaw T σ J))
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  change 0 < a at ha
  symm
  change (∫⁻ v, (g v : ℝ≥0∞) ∂(bridgeProbability T hT a : Measure Path).map
    (sampleEval T σ J)) = _
  rw [lintegral_map hg (continuous_sampleEval T σ J).measurable,
    bridgeProbability_toMeasure T hT a ha]

theorem weak_cluster_padded_marginal {ι : Type*} {L : Filter ι} [L.NeBot]
    (T : ℝ≥0) (hT : 0 < T) (a : ι → ℝ)
    (ha : Tendsto a L (𝓝[>] 0)) (μ : ProbabilityMeasure Path)
    (hμ : Tendsto (fun i ↦ bridgeProbability T hT (a i)) L (𝓝 μ))
    (σ : ℕ → ℝ≥0) (J : Finset ℕ) :
    (μ : Measure Path).map (sampleEval T σ J) = sampleLaw T σ J := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun i ↦ bridgeProbability T hT (a i)) μ hμ (continuous_sampleEval T σ J)
  have he := tendsto_nhds_unique hmap ((actual_sampleProbability_tendsto T hT σ J).comp ha)
  exact congrArg ProbabilityMeasure.toMeasure he

theorem weak_cluster_unpadded_marginal {ι : Type*} {L : Filter ι} [L.NeBot]
    (T : ℝ≥0) (hT : 0 < T) (a : ι → ℝ)
    (ha : Tendsto a L (𝓝[>] 0)) (μ : ProbabilityMeasure Path)
    (hμ : Tendsto (fun i ↦ bridgeProbability T hT (a i)) L (𝓝 μ))
    (σ : ℕ → ℝ≥0) (J : Finset ℕ) :
    (μ : Measure Path).map (fun f (j : J) ↦ f (σ j.val)) = sampleLaw T σ J := by
  have he : (fun f (j : J) ↦ f (σ j.val))
      =ᵐ[(μ : Measure Path)] sampleEval T σ J := by
    filter_upwards [ae_weak_cluster_stopped_zero T hT a ha μ hμ,
      ae_weak_cluster_endpoint_zero T hT a ha μ hμ 0 (Or.inl rfl)] with f hs hz
    funext j
    by_cases hi : 0 < σ j.val ∧ σ j.val < T
    · simp only [sampleEval,if_pos hi]
    · have hf : f (σ j.val) = 0 := by
        rcases eq_or_lt_of_le (show 0 ≤ σ j.val from zero_le) with heq | hpos
        · rw [← heq,hz]
        · have ht : T ≤ σ j.val := le_of_not_gt (fun hlt ↦ hi ⟨hpos,hlt⟩)
          exact hs _ ht
      simp only [sampleEval,if_neg hi,hf]
  rw [Measure.map_congr he]
  exact weak_cluster_padded_marginal T hT a ha μ hμ σ J

theorem weak_cluster_sampling_finite {ι : Type*} {L : Filter ι} [L.NeBot]
    (T : ℝ≥0) (hT : 0 < T) (a : ι → ℝ)
    (ha : Tendsto a L (𝓝[>] 0)) (μ : ProbabilityMeasure Path)
    (hμ : Tendsto (fun i ↦ bridgeProbability T hT (a i)) L (𝓝 μ)) (J : Finset ℕ) :
    (μ : Measure Path).map (fun f ↦ J.restrict
      (BrownianEntranceContinuousRealization.pathSampling T f)) =
      sampleLaw T (samplingTimes T) J :=
  weak_cluster_unpadded_marginal T hT a ha μ hμ (samplingTimes T) J

theorem weak_cluster_sampling_eq_source {ι : Type*} {L : Filter ι} [L.NeBot]
    (T : ℝ≥0) (hT : 0 < T) (a : ι → ℝ)
    (ha : Tendsto a L (𝓝[>] 0)) (μ : ProbabilityMeasure Path)
    (hμ : Tendsto (fun i ↦ bridgeProbability T hT (a i)) L (𝓝 μ)) :
    (μ : Measure Path).map (BrownianEntranceContinuousRealization.pathSampling T) =
      BrownianEntranceDyadicSamples.law T hT := by
  apply BrownianEntranceCountableLaw.law_unique T hT (samplingTimes T)
  intro J
  rw [Measure.map_map (Finset.measurable_restrict J)
    (BrownianEntranceContinuousRealization.measurable_pathSampling T)]
  exact weak_cluster_sampling_finite T hT a ha μ hμ J

end PerronWright.BrownianPositiveBridgeWeakClusterMarginals
