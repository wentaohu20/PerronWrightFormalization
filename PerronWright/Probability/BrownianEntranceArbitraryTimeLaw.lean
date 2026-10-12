import PerronWright.Probability.BrownianPositiveBridgePathConvergence

/-! # Arbitrary-real-time marginals of the constructed continuous entrance law

The genuine path weak limit and the proved actual positive-bridge finite
test limits identify the literal path-law marginals, by finite Borel
measure uniqueness. Endpoints and the stopped part are treated through
their actual almost-sure zero values, not a false endpoint setwise limit.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceArbitraryTimeLaw

open BrownianPathLaw BrownianPositiveBridgeConditioning
open BrownianEntranceContinuousRealization BrownianPositiveBridgePathConvergence

/-- Composition with the proved actual path limit, followed by finite
Borel measure uniqueness. Its finite-law premises are discharged below. -/
theorem map_eq_of_actual_bounded_test_limit {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [HasOuterApproxClosed X]
    (T : ℝ≥0) (hT : 0 < T) (F : Path → X) (hF : Continuous F) (ν : Measure X)
    (hlim : ∀ Ψ : X →ᵇ ℝ≥0, Tendsto
      (fun a : ℝ ↦ ∫⁻ f, (Ψ (F f) : ℝ≥0∞) ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (∫⁻ v, (Ψ v : ℝ≥0∞) ∂ν))) :
    (pathLaw T hT).map F = ν := by
  let := pathLaw_isProbability T hT
  let : IsProbabilityMeasure ((pathLaw T hT).map F) :=
    Measure.isProbabilityMeasure_map hF.measurable.aemeasurable
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro Ψ
  have hΨ : Measurable (fun v ↦ (Ψ v : ℝ≥0∞)) :=
    ENNReal.continuous_coe.measurable.comp Ψ.continuous.measurable
  rw [lintegral_map hΨ hF.measurable]
  have hw := tendsto_actual_positiveBridge_bounded_lintegral T hT
    (Ψ.compContinuous ⟨F,hF⟩)
  exact tendsto_nhds_unique hw (hlim Ψ)

theorem continuous_paddedFiniteEval (T : ℝ≥0) (J : Finset ℝ≥0) :
    Continuous (BrownianEntranceEndpointFamily.paddedFiniteEval T J) := by
  apply continuous_pi
  intro j
  by_cases h : 0 < j.val ∧ j.val < T
  · simp only [BrownianEntranceEndpointFamily.paddedFiniteEval,if_pos h]
    exact continuous_eval _
  · simp only [BrownianEntranceEndpointFamily.paddedFiniteEval,if_neg h]
    exact continuous_const

theorem pathLaw_padded_finite_eq (T : ℝ≥0) (hT : 0 < T) (J : Finset ℝ≥0) :
    (pathLaw T hT).map (BrownianEntranceEndpointFamily.paddedFiniteEval T J) =
      BrownianEntranceEndpointFamily.finiteLaw T J := by
  apply map_eq_of_actual_bounded_test_limit T hT _ (continuous_paddedFiniteEval T J)
  intro Ψ
  exact BrownianEntranceEndpointFamily.actual_padded_bounded_test_tendsto T hT J
    (nndist Ψ 0 : ℝ) (fun v ↦ (Ψ v : ℝ≥0∞))
    (ENNReal.continuous_coe.measurable.comp Ψ.continuous.measurable)
    (fun v ↦ by
      rw [ENNReal.ofReal_coe_nnreal]
      exact ENNReal.coe_le_coe.mpr (BoundedContinuousFunction.NNReal.upper_bound Ψ v))

theorem ae_pathLaw_all_padded_eval_eq (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw T hT, ∀ t : ℝ≥0,
      f t = if 0 < t ∧ t < T then f t else 0 := by
  filter_upwards [ae_pathLaw_initial_zero T hT,ae_pathLaw_stopped_zero T hT] with f hz hs
  intro t
  by_cases hi : 0 < t ∧ t < T
  · simp only [if_pos hi]
  · simp only [if_neg hi]
    by_cases hp : 0 < t
    · exact hs t (le_of_not_gt (fun ht ↦ hi ⟨hp,ht⟩))
    · have ht : t = 0 := le_antisymm (le_of_not_gt hp) (zero_le : (0 : ℝ≥0) ≤ t)
      simpa only [ht] using hz

def finiteEval (J : Finset ℝ≥0) (f : Path) : J → ℝ := fun j ↦ f j.val

theorem continuous_finiteEval (J : Finset ℝ≥0) : Continuous (finiteEval J) :=
  continuous_pi (fun _ ↦ continuous_eval _)

theorem pathLaw_finite_eq (T : ℝ≥0) (hT : 0 < T) (J : Finset ℝ≥0) :
    (pathLaw T hT).map (finiteEval J) = BrownianEntranceEndpointFamily.finiteLaw T J := by
  have he : finiteEval J =ᵐ[pathLaw T hT] BrownianEntranceEndpointFamily.paddedFiniteEval T J := by
    filter_upwards [ae_pathLaw_all_padded_eval_eq T hT] with f hf
    exact funext (fun j ↦ hf j.val)
  rw [Measure.map_congr he]
  exact pathLaw_padded_finite_eq T hT J

theorem pathLaw_finite_lintegral (T : ℝ≥0) (hT : 0 < T) (J : Finset ℝ≥0)
    (Ψ : (J → ℝ) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (finiteEval J f) ∂pathLaw T hT) =
      ∫⁻ v, Ψ v ∂BrownianEntranceEndpointFamily.finiteLaw T J := by
  rw [← lintegral_map hΨ (continuous_finiteEval J).measurable,pathLaw_finite_eq T hT J]

theorem pathLaw_finite_probability (T : ℝ≥0) (hT : 0 < T) (J : Finset ℝ≥0)
    {B : Set (J → ℝ)} (hB : MeasurableSet B) :
    pathLaw T hT ((finiteEval J) ⁻¹' B) = BrownianEntranceEndpointFamily.finiteLaw T J B := by
  rw [← Measure.map_apply (continuous_finiteEval J).measurable hB,pathLaw_finite_eq T hT J]

theorem pathLaw_arbitrary_samples_finite_eq (T : ℝ≥0) (hT : 0 < T)
    (σ : ℕ → ℝ≥0) (J : Finset ℕ) :
    (pathLaw T hT).map (fun f (j : J) ↦ f (σ j.val)) =
      BrownianEntranceCountableLaw.sampleLaw T σ J := by
  have he : (fun f (j : J) ↦ f (σ j.val))
      =ᵐ[pathLaw T hT] BrownianEntranceCountableLaw.sampleEval T σ J := by
    filter_upwards [ae_pathLaw_all_padded_eval_eq T hT] with f hf
    exact funext (fun j ↦ hf (σ j.val))
  rw [Measure.map_congr he]
  apply map_eq_of_actual_bounded_test_limit T hT _
    (BrownianPositiveBridgeWeakClusterMarginals.continuous_sampleEval T σ J)
  intro Ψ
  exact BrownianEntranceCountableLaw.actual_sample_bounded_test_tendsto T hT σ J
    (nndist Ψ 0 : ℝ) (fun v ↦ (Ψ v : ℝ≥0∞))
    (ENNReal.continuous_coe.measurable.comp Ψ.continuous.measurable)
    (fun v ↦ by
      rw [ENNReal.ofReal_coe_nnreal]
      exact ENNReal.coe_le_coe.mpr (BoundedContinuousFunction.NNReal.upper_bound Ψ v))

def arbitrarySampling (σ : ℕ → ℝ≥0) (f : Path) : ℕ → ℝ := fun i ↦ f (σ i)

theorem continuous_arbitrarySampling (σ : ℕ → ℝ≥0) : Continuous (arbitrarySampling σ) :=
  continuous_pi (fun _ ↦ continuous_eval _)

theorem pathLaw_arbitrary_sampling_eq_countable (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) :
    (pathLaw T hT).map (arbitrarySampling σ) = BrownianEntranceCountableLaw.law T hT σ := by
  apply BrownianEntranceCountableLaw.law_unique T hT σ
  intro J
  rw [Measure.map_map (Finset.measurable_restrict J) (continuous_arbitrarySampling σ).measurable]
  exact pathLaw_arbitrary_samples_finite_eq T hT σ J

theorem pathLaw_arbitrary_sampling_lintegral (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0)
    (Ψ : (ℕ → ℝ) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (arbitrarySampling σ f) ∂pathLaw T hT) =
      ∫⁻ v, Ψ v ∂BrownianEntranceCountableLaw.law T hT σ := by
  rw [← lintegral_map hΨ (continuous_arbitrarySampling σ).measurable,
    pathLaw_arbitrary_sampling_eq_countable T hT σ]

def nonnegativePaths : Set Path := {f | ∀ t : ℝ≥0, 0 ≤ f t}

theorem isClosed_nonnegativePaths : IsClosed nonnegativePaths := by
  have hc (t : ℝ≥0) : IsClosed {f : Path | 0 ≤ f t} :=
    isClosed_le continuous_const (continuous_eval t)
  simpa only [nonnegativePaths,Set.ofPred_forall] using isClosed_iInter hc

theorem ae_positiveBridgeLaw_nonnegative (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ f ∂positiveBridgeLaw a T, f ∈ nonnegativePaths := by
  filter_upwards [ae_positiveBridgeLaw_strictly_positive a T,
    BrownianPositiveBridgeStoppedSupport.ae_positiveBridgeLaw_stopped a T] with f hp hs
  intro t
  rw [hs t]
  exact (hp (min t T) (min_le_right _ _)).le

theorem ae_pathLaw_nonnegative (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw T hT, ∀ t : ℝ≥0, 0 ≤ f t := by
  have hm : ∀ᶠ a : ℝ in 𝓝[>] 0,
      (BrownianPositiveBridgeWeakClusterSupport.bridgeProbability T hT a : Measure Path)
        nonnegativePaths = 1 := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [BrownianPositiveBridgeWeakClusterSupport.bridgeProbability_toMeasure T hT a ha]
    let := positiveBridgeLaw_isProbability a ha T hT
    exact (mem_ae_iff_prob_eq_one isClosed_nonnegativePaths.measurableSet).mp
      (ae_positiveBridgeLaw_nonnegative a T)
  have hl := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    (tendsto_positiveBridgeProbability T hT) isClosed_nonnegativePaths
  rw [Filter.limsup_congr hm,limsup_const] at hl
  let := pathLaw_isProbability T hT
  have hmass : pathLaw T hT nonnegativePaths = 1 := le_antisymm prob_le_one hl
  exact (mem_ae_iff_prob_eq_one isClosed_nonnegativePaths.measurableSet).mpr hmass

end PerronWright.BrownianEntranceArbitraryTimeLaw
