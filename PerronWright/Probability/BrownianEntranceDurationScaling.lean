import PerronWright.Probability.BrownianPositiveBridgePathConvergence
import PerronWright.Probability.BrownianPositiveBridgeDilationLaw

/-! # Exact duration scaling of the genuine continuous entrance path law

The existing literal dilation is continuous for compact-open paths.
The exact actual positive-bridge scaling identity passes to the already
proved directed path weak limits, identifying the whole Borel measures.
No excursion, Vervaat, or moment identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceDurationScaling

open BrownianPathLaw BrownianPathDilationLaw BrownianPositiveBridgeConditioning
open BrownianEntranceContinuousRealization BrownianPositiveBridgePathConvergence
open BrownianPositiveBridgeWeakClusterSupport BrownianPositiveBridgeDilationLaw

theorem continuous_dilatePath (T : ℝ≥0) (c : ℝ) : Continuous (dilatePath T c) := by
  let θ : C(ℝ≥0,ℝ≥0) := ⟨fun t ↦ t/T,continuous_id.div_const T⟩
  change Continuous (fun f : C(ℝ≥0,ℝ) ↦ c • f.comp θ)
  exact (ContinuousMap.continuous_precomp θ).const_smul c

theorem continuous_brownianDilation (T : ℝ≥0) : Continuous (brownianDilation T) :=
  continuous_dilatePath T _

theorem positive_parameter_dilation_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun a : ℝ ↦ Real.sqrt (T : ℝ)*a) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hi : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [id_eq,mul_zero] using hi.const_mul (Real.sqrt (T : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact mul_pos (Real.sqrt_pos.mpr hT) (show 0 < a from ha)

theorem bridgeProbability_duration_scaling (T : ℝ≥0) (hT : 0 < T) (a : ℝ) (ha : 0 < a) :
    bridgeProbability T hT (Real.sqrt (T : ℝ)*a) =
      (bridgeProbability 1 zero_lt_one a).map (continuous_brownianDilation T).measurable.aemeasurable := by
  apply Subtype.ext
  change (bridgeProbability T hT (Real.sqrt (T : ℝ)*a) : Measure Path) =
    (bridgeProbability 1 zero_lt_one a : Measure Path).map (brownianDilation T)
  calc
    _ = positiveBridgeLaw (Real.sqrt (T : ℝ)*a) T :=
      bridgeProbability_toMeasure T hT (Real.sqrt (T : ℝ)*a)
        (mul_pos (Real.sqrt_pos.mpr hT) ha)
    _ = (positiveBridgeLaw a 1).map (brownianDilation T) :=
      positiveBridgeLaw_duration_scaling T hT a
    _ = _ := congrArg (Measure.map (brownianDilation T))
      (bridgeProbability_toMeasure 1 zero_lt_one a ha).symm

theorem pathLaw_duration_scaling (T : ℝ≥0) (hT : 0 < T) :
    pathLaw T hT = (pathLaw 1 zero_lt_one).map (brownianDilation T) := by
  have hsource := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (bridgeProbability 1 zero_lt_one) (entranceProbability 1 zero_lt_one)
    (tendsto_positiveBridgeProbability 1 zero_lt_one) (continuous_brownianDilation T)
  have htarget := (tendsto_positiveBridgeProbability T hT).comp
    (positive_parameter_dilation_tendsto T hT)
  have he : (fun a : ℝ ↦ (bridgeProbability 1 zero_lt_one a).map
      (continuous_brownianDilation T).measurable.aemeasurable) =ᶠ[𝓝[>] 0]
      (fun a ↦ bridgeProbability T hT (Real.sqrt (T : ℝ)*a)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (bridgeProbability_duration_scaling T hT a ha).symm
  have hp := tendsto_nhds_unique htarget (hsource.congr' he)
  exact congrArg ProbabilityMeasure.toMeasure hp

theorem lintegral_duration_scaling (T : ℝ≥0) (hT : 0 < T)
    (Ψ : Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ f ∂pathLaw T hT) =
      ∫⁻ f, Ψ (brownianDilation T f) ∂pathLaw 1 zero_lt_one := by
  rw [pathLaw_duration_scaling T hT,lintegral_map hΨ (measurable_brownianDilation T)]

theorem integrable_duration_scaling_iff (T : ℝ≥0) (hT : 0 < T)
    (Ψ : Path → ℝ) (hΨ : Measurable Ψ) :
    Integrable Ψ (pathLaw T hT) ↔
      Integrable (fun f ↦ Ψ (brownianDilation T f)) (pathLaw 1 zero_lt_one) := by
  rw [pathLaw_duration_scaling T hT]
  exact integrable_map_measure hΨ.aestronglyMeasurable (measurable_brownianDilation T).aemeasurable

/-- Real integrals transport exactly; the previous theorem gives their
integrability criterion, including for unbounded tests. -/
theorem integral_duration_scaling (T : ℝ≥0) (hT : 0 < T)
    (Ψ : Path → ℝ) (hΨ : Measurable Ψ) :
    (∫ f, Ψ f ∂pathLaw T hT) =
      ∫ f, Ψ (brownianDilation T f) ∂pathLaw 1 zero_lt_one := by
  rw [pathLaw_duration_scaling T hT]
  exact integral_map_of_stronglyMeasurable (measurable_brownianDilation T) hΨ.stronglyMeasurable

end PerronWright.BrownianEntranceDurationScaling
