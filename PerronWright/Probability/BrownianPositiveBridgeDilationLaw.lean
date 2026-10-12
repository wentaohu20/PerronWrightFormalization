import PerronWright.Probability.BrownianPositiveBridgeDilationGeometry

/-! # Exact scaling of the actual conditioned positive bridge path law

The actual conditional probability is transported by a measurable path
dilation. The conditioning event and its normalizing mass are carried
through the map; no positive-excursion or limiting-path premise is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeDilationLaw

open BrownianPathLaw BrownianPathDilationLaw BrownianFirstPassageBridgeLaw
open BrownianPositiveBridgeConditioning BrownianPositiveBridgeDilationGeometry

theorem conditional_map_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (s : Set β) (hs : MeasurableSet s) :
    ProbabilityTheory.cond (μ.map f) s = (ProbabilityTheory.cond μ (f ⁻¹' s)).map f := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_apply hf hs,Measure.restrict_map hf hs,Measure.map_smul]

theorem conditionedLaw_duration_scaling (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    conditionedLaw (Real.sqrt (T : ℝ)*a) T = (conditionedLaw a 1).map (brownianDilation T) := by
  unfold conditionedLaw
  rw [pinnedLaw_duration_scaling T hT]
  rw [conditional_map_preimage (pinnedLaw 1) (brownianDilation T) (measurable_brownianDilation T)
    _ (measurableSet_bridgeConstraint _ _ _)]
  rw [show -(Real.sqrt (T : ℝ)*a) = -Real.sqrt (T : ℝ)*a by ring,
    brownianDilation_bridgeConstraint_preimage T hT a]

theorem positiveBridgeLaw_duration_scaling (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    positiveBridgeLaw (Real.sqrt (T : ℝ)*a) T =
      (positiveBridgeLaw a 1).map (brownianDilation T) := by
  unfold positiveBridgeLaw
  rw [conditionedLaw_duration_scaling T hT,
    Measure.map_map (measurable_translate _) (measurable_brownianDilation T),
    Measure.map_map (measurable_brownianDilation T) (measurable_translate a)]
  congr 1
  funext g
  exact (brownianDilation_translate T a g).symm

theorem positiveBridgeLaw_unit_normalization (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    positiveBridgeLaw a T = (positiveBridgeLaw (a/Real.sqrt (T : ℝ)) 1).map (brownianDilation T) := by
  have hs : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hT)
  simpa only [mul_div_cancel₀ a hs] using positiveBridgeLaw_duration_scaling T hT (a/Real.sqrt (T : ℝ))

theorem positiveBridgeLaw_lintegral_duration_scaling (T : ℝ≥0) (hT : 0 < T) (a : ℝ)
    (Ψ : Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ g, Ψ g ∂positiveBridgeLaw (Real.sqrt (T : ℝ)*a) T) =
      ∫⁻ g, Ψ (brownianDilation T g) ∂positiveBridgeLaw a 1 := by
  rw [positiveBridgeLaw_duration_scaling T hT a,lintegral_map hΨ (measurable_brownianDilation T)]

end PerronWright.BrownianPositiveBridgeDilationLaw
