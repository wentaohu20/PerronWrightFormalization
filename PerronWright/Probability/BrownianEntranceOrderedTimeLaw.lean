import PerronWright.Probability.BrownianEntranceArbitraryTimeLaw

/-! # Genuine entrance-product marginals at arbitrary ordered real times

The actual continuous entrance path law has the literal Gaussian-kernel
entrance product at every strictly ordered deterministic interior tuple.
Its coupled Borel test formula follows from this proved measure identity;
no finite-dimensional-law premise is imposed on the path law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceOrderedTimeLaw

open BrownianPathLaw BrownianEntranceContinuousRealization BrownianEntranceArbitraryTimeLaw
open BrownianEntranceFiniteDimensionalFamily BrownianPositiveBridgeMultiPointMass
open BrownianKilledFiniteDimensionalOrderedTimes BrownianPositiveBridgeMultiPointEntrance

theorem pathLaw_ordered_eq (T : ℝ≥0) (hT : 0 < T) (k : ℕ)
    (times : Fin (k+2) → ℝ≥0) (hs : StrictMono times) (hzero : times 0 = 0)
    (hfinal : times (Fin.last (k+1)) = T) :
    (pathLaw T hT).map (orderedEval k times) = orderedLaw k times := by
  apply map_eq_of_actual_bounded_test_limit T hT _ (continuous_orderedEval k times)
  intro Ψ
  have he := actual_ordered_bounded_test_tendsto k times hs hzero
    (nndist Ψ 0 : ℝ) (fun v ↦ (Ψ v : ℝ≥0∞))
    (ENNReal.continuous_coe.measurable.comp Ψ.continuous.measurable)
    (fun v ↦ by
      rw [ENNReal.ofReal_coe_nnreal]
      exact ENNReal.coe_le_coe.mpr (BoundedContinuousFunction.NNReal.upper_bound Ψ v))
  rwa [hfinal] at he

theorem pathLaw_ordered_entrance_eq (T : ℝ≥0) (hT : 0 < T) (n : ℕ)
    (times : Fin (n+3) → ℝ≥0) (hs : StrictMono times) (hzero : times 0 = 0)
    (hfinal : times (Fin.last (n+2)) = T) :
    (pathLaw T hT).map (orderedEval (n+1) times) = entranceLaw n (orderedGaps (n+2) times) :=
  pathLaw_ordered_eq T hT (n+1) times hs hzero hfinal

theorem pathLaw_ordered_lintegral (T : ℝ≥0) (hT : 0 < T) (k : ℕ)
    (times : Fin (k+2) → ℝ≥0) (hs : StrictMono times) (hzero : times 0 = 0)
    (hfinal : times (Fin.last (k+1)) = T) (Ψ : (Fin k → ℝ) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (orderedEval k times f) ∂pathLaw T hT) = ∫⁻ v, Ψ v ∂orderedLaw k times := by
  rw [← lintegral_map hΨ (continuous_orderedEval k times).measurable,
    pathLaw_ordered_eq T hT k times hs hzero hfinal]

theorem pathLaw_ordered_entrance_lintegral (T : ℝ≥0) (hT : 0 < T) (n : ℕ)
    (times : Fin (n+3) → ℝ≥0) (hs : StrictMono times) (hzero : times 0 = 0)
    (hfinal : times (Fin.last (n+2)) = T)
    (Ψ : (Fin (n+1) → ℝ) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (orderedEval (n+1) times f) ∂pathLaw T hT) =
      ∫⁻ v, entranceProduct n (orderedGaps (n+2) times) v * Ψ v := by
  rw [pathLaw_ordered_lintegral T hT (n+1) times hs hzero hfinal Ψ hΨ]
  change (∫⁻ v, Ψ v ∂volume.withDensity (entranceProduct n (orderedGaps (n+2) times))) = _
  exact lintegral_withDensity_eq_lintegral_mul volume
    (measurable_entranceProduct n (orderedGaps (n+2) times)) hΨ

theorem pathLaw_ordered_probability (T : ℝ≥0) (hT : 0 < T) (k : ℕ)
    (times : Fin (k+2) → ℝ≥0) (hs : StrictMono times) (hzero : times 0 = 0)
    (hfinal : times (Fin.last (k+1)) = T) {B : Set (Fin k → ℝ)} (hB : MeasurableSet B) :
    pathLaw T hT ((orderedEval k times) ⁻¹' B) = orderedLaw k times B := by
  rw [← Measure.map_apply (continuous_orderedEval k times).measurable hB,
    pathLaw_ordered_eq T hT k times hs hzero hfinal]

end PerronWright.BrownianEntranceOrderedTimeLaw
