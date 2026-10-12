import PerronWright.Probability.BrownianPositiveBridgeMultiPointTests
import PerronWright.Probability.BrownianPositiveBridgeMultiPointOrderedLaw

/-! # Actual finite positive-bridge coupled tests as the endpoint vanishes

The true conditioned pinned-path law is used, not a candidate density law.
Its already proved multi-point Radon--Nikodym identity connects the new
numeric entrance--interior--exit limits to actual arbitrary ordered times.
No path weak-limit or positive-excursion identification is asserted.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeMultiPointActualTests

open BrownianPathLaw BrownianPositiveBridgeConditioning
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledFiniteDimensionalOrderedDensity BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianPositiveBridgeMultiPointCoordinates BrownianPositiveBridgeMultiPointLaw
open BrownianPositiveBridgeMultiPointOrderedLaw BrownianPositiveBridgeMultiPointEntrance
open BrownianPositiveBridgeMultiPointTests

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

theorem rawMultiDensity_eq_actual_density (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) :
    rawMultiDensity n a gaps = multiDensity (n+1) a gaps := rfl

theorem actual_multiDensity_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (v : FreeVector (n+1)) :
    Tendsto (fun a ↦ multiDensity (n+1) a gaps v) (𝓝[>] (0 : ℝ))
      (𝓝 (entranceProduct n gaps v)) := by
  have hT : 0 < sampleTime gaps (n+2) := by
    rw [sampleTime_succ]
    exact (hgaps (n+1) (by omega)).trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ _))
  exact rawMultiDensity_tendsto n gaps (hgaps 0 (by omega)) (hgaps (n+1) (by omega)) hT v

theorem actual_bounded_compact_test_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (K : Set (FreeVector (n+1))) (hK : IsCompact K)
    (b C : ℝ) (hb : 0 ≤ b) (hKb : ∀ v ∈ K, ∀ i, v i ≤ b)
    (Ψ : FreeVector (n+1) → ℝ≥0∞) (hΨ : Measurable Ψ)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ g, K.indicator Ψ (internalEval (n+1) gaps g)
        ∂positiveBridgeLaw a (sampleTime gaps (n+2)))
      (𝓝[>] 0) (𝓝 (∫⁻ v in K, entranceProduct n gaps v*Ψ v)) := by
  have he := bounded_compact_test_tendsto n gaps hgaps K hK b C hb hKb Ψ hΨ hbound
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [multiPoint_lintegral (n+1) a ha gaps (fun j hj ↦ hgaps j (by omega))
    (hgaps (n+1) (by omega)) (K.indicator Ψ) (hΨ.indicator hK.measurableSet)]
  rw [← lintegral_indicator hK.measurableSet]
  apply lintegral_congr
  intro v
  by_cases hv : v ∈ K
  · rw [indicator_of_mem hv,indicator_of_mem hv]
    rfl
  · rw [indicator_of_notMem hv,indicator_of_notMem hv,mul_zero]

theorem actual_bounded_rectangle_test_tendsto (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) (l u : FreeVector (n+1))
    (b C : ℝ) (hb : 0 ≤ b) (hu : ∀ i, u i ≤ b)
    (Ψ : FreeVector (n+1) → ℝ≥0∞) (hΨ : Measurable Ψ)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ g, (Icc l u).indicator Ψ (internalEval (n+1) gaps g)
        ∂positiveBridgeLaw a (sampleTime gaps (n+2)))
      (𝓝[>] 0) (𝓝 (∫⁻ v in Icc l u, entranceProduct n gaps v*Ψ v)) :=
  actual_bounded_compact_test_tendsto n gaps hgaps (Icc l u) isCompact_Icc b C hb
    (fun _v hv i ↦ (hv.2 i).trans (hu i)) Ψ hΨ hbound

theorem actual_ordered_bounded_rectangle_test_tendsto (n : ℕ)
    (times : Fin (n+3) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (l u : FreeVector (n+1)) (b C : ℝ) (hb : 0 ≤ b) (hu : ∀ i, u i ≤ b)
    (Ψ : FreeVector (n+1) → ℝ≥0∞) (hΨ : Measurable Ψ)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ g, (Icc l u).indicator Ψ
        (fun i : Fin (n+1) ↦ g (times i.succ.castSucc))
          ∂positiveBridgeLaw a (times (Fin.last (n+2))))
      (𝓝[>] 0) (𝓝 (∫⁻ v in Icc l u, entranceProduct n (orderedGaps (n+2) times) v*Ψ v)) := by
  have hgaps : ∀ j < n+2, 0 < orderedGaps (n+2) times j :=
    fun j hj ↦ orderedGaps_positive (n+2) times hstrict j hj
  have he := actual_bounded_rectangle_test_tendsto n (orderedGaps (n+2) times)
    hgaps l u b C hb hu Ψ hΨ hbound
  have hT := sampleTime_orderedGaps (n+2) times hstrict.monotone hzero (Fin.last (n+2))
  simp only [Fin.val_last] at hT
  rw [hT,internalEval_orderedGaps (n+1) times hstrict.monotone hzero] at he
  exact he

end PerronWright.BrownianPositiveBridgeMultiPointActualTests
