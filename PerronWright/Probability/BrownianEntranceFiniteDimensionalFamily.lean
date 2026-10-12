import PerronWright.Probability.BrownianPositiveBridgeMultiPointGlobalTests

/-! # Genuine deletion consistency of entrance finite-dimensional laws

The empty law is included explicitly. For every nonempty ordered interior
tuple the law is the proved entrance-product probability measure. Coordinate
deletion is proved by uniqueness of the limits of the actual positive-bridge
Borel probabilities, not by a projective-consistency assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceFiniteDimensionalFamily

open BrownianPathLaw BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeMultiPointMass BrownianPositiveBridgeMultiPointGlobalTests
open BrownianKilledFiniteDimensionalOrderedTimes BrownianKilledFiniteDimensionalOrderedDensity

def orderedLaw : (k : ℕ) → (Fin (k+2) → ℝ≥0) → Measure (Fin k → ℝ)
  | 0, _ => Measure.dirac 0
  | n+1, times => entranceLaw n (orderedGaps (n+2) times)

def orderedEval (k : ℕ) (times : Fin (k+2) → ℝ≥0) (f : Path) : Fin k → ℝ :=
  fun i ↦ f (times i.succ.castSucc)

theorem continuous_orderedEval (k : ℕ) (times : Fin (k+2) → ℝ≥0) :
    Continuous (orderedEval k times) :=
  continuous_pi (fun _ ↦ continuous_eval_const _)

theorem orderedLaw_isProbability (k : ℕ) (times : Fin (k+2) → ℝ≥0)
    (hstrict : StrictMono times) : IsProbabilityMeasure (orderedLaw k times) := by
  cases k with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n =>
    exact entranceLaw_isProbability n (orderedGaps (n+2) times)
      (fun j hj ↦ orderedGaps_positive (n+2) times hstrict j hj)

theorem actual_ordered_bounded_test_tendsto (k : ℕ) (times : Fin (k+2) → ℝ≥0)
    (hstrict : StrictMono times) (hzero : times 0 = 0)
    (C : ℝ) (Ψ : (Fin k → ℝ) → ℝ≥0∞) (hΨ : Measurable Ψ)
    (hbound : ∀ v, Ψ v ≤ ENNReal.ofReal C) :
    Tendsto (fun a : ℝ ↦ ∫⁻ g, Ψ (orderedEval k times g)
      ∂positiveBridgeLaw a (times (Fin.last (k+1)))) (𝓝[>] 0)
      (𝓝 (∫⁻ v, Ψ v ∂orderedLaw k times)) := by
  cases k with
  | zero =>
    have hT : 0 < times (Fin.last 1) := by
      rw [← hzero]
      exact hstrict (by decide : (0 : Fin 2) < Fin.last 1)
    have he : ∀ᶠ a : ℝ in 𝓝[>] 0,
        (∫⁻ g, Ψ (orderedEval 0 times g) ∂positiveBridgeLaw a (times (Fin.last 1))) = Ψ 0 := by
      filter_upwards [self_mem_nhdsWithin] with a ha
      let := positiveBridgeLaw_isProbability a ha (times (Fin.last 1)) hT
      have hv (g : Path) : orderedEval 0 times g = 0 := Subsingleton.elim _ _
      simp only [hv,lintegral_const,measure_univ, mul_one]
    simpa only [orderedLaw,lintegral_dirac' _ hΨ] using
      (tendsto_const_nhds (x := Ψ 0)).congr' (he.mono (fun _ ha ↦ ha.symm))
  | succ n =>
    exact actual_ordered_global_bounded_test_tendsto n times hstrict hzero C Ψ hΨ hbound

theorem actual_ordered_borel_probability_tendsto (k : ℕ) (times : Fin (k+2) → ℝ≥0)
    (hstrict : StrictMono times) (hzero : times 0 = 0)
    {B : Set (Fin k → ℝ)} (hB : MeasurableSet B) :
    Tendsto (fun a : ℝ ↦ ((positiveBridgeLaw a (times (Fin.last (k+1)))).map
      (orderedEval k times)) B) (𝓝[>] 0) (𝓝 (orderedLaw k times B)) := by
  have he := actual_ordered_bounded_test_tendsto k times hstrict hzero 1
    (B.indicator (fun _ ↦ 1)) (measurable_const.indicator hB)
    (fun v ↦ by by_cases hv : v ∈ B <;> simp [hv])
  have h1 : (fun _ : Fin k → ℝ ↦ (1 : ℝ≥0∞)) = (1 : (Fin k → ℝ) → ℝ≥0∞) := rfl
  have hl : (∫⁻ v, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) v ∂orderedLaw k times) =
      orderedLaw k times B := by rw [h1]; exact lintegral_indicator_one hB
  rw [hl] at he
  apply he.congr
  intro a
  rw [← lintegral_map (measurable_const.indicator hB) (continuous_orderedEval k times).measurable,
    h1,lintegral_indicator_one hB]

def selectCoordinates {k l : ℕ} (e : Fin l → Fin k) (v : Fin k → ℝ) : Fin l → ℝ :=
  fun i ↦ v (e i)

theorem measurable_selectCoordinates {k l : ℕ} (e : Fin l → Fin k) :
    Measurable (selectCoordinates e) := measurable_pi_lambda _ (fun i ↦ measurable_pi_apply (e i))

/-- Actual coordinate deletion, including deletion of every interior point. -/
theorem orderedLaw_map_select (k l : ℕ)
    (times : Fin (k+2) → ℝ≥0) (small : Fin (l+2) → ℝ≥0)
    (ht : StrictMono times) (hs : StrictMono small)
    (ht0 : times 0 = 0) (hs0 : small 0 = 0)
    (hT : times (Fin.last (k+1)) = small (Fin.last (l+1)))
    (e : Fin l → Fin k)
    (hmatch : ∀ i, times (e i).succ.castSucc = small i.succ.castSucc) :
    (orderedLaw k times).map (selectCoordinates e) = orderedLaw l small := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_selectCoordinates e) hB]
  have hb := actual_ordered_borel_probability_tendsto k times ht ht0
    ((measurable_selectCoordinates e) hB)
  have hs' := actual_ordered_borel_probability_tendsto l small hs hs0 hB
  apply tendsto_nhds_unique hb
  apply hs'.congr
  intro a
  rw [Measure.map_apply (continuous_orderedEval k times).measurable
    ((measurable_selectCoordinates e) hB),
    Measure.map_apply (continuous_orderedEval l small).measurable hB,hT]
  congr 1
  ext g
  change orderedEval l small g ∈ B ↔ selectCoordinates e (orderedEval k times g) ∈ B
  have he : selectCoordinates e (orderedEval k times g) = orderedEval l small g := by
    funext i
    exact congrArg g (hmatch i)
  rw [he]

end PerronWright.BrownianEntranceFiniteDimensionalFamily
