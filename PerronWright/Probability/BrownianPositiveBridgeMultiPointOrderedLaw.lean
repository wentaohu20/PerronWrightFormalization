import PerronWright.Probability.BrownianPositiveBridgeMultiPointLaw

/-! # Actual positive pinned bridge at arbitrary ordered internal times

A finite strictly ordered vector contains the initial time zero, all
internal evaluation times, and the final pinning time. Its full Borel
law is the proved killed entrance/internal/exit product density.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeMultiPointOrderedLaw

open BrownianPathLaw BrownianPositiveBridgeConditioning
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledFiniteDimensionalOrderedDensity BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianPositiveBridgeMultiPointCoordinates BrownianPositiveBridgeMultiPointLaw

theorem sampleTime_orderedGaps (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hmono : Monotone times) (hzero : times 0 = 0) (i : Fin (n+1)) :
    sampleTime (orderedGaps n times) i.val = times i := by
  have h0 : finiteTimeExtension n times 0 = 0 := by
    calc
      _ = times 0 := finiteTimeExtension_at n times 0
      _ = 0 := hzero
  unfold orderedGaps
  rw [sampleTime_ordered _ (finiteTimeExtension_monotone n times hmono) h0,
    finiteTimeExtension_at]

theorem internalEval_orderedGaps (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hmono : Monotone times) (hzero : times 0 = 0) :
    internalEval n (orderedGaps (n+1) times) =
      fun g : Path ↦ fun i : Fin n ↦ g (times i.succ.castSucc) := by
  funext g i
  unfold internalEval internalTimes
  exact congrArg g (sampleTime_orderedGaps (n+1) times hmono hzero i.succ.castSucc)

theorem ordered_multiPointLaw_eq_withDensity (n : ℕ) (a : ℝ) (ha : 0 < a)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0) :
    (positiveBridgeLaw a (times (Fin.last (n+1)))).map
        (fun g : Path ↦ fun i : Fin n ↦ g (times i.succ.castSucc)) =
      volume.withDensity (multiDensity n a (orderedGaps (n+1) times)) := by
  have hprev : ∀ j < n, 0 < orderedGaps (n+1) times j :=
    fun j hj ↦ orderedGaps_positive (n+1) times hstrict j (by omega)
  have hgap : 0 < orderedGaps (n+1) times n :=
    orderedGaps_positive (n+1) times hstrict n (Nat.lt_succ_self n)
  have hT := sampleTime_orderedGaps (n+1) times hstrict.monotone hzero (Fin.last (n+1))
  simp only [Fin.val_last] at hT
  have he := multiPointLaw_eq_withDensity n a ha (orderedGaps (n+1) times) hprev hgap
  rw [hT,internalEval_orderedGaps n times hstrict.monotone hzero] at he
  exact he

theorem lintegral_ordered_multiPoint (n : ℕ) (a : ℝ) (ha : 0 < a)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (Φ : FreeVector n → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ g, Φ (fun i : Fin n ↦ g (times i.succ.castSucc))
        ∂positiveBridgeLaw a (times (Fin.last (n+1)))) =
      ∫⁻ v, multiDensity n a (orderedGaps (n+1) times) v*Φ v := by
  have hm : Measurable (fun g : Path ↦ fun i : Fin n ↦ g (times i.succ.castSucc)) :=
    (continuous_pi (fun _ ↦ continuous_eval _)).measurable
  rw [← lintegral_map hΦ hm,ordered_multiPointLaw_eq_withDensity n a ha times hstrict hzero,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_multiDensity n a _) hΦ]
  rfl

theorem ordered_multiDensity_integral_eq_one (n : ℕ) (a : ℝ) (ha : 0 < a)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0) :
    (∫⁻ v, multiDensity n a (orderedGaps (n+1) times) v) = 1 := by
  have hgap := orderedGaps_positive (n+1) times hstrict n (Nat.lt_succ_self n)
  have hT := sampleTime_orderedGaps (n+1) times hstrict.monotone hzero (Fin.last (n+1))
  simp only [Fin.val_last] at hT
  have hpos : 0 < times (Fin.last (n+1)) := by
    rw [← hT]
    exact finalTime_pos n _ hgap
  let : IsProbabilityMeasure (positiveBridgeLaw a (times (Fin.last (n+1)))) :=
    positiveBridgeLaw_isProbability a ha _ hpos
  simpa only [mul_one,lintegral_one,measure_univ] using
    (lintegral_ordered_multiPoint n a ha times hstrict hzero (fun _ ↦ 1) measurable_const).symm

end PerronWright.BrownianPositiveBridgeMultiPointOrderedLaw
