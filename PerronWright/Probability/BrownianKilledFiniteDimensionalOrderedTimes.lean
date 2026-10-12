import PerronWright.Probability.BrownianKilledFiniteDimensionalLaw

/-! # Arbitrary finite ordered-time killed Brownian source

A finite monotone time vector is extended constantly after its last
coordinate. This proves the actual finite-vector endpoint law directly,
without requiring the user to supply any infinite time-sequence extension.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledFiniteDimensionalOrderedTimes

open BrownianPathLaw ContinuousPathFirstPassage BrownianKilledFiniteDimensionalCoordinates
open BrownianKilledFiniteDimensionalLaw

def finiteTimeExtension (n : ℕ) (times : Fin (n+1) → ℝ≥0) (j : ℕ) : ℝ≥0 :=
  times ⟨min j n,by omega⟩

theorem finiteTimeExtension_monotone (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hmono : Monotone times) : Monotone (finiteTimeExtension n times) := by
  intro i j hij
  apply hmono
  change min i n ≤ min j n
  exact min_le_min hij le_rfl

@[simp] theorem finiteTimeExtension_at (n : ℕ) (times : Fin (n+1) → ℝ≥0) (i : Fin (n+1)) :
    finiteTimeExtension n times i.val = times i := by
  unfold finiteTimeExtension
  congr 1
  apply Fin.ext
  exact min_eq_left (Nat.le_of_lt_succ i.isLt)

def orderedGaps (n : ℕ) (times : Fin (n+1) → ℝ≥0) (j : ℕ) : ℝ≥0 :=
  finiteTimeExtension n times (j+1)-finiteTimeExtension n times j

/-- Actual source law of every finite nondecreasing deterministic-time
tuple, including its initial point. The only assumptions are the literal
ordering and the first time being zero; repeated times are permitted. -/
theorem finite_ordered_endpoint_law (level x : ℝ) (n : ℕ)
    (times : Fin (n+1) → ℝ≥0) (hmono : Monotone times) (hzero : times 0 = 0) :
    (pathLaw.restrict (survival (level-x) (times (Fin.last n)))).map
        (fun f : Path ↦ fun i : Fin (n+1) ↦ x+f (times i)) =
      chainLaw level x (orderedGaps n times) n := by
  have h0 : finiteTimeExtension n times 0 = 0 := by
    calc
      _ = times 0 := finiteTimeExtension_at n times 0
      _ = 0 := hzero
  have ht : finiteTimeExtension n times n = times (Fin.last n) :=
    finiteTimeExtension_at n times (Fin.last n)
  have h := ordered_endpoint_law level x (finiteTimeExtension n times)
    (finiteTimeExtension_monotone n times hmono) h0 n
  unfold orderedGaps
  simpa only [ht,finiteTimeExtension_at] using h

theorem lintegral_finite_ordered_endpoints (level x : ℝ) (n : ℕ)
    (times : Fin (n+1) → ℝ≥0) (hmono : Monotone times) (hzero : times 0 = 0)
    {Φ : EndpointVector n → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f in survival (level-x) (times (Fin.last n)),
        Φ (fun i : Fin (n+1) ↦ x+f (times i)) ∂pathLaw) =
      ∫⁻ v, Φ v ∂chainLaw level x (orderedGaps n times) n := by
  have hm : Measurable (fun f : Path ↦ fun i : Fin (n+1) ↦ x+f (times i)) :=
    measurable_pi_lambda _ (fun i ↦ measurable_const.add (continuous_eval _).measurable)
  rw [← finite_ordered_endpoint_law level x n times hmono hzero,lintegral_map hΦ hm]

end PerronWright.BrownianKilledFiniteDimensionalOrderedTimes
