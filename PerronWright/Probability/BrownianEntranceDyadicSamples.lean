import PerronWright.Probability.BrownianEntranceCountableLaw
import PerronWright.Probability.DyadicGeometricApproximation
import Mathlib.Data.Nat.Pairing

/-! # Genuine compatible clamped dyadic samples of the entrance law

The sampling labels enumerate every clamped dyadic time. Equality of labels
with the same physical time is proved from the constructed law's exact
finite marginals. In particular compatibility and both endpoint values are
actual almost-everywhere facts, not regularity assumptions.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceDyadicSamples

open BrownianEntranceCountableLaw DyadicFloorGeometry DyadicGeometricApproximation

theorem ae_countableLaw_equal_time (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0)
    (i j : ℕ) (hij : σ i = σ j) : ∀ᵐ x ∂BrownianEntranceCountableLaw.law T hT σ, x i = x j := by
  let J : Finset ℕ := {i,j}
  let u : J := ⟨i,by simp [J]⟩
  let v : J := ⟨j,by simp [J]⟩
  have he : ∀ᵐ z ∂sampleLaw T σ J, z u = z v := by
    unfold sampleLaw
    apply (ae_map_iff (measurable_sampleFromFinite σ J).aemeasurable
      (measurableSet_eq_fun (measurable_pi_apply u) (measurable_pi_apply v))).mpr
    apply Eventually.of_forall
    intro z
    change z ⟨σ i,_⟩ = z ⟨σ j,_⟩
    exact congrArg z (Subtype.ext hij)
  rw [← law_projectiveLimit T hT σ J] at he
  exact (ae_map_iff (Finset.measurable_restrict J).aemeasurable
    (measurableSet_eq_fun (measurable_pi_apply u) (measurable_pi_apply v))).mp he

theorem ae_countableLaw_all_equal_times (T : ℝ≥0) (hT : 0 < T) (σ : ℕ → ℝ≥0) :
    ∀ᵐ x ∂BrownianEntranceCountableLaw.law T hT σ, ∀ i j, σ i = σ j → x i = x j := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : σ i = σ j
  · filter_upwards [ae_countableLaw_equal_time T hT σ i j hij] with x hx
    exact fun _ ↦ hx
  · exact Eventually.of_forall (fun _ h ↦ (hij h).elim)

def clampedTime (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := min (coordinate n k) T

def samplingTimes (T : ℝ≥0) (i : ℕ) : ℝ≥0 :=
  clampedTime T (Nat.unpair i).1 (Nat.unpair i).2

theorem samplingTimes_pair (T : ℝ≥0) (n k : ℕ) :
    samplingTimes T (Nat.pair n k) = clampedTime T n k := by
  simp only [samplingTimes,Nat.unpair_pair]

theorem clampedTime_succ_even (T : ℝ≥0) (n k : ℕ) :
    clampedTime T (n+1) (2*k) = clampedTime T n k := by
  rw [clampedTime,coordinate_succ_even]
  rfl

theorem clampedTime_zero (T : ℝ≥0) (n : ℕ) : clampedTime T n 0 = 0 := by
  simp [clampedTime,coordinate]

theorem clampedTime_le_horizon (T : ℝ≥0) (n k : ℕ) : clampedTime T n k ≤ T :=
  min_le_right _ _

def samples (x : ℕ → ℝ) (n k : ℕ) : ℝ := x (Nat.pair n k)

theorem measurable_sample (n k : ℕ) : Measurable (fun x : ℕ → ℝ ↦ samples x n k) :=
  measurable_pi_apply _

theorem measurable_samples : Measurable samples :=
  measurable_pi_lambda _ (fun n ↦ measurable_pi_lambda _ (fun k ↦ measurable_sample n k))

def law (T : ℝ≥0) (hT : 0 < T) : Measure (ℕ → ℝ) :=
  BrownianEntranceCountableLaw.law T hT (samplingTimes T)

theorem law_isProbability (T : ℝ≥0) (hT : 0 < T) : IsProbabilityMeasure (law T hT) :=
  BrownianEntranceCountableLaw.law_isProbability T hT (samplingTimes T)

theorem ae_samples_equal_times (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, ∀ n k m l, clampedTime T n k = clampedTime T m l →
      samples x n k = samples x m l := by
  filter_upwards [ae_countableLaw_all_equal_times T hT (samplingTimes T)] with x hx
  intro n k m l he
  exact hx (Nat.pair n k) (Nat.pair m l) (by simpa only [samplingTimes_pair] using he)

theorem ae_samples_compatible (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, Compatible (samples x) := by
  filter_upwards [ae_samples_equal_times T hT] with x hx
  exact fun n k ↦ hx (n+1) (2*k) n k (clampedTime_succ_even T n k)

theorem ae_samples_boundary_zero (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, ∀ n k, ¬ (0 < clampedTime T n k ∧ clampedTime T n k < T) →
      samples x n k = 0 := by
  filter_upwards [ae_law_boundary_zero T hT (samplingTimes T)] with x hx
  intro n k he
  exact hx (Nat.pair n k) (by simpa only [samplingTimes_pair] using he)

theorem ae_samples_initial_zero (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, ∀ n, samples x n 0 = 0 := by
  filter_upwards [ae_samples_boundary_zero T hT] with x hx
  intro n
  exact hx n 0 (by simp only [clampedTime_zero,lt_self_iff_false,false_and,not_false_eq_true])

theorem ae_samples_terminal_zero (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ x ∂law T hT, ∀ n k, T ≤ coordinate n k → samples x n k = 0 := by
  filter_upwards [ae_samples_boundary_zero T hT] with x hx
  intro n k hk
  apply hx n k
  rw [clampedTime,min_eq_right hk]
  simp

end PerronWright.BrownianEntranceDyadicSamples
