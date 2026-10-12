import PerronWright.Probability.CountableFiniteAtomSampling
import PerronWright.Probability.FinitePointMeasureRectangleFactorials

/-!
# Exact tuple sums for an actual finite countable-index selection

Injectivity is in the atom labels, not in atom positions: multiplicity
is retained. The finite embedding bijection proves the nonnegative
countable-sum formula, including arbitrary overlapping slot cells.
-/

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableFiniteTupleSampling

open FinitePointMeasureCompact FinitePointMeasureRectangleFactorials
open CountableFiniteAtomSampling

variable {I E J : Type*} [Fintype J]

def sampledTupleEquiv (t : Finset I) (x : I → E) (A : J → Set E) :
    {e : J → I // Function.Injective e ∧ ∀ j, e j ∈ t ∧ x (e j) ∈ A j} ≃
      {e : J ↪ t // ∀ j, x (e j).1 ∈ A j} where
  toFun e := ⟨⟨fun j ↦ ⟨e.val j,(e.2.2 j).1⟩, by
    intro j k h
    exact e.2.1 (congrArg Subtype.val h)⟩,fun j ↦ (e.2.2 j).2⟩
  invFun e := ⟨fun j ↦ (e.val j).1, (by
    intro j k h
    exact e.val.injective (Subtype.ext h)),fun j ↦ ⟨(e.val j).2,e.2 j⟩⟩
  left_inv e := rfl
  right_inv e := rfl

theorem tsum_tuple_test_eq_finite_sum (t : Finset I) (x : I → E) (A : J → Set E)
    (Ψ : (J → E) → ℝ≥0∞) :
    (∑' e : J → I, if Function.Injective e ∧ ∀ j, e j ∈ t ∧ x (e j) ∈ A j
      then Ψ (fun j ↦ x (e j)) else 0) =
    ∑ e : {e : J ↪ t // ∀ j, x (e j).1 ∈ A j}, Ψ (fun j ↦ x (e.val j).1) := by
  let P : Set (J → I) := {e | Function.Injective e ∧ ∀ j, e j ∈ t ∧ x (e j) ∈ A j}
  calc
    _ = ∑' e : P, Ψ (fun j ↦ x (e.val j)) := by
      simpa only [Set.indicator_apply,P,Set.mem_ofPred_eq] using
        (tsum_subtype P (fun e : J → I ↦ Ψ (fun j ↦ x (e j)))).symm
    _ = ∑' e : {e : J ↪ t // ∀ j, x (e j).1 ∈ A j}, Ψ (fun j ↦ x (e.val j).1) :=
      (sampledTupleEquiv t x A).tsum_eq
        (fun e : {e : J ↪ t // ∀ j, x (e j).1 ∈ A j} ↦ Ψ (fun j ↦ x (e.val j).1))
    _ = _ := tsum_fintype _

theorem tsum_tuple_indicator_eq_card (t : Finset I) (x : I → E) (A : J → Set E) :
    (∑' e : J → I, if Function.Injective e ∧ ∀ j, e j ∈ t ∧ x (e j) ∈ A j
      then (1 : ℝ≥0∞) else 0) =
      (Fintype.card {e : J ↪ t // ∀ j, x (e j).1 ∈ A j} : ℝ≥0∞) := by
  simpa using tsum_tuple_test_eq_finite_sum t x A (fun _ ↦ 1)

variable [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
  [SecondCountableTopology E]

omit [TopologicalSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem rectangleFactorial_ofFinset (t : Finset I) (x : I → E) (A : J → Set E)
    (hA : ∀ j, MeasurableSet (A j)) :
    (rectangleFactorial (ofFinset t x) A : ℝ≥0∞) =
      ∑' e : J → I, if Function.Injective e ∧ ∀ j, e j ∈ t ∧ x (e j) ∈ A j
        then (1 : ℝ≥0∞) else 0 := by
  rw [tsum_tuple_indicator_eq_card]
  exact congrArg (fun n : ℕ ↦ (n : ℝ≥0∞))
    (rectangleFactorial_ofFintype (fun i : t ↦ x i.1) A hA)

variable {S : Type*} [MeasurableSpace S] [Countable I]

omit [TopologicalSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace S] [Countable I] in
theorem rectangleFactorial_pointMeasure (B : S → Set I) (X : S → I → E)
    (s : S) (hB : (B s).Finite) (A : J → Set E) (hA : ∀ j, MeasurableSet (A j)) :
    (rectangleFactorial (pointMeasure B X s) A : ℝ≥0∞) =
      ∑' e : J → I, if Function.Injective e ∧ ∀ j, e j ∈ B s ∧ X s (e j) ∈ A j
        then (1 : ℝ≥0∞) else 0 := by
  have ht : B s = (hB.toFinset : Set I) := by
    ext i
    exact (Set.Finite.mem_toFinset hB).symm
  rw [pointMeasure_eq_ofFinset B X s hB.toFinset ht,rectangleFactorial_ofFinset _ _ _ hA]
  exact tsum_congr (fun e ↦ by simp only [Set.Finite.mem_toFinset])

end PerronWright.CountableFiniteTupleSampling
