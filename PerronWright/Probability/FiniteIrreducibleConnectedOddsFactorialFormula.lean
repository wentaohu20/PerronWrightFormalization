import PerronWright.Probability.FiniteIrreducibleConnectedOddsWeights

/-!
# Genuine arbitrary-count finite factorial formula with connected odds products

All selected-type vectors are allowed. Nonrealizable vectors are killed
by their proved zero falling-factorial selection factor, so the terminal
uses only literal count-based isolation and connected simple-graph sums.
The right side no longer depends on the ordering of ambient vertex types.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleConnectedOddsFactorialFormula

open ComponentCounts AnnealedTupleResidualCounting
open FiniteIrreducibleTypedGraphLaw FiniteIrreducibleTypePlacementMultiplicity
open FiniteIrreducibleTypedFactorialIsolationFormula FiniteIrreducibleConnectedOddsWeights

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The exact B_n(K) written using any prescribed actual integer counts. -/
def countIsolationBudget (M : FiniteIrreducibleModel S) (c : S → ℕ)
    {q : ℕ} {k : Fin q → ℕ} (y : SelectedVertices k → S) : ℝ :=
  (∑ a : S, ∑ b : S, (fiberCount y a : ℝ) * M.kernel a b * (c b : ℝ)) -
    (∑ a : S, ∑ b : S, (fiberCount y a : ℝ) * M.kernel a b * (fiberCount y b : ℝ)) / 2 -
    (∑ a : S, (fiberCount y a : ℝ) * M.kernel a a) / 2

theorem typedIsolationBudget_eq_countIsolationBudget
    (M : FiniteIrreducibleModel S) {n q : ℕ} {k : Fin q → ℕ}
    (x : Fin n → S) (c : S → ℕ) (hc : ∀ a, fiberCount x a = c a)
    (y : SelectedVertices k → S) :
    typedIsolationBudget M x y = countIsolationBudget M c y := by
  unfold typedIsolationBudget countIsolationBudget
  simp_rw [hc]

/-- After weighting by actual placement multiplicity, the representative
pattern odds can always be replaced by the product of literal connected
graph sums, also for unrealizable selected type vectors. -/
theorem weighted_selectedTypePatternOdds_eq_connectedOdds_product
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (y : SelectedVertices k → S) :
    (∏ a : S, ((fiberCount x a).descFactorial (fiberCount y a) : ℝ)) *
        Real.exp (-(t / (n : ℝ) * typedIsolationBudget M x y)) *
          selectedTypePatternOdds M t x k r hk y =
      (∏ a : S, ((fiberCount x a).descFactorial (fiberCount y a) : ℝ)) *
        Real.exp (-(t / (n : ℝ) * typedIsolationBudget M x y)) *
          (∏ i, connectedOddsWeight M t n (fun a ↦ y ⟨i,a⟩) (r i)) := by
  by_cases h : Nonempty (TypePreservingEmbeddings y x)
  · rw [selectedTypePatternOdds_eq_product_connectedOddsWeight M t ht x k r hk y
      (Classical.choice h)]
  · rw [selectionFactor_eq_zero_of_not_realizable y x h]
    simp only [zero_mul]

theorem factorial_expectation_connectedOdds_formula
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    (∫ G, (count G k r : ℝ) ∂law M t ht x) =
      (∑ y : SelectedVertices k → S,
        (∏ a : S, ((fiberCount x a).descFactorial (fiberCount y a) : ℝ)) *
          Real.exp (-(t / (n : ℝ) * typedIsolationBudget M x y)) *
            (∏ i, connectedOddsWeight M t n (fun a ↦ y ⟨i,a⟩) (r i))) /
        (∏ i, ((k i).factorial : ℝ)) := by
  rw [factorial_expectation_isolation_formula M t ht x k r hk]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  exact weighted_selectedTypePatternOdds_eq_connectedOdds_product M t ht x k r hk y

/-- The paper's genuine fixed-count factorial formula, with no arbitrary
profile or graph-probability interface and no chosen rounding scheme.
The right side depends on actual counts, not on their ambient ordering. -/
theorem factorial_expectation_connectedOdds_formula_of_counts
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (c : S → ℕ)
    (hc : ∀ a, fiberCount x a = c a)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    (∫ G, (count G k r : ℝ) ∂law M t ht x) =
      (∑ y : SelectedVertices k → S,
        (∏ a : S, ((c a).descFactorial (fiberCount y a) : ℝ)) *
          Real.exp (-(t / (n : ℝ) * countIsolationBudget M c y)) *
            (∏ i, connectedOddsWeight M t n (fun a ↦ y ⟨i,a⟩) (r i))) /
        (∏ i, ((k i).factorial : ℝ)) := by
  rw [factorial_expectation_connectedOdds_formula M t ht x k r hk]
  simp_rw [typedIsolationBudget_eq_countIsolationBudget M x c hc, hc]

theorem factorial_expectation_eq_of_same_counts
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x x' : Fin n → S) (c : S → ℕ)
    (hx : ∀ a, fiberCount x a = c a) (hx' : ∀ a, fiberCount x' a = c a)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    (∫ G, (count G k r : ℝ) ∂law M t ht x) =
      ∫ G, (count G k r : ℝ) ∂law M t ht x' := by
  rw [factorial_expectation_connectedOdds_formula_of_counts M t ht x c hx k r hk,
    factorial_expectation_connectedOdds_formula_of_counts M t ht x' c hx' k r hk]

end PerronWright.FiniteIrreducibleConnectedOddsFactorialFormula

