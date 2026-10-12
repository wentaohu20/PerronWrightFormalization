import PerronWright.Probability.FiniteIrreducibleFixedTypeExchangeability
import PerronWright.Probability.AnnealedTupleResidualPatternFormula

/-!
# Exact deterministic finite component factorial formula by selected types

The left side counts ordered distinct genuine components. On the right,
the exact multiplicity of each selected type vector is the product of
the actual ambient type-count falling factorials. The representative
placed probability is well-defined by proved within-type invariance;
impossible type vectors contribute zero. No target-law substitution,
profile limit, or asymptotic probability statement is made.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleFixedTypeFactorialFormula

open AnnealedGraph ComponentCounts ExactFactorialExpectation SelectedConfiguration
open AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
open FiniteIrreducibleTypedGraphLaw FiniteIrreducibleTypePlacementMultiplicity
open FiniteIrreducibleFixedTypeExchangeability

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact internal-labelling regrouping for an arbitrary actual fixed
assignment and the actual graph probability measure. -/
theorem expectation_mul_factorials_eq_sum_placement_probabilities
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ) :
    (∫ G, (count G k r : ℝ) ∂law M t ht x) *
        (∏ i, ((k i).factorial : ℝ)) =
      ∑ f : Placements n k, placementProbability M t ht x k r f := by
  unfold placementProbability
  rw [← integral_mul_const]
  simp_rw [count_mul_factorials_eq_sum_placements]
  rw [integral_finsetSum]
  intro f _
  exact Integrable.of_finite

theorem expectation_eq_div_sum_placement_probabilities
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ) :
    (∫ G, (count G k r : ℝ) ∂law M t ht x) =
      (∑ f : Placements n k, placementProbability M t ht x k r f) /
        (∏ i, ((k i).factorial : ℝ)) := by
  apply (eq_div_iff (factorialProduct_pos k).ne').mpr
  exact expectation_mul_factorials_eq_sum_placement_probabilities M t ht x k r

/-- The actual probability for any realization of this full selected
type vector. Within-type invariance proves independence of the choice;
zero is used precisely when no actual placement exists. -/
def selectedTypeProbability (M : FiniteIrreducibleModel S)
    (t : ℝ) (ht : 0 ≤ t) {n q : ℕ} (x : Fin n → S)
    (k r : Fin q → ℕ) (y : SelectedVertices k → S) : ℝ :=
  if h : Nonempty (TypePreservingEmbeddings y x) then
    placementProbability M t ht x k r (Classical.choice h).val
  else 0

theorem selectedTypeProbability_eq (M : FiniteIrreducibleModel S)
    (t : ℝ) (ht : 0 ≤ t) {n q : ℕ} (x : Fin n → S)
    (k r : Fin q → ℕ) (y : SelectedVertices k → S)
    (f : TypePreservingEmbeddings y x) :
    selectedTypeProbability M t ht x k r y =
      placementProbability M t ht x k r f.val := by
  have h : Nonempty (TypePreservingEmbeddings y x) := ⟨f⟩
  rw [selectedTypeProbability, dif_pos h]
  apply placementProbability_eq_of_selectedTypes
  intro v
  exact ((Classical.choice h).property v).trans (f.property v).symm

theorem selectedTypeProbability_eq_zero_of_not_realizable
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ)
    (y : SelectedVertices k → S)
    (h : ¬Nonempty (TypePreservingEmbeddings y x)) :
    selectedTypeProbability M t ht x k r y = 0 := by
  rw [selectedTypeProbability, dif_neg h]

/-- The exact selected-type regrouping with the actual depletion factor,
proved by genuine placement cardinalities and actual graph-law invariance. -/
theorem sum_placement_probabilities_by_selectedTypes
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ) :
    (∑ f : Placements n k, placementProbability M t ht x k r f) =
      ∑ y : SelectedVertices k → S,
        (∏ a : S, ((fiberCount x a).descFactorial (fiberCount y a) : ℝ)) *
          selectedTypeProbability M t ht x k r y := by
  calc
    _ = ∑ f : Placements n k,
        selectedTypeProbability M t ht x k r (fun v ↦ x (f v)) := by
      apply Finset.sum_congr rfl
      intro f _
      exact (selectedTypeProbability_eq M t ht x k r
        (fun v ↦ x (f v)) ⟨f, fun _ ↦ rfl⟩).symm
    _ = _ := by
      convert sum_embeddings_by_typePattern x
        (selectedTypeProbability M t ht x k r) using 1
      congr 1
      ext
      simp only [Finset.mem_univ]

/-- Exact deterministic finite factorial formula for arbitrary actual
assignments, including every integer count vector and impossible profiles. -/
theorem factorial_expectation_by_selectedTypes
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ) :
    (∫ G, (count G k r : ℝ) ∂law M t ht x) =
      (∑ y : SelectedVertices k → S,
        (∏ a : S, ((fiberCount x a).descFactorial (fiberCount y a) : ℝ)) *
          selectedTypeProbability M t ht x k r y) /
        (∏ i, ((k i).factorial : ℝ)) := by
  rw [expectation_eq_div_sum_placement_probabilities,
    sum_placement_probabilities_by_selectedTypes]

/-- For any realization of a selected vector, its probability is the
literal finite prescribed-edge odds sum. Connectivity, isolation, size,
and surplus are tested on the actual padded graph pattern. -/
theorem selectedTypeProbability_eq_patternOdds
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (y : SelectedVertices k → S)
    (f : TypePreservingEmbeddings y x) :
    selectedTypeProbability M t ht x k r y =
      ∑ c : prescribedEdges (selectedUnion (blocksOfPlacement hk f.val)) → Bool,
        Real.exp (-(∑ e ∈ prescribedEdges
          (selectedUnion (blocksOfPlacement hk f.val)), hazard M t x e)) *
          (∏ e ∈ prescribedEdges (selectedUnion (blocksOfPlacement hk f.val)),
            if IndependentEdges.extend
              (prescribedEdges (selectedUnion (blocksOfPlacement hk f.val))) c e
            then Real.exp (hazard M t x e) - 1 else 1) *
          (if ∀ i, MatchesBlock
            (toGraph (IndependentEdges.extend
              (prescribedEdges (selectedUnion (blocksOfPlacement hk f.val))) c))
            (blockOfPlacement f.val i) (k i) (r i) then (1 : ℝ) else 0) := by
  rw [selectedTypeProbability_eq M t ht x k r y f]
  exact FixedTypeGraph.block_probability_odds
    (hazard M t x) (hazard_nonneg M ht x) (blocksOfPlacement hk f.val) k r

/-- Arbitrary literal integer counts summing to n, not a particular
rounding algorithm, give the same exact type-depletion factorial formula. -/
theorem factorial_expectation_integerTypeVector
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (c : S → ℕ) (hc : ∑ a, c a = n) (k r : Fin q → ℕ) :
    (∫ G, (count G k r : ℝ)
      ∂law M t ht (IntegerTypeAssignment.typeVector c hc)) =
      (∑ y : SelectedVertices k → S,
        (∏ a : S, ((c a).descFactorial (fiberCount y a) : ℝ)) *
          selectedTypeProbability M t ht (IntegerTypeAssignment.typeVector c hc) k r y) /
        (∏ i, ((k i).factorial : ℝ)) := by
  rw [factorial_expectation_by_selectedTypes]
  simp_rw [fiberCount, IntegerTypeAssignment.typeVector_fiber_card]

end PerronWright.FiniteIrreducibleFixedTypeFactorialFormula

