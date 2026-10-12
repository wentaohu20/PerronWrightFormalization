import PerronWright.Probability.FiniteIrreducibleFixedTypeFactorialFormula
import PerronWright.Probability.FiniteIrreducibleSelectedIsolationExponent
import PerronWright.Probability.AnnealedTupleResidualConnectedLawWeights

/-!
# Literal deterministic finite typed factorial isolation formula

The exact falling-factorial selection factor and the exact count-based
isolation exponent are combined with a genuine finite edge-pattern odds
enumerator. No target-law substitution or asymptotic interface is used.
The remaining separate combinatorial step is to identify the valid-pattern
odds enumerator with a product of profilewise connected-graph sums.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleTypedFactorialIsolationFormula

open AnnealedGraph ComponentCounts ExactFactorialExpectation SelectedConfiguration
open AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
open AnnealedTupleResidualConnectedLawWeights
open FiniteIrreducibleTypedGraphLaw FiniteIrreducibleTypePlacementMultiplicity
open FiniteIrreducibleFixedTypeExchangeability FiniteIrreducibleFixedTypeFactorialFormula
open FiniteIrreducibleSelectedIsolationExponent

variable {S : Type*} [Fintype S] [DecidableEq S]

omit [Fintype S] [DecidableEq S] in
/-- The selected union of any realizing placement has precisely the
prescribed selected type counts, by an actual labelled-vertex bijection. -/
theorem selectedCount_placed_eq {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (x : Fin n → S) (y : SelectedVertices k → S)
    (f : TypePreservingEmbeddings y x) (a : S) :
    selectedCount x (selectedUnion (blocksOfPlacement hk f.val)) a = fiberCount y a := by
  let e := selectedVerticesEquiv hk f.val
  let E := e.subtypeEquiv (p := fun v ↦ y v = a)
    (q := fun w ↦ x w.val = a) (fun v ↦ by
      change y v = a ↔ x (f.val v) = a
      rw [f.property v])
  exact (Fintype.card_congr E).symm

/-- The full count-based isolation budget as a function of the actual
ambient assignment and prescribed selected type vector. -/
def typedIsolationBudget (M : FiniteIrreducibleModel S)
    {n q : ℕ} (x : Fin n → S) {k : Fin q → ℕ} (y : SelectedVertices k → S) : ℝ :=
  (∑ a : S, ∑ b : S, (fiberCount y a : ℝ) * M.kernel a b * (fiberCount x b : ℝ)) -
    (∑ a : S, ∑ b : S, (fiberCount y a : ℝ) * M.kernel a b * (fiberCount y b : ℝ)) / 2 -
    (∑ a : S, (fiberCount y a : ℝ) * M.kernel a a) / 2

theorem isolationBudget_placed_eq (M : FiniteIrreducibleModel S)
    {n q : ℕ} (x : Fin n → S) {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (y : SelectedVertices k → S)
    (f : TypePreservingEmbeddings y x) :
    isolationBudget M x (selectedUnion (blocksOfPlacement hk f.val)) =
      typedIsolationBudget M x y := by
  unfold isolationBudget exposureBudget selectedQuadratic selectedDiagonal typedIsolationBudget
  simp_rw [selectedCount_placed_eq hk x y f]

/-- Genuine valid-pattern finite odds sum on a realizing placement.
Its component tests force every boundary and intercomponent edge absent. -/
def placementPatternOdds (M : FiniteIrreducibleModel S) (t : ℝ)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) : ℝ :=
  ∑ c : prescribedEdges (selectedUnion (blocksOfPlacement hk f)) → Bool,
    (∏ e ∈ prescribedEdges (selectedUnion (blocksOfPlacement hk f)),
      if IndependentEdges.extend
        (prescribedEdges (selectedUnion (blocksOfPlacement hk f))) c e
      then Real.exp (hazard M t x e) - 1 else 1) *
    (if ∀ i, MatchesBlock
      (toGraph (IndependentEdges.extend
        (prescribedEdges (selectedUnion (blocksOfPlacement hk f))) c))
      (blockOfPlacement f i) (k i) (r i) then (1 : ℝ) else 0)

theorem selectedTypeProbability_eq_exp_mul_patternOdds
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (y : SelectedVertices k → S)
    (f : TypePreservingEmbeddings y x) :
    selectedTypeProbability M t ht x k r y =
      Real.exp (-(t / (n : ℝ) * typedIsolationBudget M x y)) *
        placementPatternOdds M t x k r hk f.val := by
  rw [selectedTypeProbability_eq_patternOdds M t ht x k r hk y f]
  simp_rw [sum_prescribed_hazard_eq, isolationBudget_placed_eq M x hk y f]
  unfold placementPatternOdds
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Type-preserving placement invariance of the actual valid-pattern odds
enumerator, obtained by cancelling the strictly positive literal isolation factor. -/
theorem placementPatternOdds_eq_of_same_selectedTypes
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (y : SelectedVertices k → S)
    (f g : TypePreservingEmbeddings y x) :
    placementPatternOdds M t x k r hk f.val =
      placementPatternOdds M t x k r hk g.val := by
  apply mul_left_cancel₀ (Real.exp_ne_zero (-(t / (n : ℝ) * typedIsolationBudget M x y)))
  exact (selectedTypeProbability_eq_exp_mul_patternOdds M t ht x k r hk y f).symm.trans
    (selectedTypeProbability_eq_exp_mul_patternOdds M t ht x k r hk y g)

/-- Actual selected-type finite pattern odds; well-defined by the proved
placement invariance, and zero on unrealizable selected type vectors. -/
def selectedTypePatternOdds (M : FiniteIrreducibleModel S) (t : ℝ)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (y : SelectedVertices k → S) : ℝ :=
  if h : Nonempty (TypePreservingEmbeddings y x) then
    placementPatternOdds M t x k r hk (Classical.choice h).val
  else 0

theorem selectedTypePatternOdds_eq (M : FiniteIrreducibleModel S)
    (t : ℝ) (ht : 0 ≤ t) {n q : ℕ} (x : Fin n → S)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (y : SelectedVertices k → S) (f : TypePreservingEmbeddings y x) :
    selectedTypePatternOdds M t x k r hk y =
      placementPatternOdds M t x k r hk f.val := by
  have h : Nonempty (TypePreservingEmbeddings y x) := ⟨f⟩
  rw [selectedTypePatternOdds, dif_pos h]
  exact placementPatternOdds_eq_of_same_selectedTypes M t ht x k r hk y
    (Classical.choice h) f

theorem selectedTypeProbability_eq_exp_mul_selectedTypePatternOdds
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (y : SelectedVertices k → S) :
    selectedTypeProbability M t ht x k r y =
      Real.exp (-(t / (n : ℝ) * typedIsolationBudget M x y)) *
        selectedTypePatternOdds M t x k r hk y := by
  by_cases h : Nonempty (TypePreservingEmbeddings y x)
  · rw [selectedTypePatternOdds, dif_pos h]
    exact selectedTypeProbability_eq_exp_mul_patternOdds M t ht x k r hk y
      (Classical.choice h)
  · rw [selectedTypeProbability, selectedTypePatternOdds, dif_neg h, dif_neg h, mul_zero]

/-- Exact factorial expectation for arbitrary deterministic finite types:
true falling-factorial depletion, true B_n isolation, and true finite odds
pattern enumerator. No approximation or regular-critical hypothesis. -/
theorem factorial_expectation_isolation_formula
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    (∫ G, (count G k r : ℝ) ∂law M t ht x) =
      (∑ y : SelectedVertices k → S,
        (∏ a : S, ((fiberCount x a).descFactorial (fiberCount y a) : ℝ)) *
          Real.exp (-(t / (n : ℝ) * typedIsolationBudget M x y)) *
            selectedTypePatternOdds M t x k r hk y) /
        (∏ i, ((k i).factorial : ℝ)) := by
  rw [factorial_expectation_by_selectedTypes]
  simp_rw [selectedTypeProbability_eq_exp_mul_selectedTypePatternOdds M t ht x k r hk,
    mul_assoc]

/-- The same exact formula for every actual assignment realizing any
prescribed integer counts. In particular it is not restricted to a
chosen rounding construction or a chosen ordering of the ambient types. -/
theorem factorial_expectation_isolation_formula_of_fiberCounts
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (c : S → ℕ)
    (hc : ∀ a, fiberCount x a = c a)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    (∫ G, (count G k r : ℝ) ∂law M t ht x) =
      (∑ y : SelectedVertices k → S,
        (∏ a : S, ((c a).descFactorial (fiberCount y a) : ℝ)) *
          Real.exp (-(t / (n : ℝ) *
            ((∑ a : S, ∑ b : S,
                (fiberCount y a : ℝ) * M.kernel a b * (c b : ℝ)) -
              (∑ a : S, ∑ b : S,
                (fiberCount y a : ℝ) * M.kernel a b * (fiberCount y b : ℝ)) / 2 -
              (∑ a : S, (fiberCount y a : ℝ) * M.kernel a a) / 2))) *
            selectedTypePatternOdds M t x k r hk y) /
        (∏ i, ((k i).factorial : ℝ)) := by
  rw [factorial_expectation_isolation_formula M t ht x k r hk]
  simp_rw [typedIsolationBudget, hc]

end PerronWright.FiniteIrreducibleTypedFactorialIsolationFormula

