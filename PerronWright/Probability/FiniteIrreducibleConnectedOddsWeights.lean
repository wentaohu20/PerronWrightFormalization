import PerronWright.Probability.FiniteIrreducibleGraphPatternProducts
import PerronWright.Probability.FiniteIrreducibleTypedFactorialIsolationFormula

/-!
# Literal connected weighted graph odds enumerators

The denominator of every edge odds factor is the ambient population n,
not the component size. The actual valid-pattern odds sum is proved to
be the product of genuine labelled connected-graph odds enumerators.
-/

open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleConnectedOddsWeights

open AnnealedGraph ComponentCounts ExactFactorialExpectation SelectedConfiguration
open AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
open AnnealedTupleResidualConnectedLawGraphTuple AnnealedTupleResidualConnectedLawWeights
open FiniteIrreducibleTypedGraphLaw FiniteIrreducibleTypePlacementMultiplicity
open FiniteIrreducibleTypedFactorialIsolationFormula FiniteIrreducibleGraphPatternProducts

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact edge odds for labelled component types, with the actual ambient
population denominator n retained. -/
def edgeOdds (M : FiniteIrreducibleModel S) (t : ℝ) (n : ℕ)
    {k : ℕ} (y : Fin k → S) (e : Sym2 (Fin k)) : ℝ :=
  Real.exp (t * pairKernel M y e / (n : ℝ)) - 1

@[simp] theorem edgeOdds_mk (M : FiniteIrreducibleModel S) (t : ℝ) (n : ℕ)
    {k : ℕ} (y : Fin k → S) (i j : Fin k) :
    edgeOdds M t n y s(i,j) =
      Real.exp (t * M.kernel (y i) (y j) / (n : ℝ)) - 1 := rfl

theorem edgeOdds_nonneg (M : FiniteIrreducibleModel S) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) {k : ℕ} (y : Fin k → S) (e : Sym2 (Fin k)) :
    0 ≤ edgeOdds M t n y e := by
  exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr
    (div_nonneg (mul_nonneg ht (pairKernel_nonneg M y e)) (Nat.cast_nonneg n)))

/-- The true simple-graph edge odds product on fixed labelled types. -/
def graphOddsWeight (M : FiniteIrreducibleModel S) (t : ℝ) (n : ℕ)
    {k : ℕ} (y : Fin k → S) (H : SimpleGraph (Fin k)) : ℝ :=
  ∏ e ∈ H.edgeFinset, edgeOdds M t n y e

theorem graphOddsWeight_nonneg (M : FiniteIrreducibleModel S) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) {k : ℕ} (y : Fin k → S) (H : SimpleGraph (Fin k)) :
    0 ≤ graphOddsWeight M t n y H :=
  Finset.prod_nonneg (fun e _ ↦ edgeOdds_nonneg M ht n y e)

/-- Literal CW_{n,kappa} for a fixed labelled type vector and natural surplus.
Every eligible graph is genuinely connected and has k+r-1 actual edges. -/
def connectedOddsWeight (M : FiniteIrreducibleModel S) (t : ℝ) (n : ℕ)
    {k : ℕ} (y : Fin k → S) (r : ℕ) : ℝ :=
  ∑ H : SimpleGraph (Fin k), if ConnectedTypeLaw.Eligible r H then
    graphOddsWeight M t n y H else 0

theorem connectedOddsWeight_nonneg (M : FiniteIrreducibleModel S) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) {k : ℕ} (y : Fin k → S) (r : ℕ) :
    0 ≤ connectedOddsWeight M t n y r := by
  apply Finset.sum_nonneg
  intro H _
  split_ifs
  · exact graphOddsWeight_nonneg M ht n y H
  · exact le_rfl

theorem edgeOdds_placedPair (M : FiniteIrreducibleModel S)
    (t : ℝ) {n q : ℕ} {k : Fin q → ℕ} (x : Fin n → S)
    (y : SelectedVertices k → S) (f : TypePreservingEmbeddings y x)
    (i : Fin q) (e : Sym2 (Fin (k i))) :
    edgeOdds M t n x (placedPair f.val ⟨i,e⟩) =
      edgeOdds M t n (fun a ↦ y ⟨i,a⟩) e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    change Real.exp (t * M.kernel (x (f.val ⟨i,a⟩)) (x (f.val ⟨i,b⟩)) / (n : ℝ)) - 1 = _
    rw [f.property ⟨i,a⟩, f.property ⟨i,b⟩]
    rfl

theorem placementPatternOdds_eq_graphTupleSum
    (M : FiniteIrreducibleModel S) (t : ℝ) {n q : ℕ}
    (x : Fin n → S) (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (f : Placements n k) :
    placementPatternOdds M t x k r hk f =
      ∑ H : GraphTuple k, if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i) then
        graphOddsWeight M t n x (tupleGraph f H) else 0 :=
  valid_pattern_edge_sum_eq_graphTuple_sum hk f r (edgeOdds M t n x)

/-- Actual finite valid-pattern odds are a product of genuine connected
graph enumerators on the actual selected component type vectors. -/
theorem placementPatternOdds_eq_product_connectedOddsWeight
    (M : FiniteIrreducibleModel S) (t : ℝ) {n q : ℕ}
    (x : Fin n → S) (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (y : SelectedVertices k → S) (f : TypePreservingEmbeddings y x) :
    placementPatternOdds M t x k r hk f.val =
      ∏ i, connectedOddsWeight M t n (fun a ↦ y ⟨i,a⟩) (r i) := by
  rw [placementPatternOdds_eq_graphTupleSum]
  calc
    _ = ∑ H : GraphTuple k, if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i) then
        (∏ i, graphOddsWeight M t n (fun a ↦ y ⟨i,a⟩) (H i)) else 0 := by
      apply Finset.sum_congr rfl
      intro H _
      split_ifs
      · unfold graphOddsWeight
        rw [prod_tupleGraph_edges]
        apply Finset.prod_congr rfl
        intro i _
        apply Finset.prod_congr rfl
        intro e _
        exact edgeOdds_placedPair M t x y f i e
      · rfl
    _ = _ := sum_eligibleGraphTuples_eq_prod_sums k r
      (fun i H ↦ graphOddsWeight M t n (fun a ↦ y ⟨i,a⟩) H)

theorem selectedTypePatternOdds_eq_product_connectedOddsWeight
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t)
    {n q : ℕ} (x : Fin n → S) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (y : SelectedVertices k → S)
    (f : TypePreservingEmbeddings y x) :
    selectedTypePatternOdds M t x k r hk y =
      ∏ i, connectedOddsWeight M t n (fun a ↦ y ⟨i,a⟩) (r i) := by
  rw [selectedTypePatternOdds_eq M t ht x k r hk y f]
  exact placementPatternOdds_eq_product_connectedOddsWeight M t x k r hk y f

omit [DecidableEq S] in
/-- An unrealizable type vector has exactly zero falling-factorial
selection multiplicity, including when one or more counts are depleted. -/
theorem selectionFactor_eq_zero_of_not_realizable
    {A B : Type*} [Fintype A] [Fintype B] (y : A → S) (x : B → S)
    (h : ¬Nonempty (TypePreservingEmbeddings y x)) :
    (∏ a : S, ((fiberCount x a).descFactorial (fiberCount y a) : ℝ)) = 0 := by
  have : IsEmpty (TypePreservingEmbeddings y x) := not_nonempty_iff.mp h
  rw [← Nat.cast_prod, ← card_typePreservingEmbeddings]
  simp only [Fintype.card_eq_zero, Nat.cast_zero]

end PerronWright.FiniteIrreducibleConnectedOddsWeights

