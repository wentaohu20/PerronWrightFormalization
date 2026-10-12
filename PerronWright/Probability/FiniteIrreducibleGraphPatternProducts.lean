import PerronWright.Probability.AnnealedTupleResidualConnectedLawWeights
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Literal finite graph-pattern product identities

The active prescribed Boolean coordinates are exactly the genuine edge
set of the padded graph. Valid patterns are then reindexed by the proved
labelled connected-graph tuple equivalence, and their products separate.
These are purely finite combinatorial identities.
-/

open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleGraphPatternProducts

open AnnealedGraph ComponentCounts ExactFactorialExpectation SelectedConfiguration
open AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
open AnnealedTupleResidualConnectedLawGraphTuple
open AnnealedTupleResidualConnectedLawWeights

/-- Active prescribed coordinates and actual padded graph edges are in
bijection. No absent edge contributes a weight. -/
theorem presence_product_eq_patternGraph_edges
    {n q : ℕ} (B : Fin q ↪ Finset (Fin n))
    (c : prescribedEdges (selectedUnion B) → Bool)
    {R : Type*} [CommMonoid R] (W : Sym2 (Fin n) → R) :
    (∏ e ∈ prescribedEdges (selectedUnion B),
      if IndependentEdges.extend (prescribedEdges (selectedUnion B)) c e
      then W e.val else 1) =
      ∏ e ∈ (patternGraph B c).edgeFinset, W e := by
  let D := prescribedEdges (selectedUnion B)
  let G := patternGraph B c
  calc
    _ = ∏ e ∈ D.filter
        (fun e ↦ IndependentEdges.extend D c e = true), W e.val := by
      rw [Finset.prod_filter]
    _ = _ := by
      apply Finset.prod_bij (fun e _ ↦ e.val)
      · intro e he
        have ht := (Finset.mem_filter.mp he).2
        exact SimpleGraph.mem_edgeFinset.mpr ((mem_toGraph_edgeSet _ e).mpr ht)
      · intro e _ e' _ heq
        exact Subtype.ext heq
      · intro e he
        let ee : Edge n := ⟨e, G.not_isDiag_of_mem_edgeFinset he⟩
        have ht : IndependentEdges.extend D c ee = true :=
          (mem_toGraph_edgeSet _ ee).mp (SimpleGraph.mem_edgeFinset.mp he)
        have hd : ee ∈ D := by
          by_contra hnot
          simp only [IndependentEdges.extend, dif_neg hnot] at ht
          contradiction
        exact ⟨ee, Finset.mem_filter.mpr ⟨hd, ht⟩, rfl⟩
      · intro e _
        rfl

/-- Every actual valid-pattern weighted edge sum is exactly the sum
over the corresponding eligible labelled connected-graph tuples. -/
theorem valid_pattern_edge_sum_eq_graphTuple_sum
    {n q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i)
    (f : Placements n k) (r : Fin q → ℕ) (W : Sym2 (Fin n) → ℝ) :
    (∑ c : prescribedEdges (selectedUnion (blocksOfPlacement hk f)) → Bool,
      (∏ e ∈ prescribedEdges (selectedUnion (blocksOfPlacement hk f)),
        if IndependentEdges.extend
          (prescribedEdges (selectedUnion (blocksOfPlacement hk f))) c e
        then W e.val else 1) *
      (if ∀ i, MatchesBlock (patternGraph (blocksOfPlacement hk f) c)
        (blockOfPlacement f i) (k i) (r i) then (1 : ℝ) else 0)) =
      ∑ H : GraphTuple k, if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i) then
        (∏ e ∈ (tupleGraph f H).edgeFinset, W e) else 0 := by
  calc
    _ = ∑ c : prescribedEdges (selectedUnion (blocksOfPlacement hk f)) → Bool,
        if ∀ i, MatchesBlock (patternGraph (blocksOfPlacement hk f) c)
          (blockOfPlacement f i) (k i) (r i) then
            (∏ e ∈ (patternGraph (blocksOfPlacement hk f) c).edgeFinset, W e)
        else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [presence_product_eq_patternGraph_edges]
      split_ifs <;> simp only [mul_one, mul_zero]
    _ = _ := sum_valid_patterns_eq_sum_eligible_graphTuples hk f r
      (fun G ↦ ∏ e ∈ G.edgeFinset, W e)

theorem prod_eligible_weights {q : ℕ} (k r : Fin q → ℕ)
    (H : GraphTuple k) (W : (i : Fin q) → SimpleGraph (Fin (k i)) → ℝ) :
    (∏ i, if ConnectedTypeLaw.Eligible (r i) (H i) then W i (H i) else 0) =
      if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i) then ∏ i, W i (H i) else 0 := by
  by_cases h : ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    rw [if_pos (h i)]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [if_neg hi]

/-- Genuine finite graph-tuple sums factor into their own connected
weighted graph sums; no independence premise or analytic assumption. -/
theorem sum_eligibleGraphTuples_eq_prod_sums {q : ℕ}
    (k r : Fin q → ℕ) (W : (i : Fin q) → SimpleGraph (Fin (k i)) → ℝ) :
    (∑ H : GraphTuple k, if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)
      then ∏ i, W i (H i) else 0) =
      ∏ i, ∑ H : SimpleGraph (Fin (k i)),
        if ConnectedTypeLaw.Eligible (r i) H then W i H else 0 := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro H _
  exact (prod_eligible_weights k r H W).symm

end PerronWright.FiniteIrreducibleGraphPatternProducts

