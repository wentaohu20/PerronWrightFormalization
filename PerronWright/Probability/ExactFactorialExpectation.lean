import PerronWright.Probability.ComponentCounts

/-!
# Exact finite-size factorial expectation

This is a finite sum/integral identity under the actual compact BJR graph
law.  All unselected edges have been eliminated, leaving precisely the
isolation exponential and the present-edge odds.  No asymptotic estimate,
profile concentration assertion, or process-convergence interface is assumed.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ExactFactorialExpectation

open AnnealedGraph SelectedConfiguration ComponentBlocks ComponentCounts

/-- The selected union for an ordered tuple of candidate blocks. -/
def selectedUnion {n q : ℕ} (B : Fin q ↪ Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.biUnion B

theorem subset_selectedUnion {n q : ℕ} (B : Fin q ↪ Finset (Fin n)) (i : Fin q) :
    B i ⊆ selectedUnion B := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hv⟩

/-- A component-block event depends only on pairs touching its vertex block. -/
theorem matchesBlock_congr {n : ℕ} (G H : SimpleGraph (Fin n))
    (B : Finset (Fin n)) (k r : ℕ)
    (h : ∀ i j, i ∈ B ∨ j ∈ B → (G.Adj i j ↔ H.Adj i j)) :
    MatchesBlock G B k r ↔ MatchesBlock H B k r := by
  have hi : G.induce (B : Set (Fin n)) = H.induce (B : Set (Fin n)) := by
    apply SimpleGraph.ext
    funext i j
    exact propext (h i.val j.val (Or.inl i.property))
  have hs : Isolated G (B : Set (Fin n)) ↔ Isolated H (B : Set (Fin n)) := by
    constructor
    · intro hg i hi j hij
      exact hg i hi j ((h i j (Or.inl hi)).mpr hij)
    · intro hh i hi j hij
      exact hh i hi j ((h i j (Or.inl hi)).mp hij)
  have he : blockSurplus G B = blockSurplus H B := by
    unfold blockSurplus
    congr 2
    exact congrArg (fun K : SimpleGraph (B : Set (Fin n)) ↦ K.edgeFinset.card) hi
  simp only [MatchesBlock, hi, hs, he]

/-- Padding every unselected edge by absence preserves all selected
component-block tests. -/
theorem matchesTuple_local {n q : ℕ} (B : Fin q ↪ Finset (Fin n))
    (k r : Fin q → ℕ) (a : Assignment n) :
    (∀ i, MatchesBlock (toGraph a) (B i) (k i) (r i)) ↔
      ∀ i, MatchesBlock
        (toGraph (IndependentEdges.extend (prescribedEdges (selectedUnion B))
          (IndependentEdges.restrict (prescribedEdges (selectedUnion B)) a)))
        (B i) (k i) (r i) := by
  apply forall_congr'
  intro l
  apply matchesBlock_congr
  intro i j hB
  by_cases hij : i = j
  · simp [hij]
  · have hU : i ∈ selectedUnion B ∨ j ∈ selectedUnion B :=
      hB.imp (fun h ↦ subset_selectedUnion B l h)
        (fun h ↦ subset_selectedUnion B l h)
    have ha : Event (selectedUnion B) (toGraph a)
        (IndependentEdges.extend (prescribedEdges (selectedUnion B))
          (IndependentEdges.restrict (prescribedEdges (selectedUnion B)) a)) := by
      simpa only [Event, assignmentOfGraph_toGraph] using
        IndependentEdges.agreesOn_extend_restrict
          (prescribedEdges (selectedUnion B)) a
    exact (agrees_adj_iff ha i j hij hU).symm

/-- Valid distinct component blocks are automatically pairwise disjoint. -/
theorem matchesTuple_disjoint {n q : ℕ} (G : SimpleGraph (Fin n))
    (B : Fin q ↪ Finset (Fin n)) (k r : Fin q → ℕ)
    (hB : ∀ i, MatchesBlock G (B i) (k i) (r i)) :
    Pairwise (fun i j ↦ Disjoint (B i) (B j)) := by
  intro i j hij
  obtain ⟨C, hC⟩ := (connected_isolated_iff_component G (B i : Set (Fin n))).mp
    ⟨(hB i).1, (hB i).2.1⟩
  obtain ⟨D, hD⟩ := (connected_isolated_iff_component G (B j : Set (Fin n))).mp
    ⟨(hB j).1, (hB j).2.1⟩
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have hvC : v ∈ C.supp := by rw [hC]; exact hv
  have hvD : v ∈ D.supp := by rw [hD]; exact hw
  have hCD : C = D := SimpleGraph.ConnectedComponent.eq_of_common_vertex hvC hvD
  have hs : (B i : Set (Fin n)) = (B j : Set (Fin n)) :=
    hC.symm.trans ((congrArg SimpleGraph.ConnectedComponent.supp hCD).trans hD)
  exact hij (B.injective (Finset.coe_injective hs))

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Exact probability that a fixed ordered tuple of candidate blocks has
the prescribed component sizes and surpluses. -/
theorem block_probability_odds (M : CompactBJRModel S)
    (t : ℝ) (ht : 0 ≤ t) (n q : ℕ)
    (B : Fin q ↪ Finset (Fin n)) (k r : Fin q → ℕ) :
    (∫ G, if ∀ i, MatchesBlock G (B i) (k i) (r i) then (1 : ℝ) else 0
      ∂AnnealedGraph.law M t ht n) =
      ∫ x : Fin n → S,
        ∑ c : prescribedEdges (selectedUnion B) → Bool,
          Real.exp (-(∑ e ∈ prescribedEdges (selectedUnion B), hazard M t x e)) *
            (∏ e ∈ prescribedEdges (selectedUnion B),
              if IndependentEdges.extend (prescribedEdges (selectedUnion B)) c e
              then Real.exp (hazard M t x e) - 1 else 1) *
            (if ∀ i, MatchesBlock
              (toGraph (IndependentEdges.extend (prescribedEdges (selectedUnion B)) c))
              (B i) (k i) (r i) then (1 : ℝ) else 0)
        ∂typeLaw M n := by
  let F : Assignment n → ℝ := fun a ↦
    if ∀ i, MatchesBlock (toGraph a) (B i) (k i) (r i) then 1 else 0
  have hF : ∀ a, F a = F (IndependentEdges.extend
      (prescribedEdges (selectedUnion B))
      (IndependentEdges.restrict (prescribedEdges (selectedUnion B)) a)) := by
    intro a
    exact if_congr (matchesTuple_local B k r a) rfl rfl
  calc
    _ = ∫ a, F a ∂(AnnealedGraph.pmf M t ht n).toMeasure := by
      rw [AnnealedGraph.law_expectation_eq_type_integral]
      exact (AnnealedGraph.expectation_eq_type_integral M t ht n
        (fun G ↦ if ∀ i, MatchesBlock G (B i) (k i) (r i) then 1 else 0)).symm
    _ = ∫ x : Fin n → S,
        ∑ c : prescribedEdges (selectedUnion B) → Bool,
          (∏ e ∈ prescribedEdges (selectedUnion B),
            IndependentEdges.edgeMass (hazard M t x e)
              (IndependentEdges.extend (prescribedEdges (selectedUnion B)) c e)) *
            F (IndependentEdges.extend (prescribedEdges (selectedUnion B)) c)
        ∂typeLaw M n := expectation_local_patterns M t ht n _ F hF
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply Finset.sum_congr rfl
      intro c _
      rw [IndependentEdges.prescribedMass_odds]

/-- Exact raw factorial expectation for the literal annealed compact BJR
graph.  The indicator selects precisely the isolated connected internal
configurations, and all irrelevant edges are already integrated out. -/
theorem factorial_expectation_exact (M : CompactBJRModel S)
    (t : ℝ) (ht : 0 ≤ t) (n q : ℕ) (k r : Fin q → ℕ) :
    (∫ G, (count G k r : ℝ) ∂AnnealedGraph.law M t ht n) =
      ∑ B : Fin q ↪ Finset (Fin n),
        ∫ x : Fin n → S,
          ∑ c : prescribedEdges (selectedUnion B) → Bool,
            Real.exp (-(∑ e ∈ prescribedEdges (selectedUnion B), hazard M t x e)) *
              (∏ e ∈ prescribedEdges (selectedUnion B),
                if IndependentEdges.extend (prescribedEdges (selectedUnion B)) c e
                then Real.exp (hazard M t x e) - 1 else 1) *
              (if ∀ i, MatchesBlock
                (toGraph (IndependentEdges.extend (prescribedEdges (selectedUnion B)) c))
                (B i) (k i) (r i) then (1 : ℝ) else 0)
          ∂typeLaw M n := by
  rw [expectation_eq_sum_block_probabilities M t ht n q k r]
  apply Finset.sum_congr rfl
  intro B _
  exact block_probability_odds M t ht n q B k r

end PerronWright.ExactFactorialExpectation
