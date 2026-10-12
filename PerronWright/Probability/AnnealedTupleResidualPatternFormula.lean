import PerronWright.Probability.AnnealedTupleResidualExchangeability
import PerronWright.Probability.AnnealedResidualFixedBlock

/-!
# Exact ordered-tuple annealed selected-type formula

This combines the genuine component count, the proved placement multiplicity
and exchangeability, exact local-pattern elimination, and the literal fresh
type integral.  Only the selected internal patterns that give the requested
isolated connected component blocks contribute.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedTupleResidualPatternFormula

open AnnealedGraph ComponentBlocks ComponentCounts SelectedConfiguration
open ExactFactorialExpectation AnnealedTupleResidualCounting
open AnnealedTupleResidualExchangeability AnnealedResidualFixedBlock FreshTypeAveraging

theorem isolated_selectedUnion {n q : ℕ} (H : SimpleGraph (Fin n))
    (B : Fin q ↪ Finset (Fin n)) (k r : Fin q → ℕ)
    (hB : ∀ i, MatchesBlock H (B i) (k i) (r i)) :
    Isolated H (selectedUnion B : Set (Fin n)) := by
  intro u hu v huv
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hu
  have hv : v ∈ B i := (hB i).2.1 u hi v huv
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩

/-- Pad a local edge pattern by absent edges, as in the exact factorial formula. -/
def patternGraph {n q : ℕ} (B : Fin q ↪ Finset (Fin n))
    (c : prescribedEdges (selectedUnion B) → Bool) : SimpleGraph (Fin n) :=
  toGraph (IndependentEdges.extend (prescribedEdges (selectedUnion B)) c)

/-- The component-tuple indicator is the sum of the unique consistent local
edge-pattern indicator.  This is a finite partition of the actual event. -/
theorem tuple_indicator_eq_sum_pattern_indicators {n q : ℕ}
    (B : Fin q ↪ Finset (Fin n)) (k r : Fin q → ℕ) (a : Assignment n) :
    (if ∀ i, MatchesBlock (toGraph a) (B i) (k i) (r i) then (1 : ℝ) else 0) =
      ∑ c : prescribedEdges (selectedUnion B) → Bool,
        if ∀ i, MatchesBlock (patternGraph B c) (B i) (k i) (r i) then
          (if Event (selectedUnion B) (patternGraph B c) a then (1 : ℝ) else 0)
        else 0 := by
  let c₀ := IndependentEdges.restrict (prescribedEdges (selectedUnion B)) a
  rw [Fintype.sum_eq_single c₀]
  · have he : Event (selectedUnion B) (patternGraph B c₀) a := by
      change IndependentEdges.AgreesOn (prescribedEdges (selectedUnion B))
        (assignmentOfGraph (toGraph (IndependentEdges.extend (prescribedEdges (selectedUnion B)) c₀))) a
      rw [assignmentOfGraph_toGraph]
      exact (IndependentEdges.agreesOn_extend_iff _ c₀ a).mpr rfl
    rw [if_pos he]
    exact if_congr (matchesTuple_local B k r a) rfl rfl
  · intro c hc
    have he : ¬Event (selectedUnion B) (patternGraph B c) a := by
      intro he
      change IndependentEdges.AgreesOn (prescribedEdges (selectedUnion B))
        (assignmentOfGraph (toGraph (IndependentEdges.extend (prescribedEdges (selectedUnion B)) c))) a at he
      rw [assignmentOfGraph_toGraph] at he
      exact hc ((IndependentEdges.agreesOn_extend_iff _ c a).mp he).symm
    rw [if_neg he]
    split_ifs <;> rfl

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The actual fixed ordered-block event is the sum of actual probabilities
of its valid prescribed configurations. -/
theorem block_probability_eq_sum_pattern_probabilities {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t)
    (B : Fin q ↪ Finset (Fin n)) (k r : Fin q → ℕ) :
    (∫ G, if ∀ i, MatchesBlock G (B i) (k i) (r i) then (1 : ℝ) else 0
      ∂AnnealedGraph.law M t ht n) =
      ∑ c : prescribedEdges (selectedUnion B) → Bool,
        if ∀ i, MatchesBlock (patternGraph B c) (B i) (k i) (r i) then
          (∫ a : Assignment n,
            if Event (selectedUnion B) (patternGraph B c) a then (1 : ℝ) else 0
            ∂(AnnealedGraph.pmf M t ht n).toMeasure)
        else 0 := by
  rw [lawIntegral_eq_assignmentIntegral]
  simp_rw [tuple_indicator_eq_sum_pattern_indicators B k r]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro c _
    by_cases hc : ∀ i, MatchesBlock (patternGraph B c) (B i) (k i) (r i)
    · simp only [if_pos hc]
    · simp only [if_neg hc,integral_zero]
  · intro c _
    exact Integrable.of_finite

/-- Exact selected-type integral for a fixed ordered tuple of blocks.
Fresh sampled types are integrated away, not replaced by a deterministic profile. -/
theorem block_probability_selected_type_formula {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t)
    (B : Fin q ↪ Finset (Fin n)) (k r : Fin q → ℕ) (s₀ : S) :
    (∫ G, if ∀ i, MatchesBlock G (B i) (k i) (r i) then (1 : ℝ) else 0
      ∂AnnealedGraph.law M t ht n) =
      ∑ c : prescribedEdges (selectedUnion B) → Bool,
        if ∀ i, MatchesBlock (patternGraph B c) (B i) (k i) (r i) then
          (∫ u : {i : Fin n // i ∈ selectedUnion B} → S,
            Real.exp (-t * internalPairWeightOn M (selectedUnion B) u s₀ / (n : ℝ)) *
              isolationFactor M t n u ^ (n-(selectedUnion B).card) *
              internalOddsProduct M t (selectedUnion B) (patternGraph B c) u s₀
            ∂Measure.pi (fun _ ↦ M.mu))
        else 0 := by
  rw [block_probability_eq_sum_pattern_probabilities]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : ∀ i, MatchesBlock (patternGraph B c) (B i) (k i) (r i)
  · simp only [if_pos hc]
    exact probability_event_averaged_odds M t ht (selectedUnion B) (patternGraph B c)
      (isolated_selectedUnion _ B k r hc) s₀
  · simp only [if_neg hc]

/-- Positive component sizes make the placed disjoint blocks an injective
ordered tuple even before a graph configuration has been specified. -/
def blocksOfPlacement {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) : Fin q ↪ Finset (Fin n) where
  toFun := blockOfPlacement f
  inj' := by
    intro i j heq
    by_contra hij
    have hd := blockOfPlacement_pairwise f hij
    change Disjoint (blockOfPlacement f i) (blockOfPlacement f j) at hd
    rw [heq] at hd
    have hp : 0 < (blockOfPlacement f j).card := by rw [blockOfPlacement_card]; exact hk j
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hp
    exact (Finset.disjoint_left.mp hd) hv hv

theorem selectedUnion_blocksOfPlacement_card {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) :
    (selectedUnion (blocksOfPlacement hk f)).card = ∑ i, k i := by
  unfold selectedUnion
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact blockOfPlacement_card f i
  · intro i _ j _ hij
    exact blockOfPlacement_pairwise f hij

/-- A literal finite sum/integral over valid selected configurations.  Its
boundary pattern coordinates are forced absent by the component tests. -/
def selectedPatternSum {n q : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (B : Fin q ↪ Finset (Fin n)) (k r : Fin q → ℕ) (s₀ : S) : ℝ :=
  ∑ c : prescribedEdges (selectedUnion B) → Bool,
    if ∀ i, MatchesBlock (patternGraph B c) (B i) (k i) (r i) then
      (∫ u : {i : Fin n // i ∈ selectedUnion B} → S,
        Real.exp (-t * internalPairWeightOn M (selectedUnion B) u s₀ / (n : ℝ)) *
          isolationFactor M t n u ^ (n-(selectedUnion B).card) *
          internalOddsProduct M t (selectedUnion B) (patternGraph B c) u s₀
        ∂Measure.pi (fun _ ↦ M.mu))
    else 0

/-- The actual ordered-component factorial expectation equals the exact
selection factor times its selected-type/internal-pattern integral.  This
is proved from the genuine count and both literal type and graph laws. -/
theorem factorial_expectation_selected_pattern_formula {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) (f₀ : Placements n k) (s₀ : S) :
    (∫ G, (count G k r : ℝ) ∂AnnealedGraph.law M t ht n) =
      ((n.descFactorial (∑ i, k i) : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
        selectedPatternSum M t (blocksOfPlacement hk f₀) k r s₀ := by
  calc
    _ = ((n.descFactorial (∑ i, k i) : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
        ∫ G, if ∀ i, MatchesBlock G (blocksOfPlacement hk f₀ i) (k i) (r i)
          then (1 : ℝ) else 0 ∂AnnealedGraph.law M t ht n :=
      factorial_expectation_selection_factor M t ht k r f₀
    _ = _ := by
      rw [block_probability_selected_type_formula M t ht (blocksOfPlacement hk f₀) k r s₀]
      rfl

/-- The unused-type exponent in the preceding exact formula is exactly
`n - ∑ k_i`, because the placed selected blocks are genuinely disjoint. -/
theorem unused_size_blocksOfPlacement {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) :
    n - (selectedUnion (blocksOfPlacement hk f)).card = n - ∑ i, k i := by
  rw [selectedUnion_blocksOfPlacement_card]

end PerronWright.AnnealedTupleResidualPatternFormula
