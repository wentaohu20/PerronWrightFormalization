import PerronWright.Probability.AnnealedMarkedFactorialPattern

/-!
# Exact marked factorial expectation under genuine connected product laws

The mark test is carried through literal selected-pattern reindexing,
weighted finite-graph Fubini, the proved selected-type coordinate map,
and the exact ordinary/field connected-weight transformation.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedMarkedFactorialFormula

open AnnealedGraph SelectedConfiguration ComponentCounts ExactFactorialExpectation
  FreshTypeAveraging AnnealedResidualFixedBlock AnnealedTupleResidualCounting
  AnnealedTupleResidualPatternFormula AnnealedTupleResidualConnectedLawGraphTuple
  AnnealedTupleResidualConnectedLawWeights AnnealedTupleResidualConnectedLawCoordinates
  AnnealedTupleResidualConnectedLawProduct AnnealedTupleResidualConnectedLawFormula
  AnnealedMarkedFactorialCounting AnnealedMarkedFactorialExchangeability AnnealedMarkedFactorialPattern
  AnnealedMarkedResidualConcentration EmpiricalMarkConcentration

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def markedWeightedGraphTupleSum {n q : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) : ℝ :=
  ∑ H : GraphTuple k, if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i) then
    (∫ u : ↥(selectedUnion (blocksOfPlacement hk f)) → S,
      (∏ i, M.graphWeightIntegrand t (H i) (blockTypes hk f u i)) *
        selectedResidual M t hk f H u s₀ * Ψ (selectedMarks hk f u)
      ∂Measure.pi (fun _ ↦ M.mu)) else 0

theorem markedPatternSum_eq_weightedGraphTupleSum {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    markedPatternSum M t k r hk f s₀ Ψ = (n:ℝ)⁻¹^(∑ i,(k i+r i-1)) *
      markedWeightedGraphTupleSum M t k r hk f s₀ Ψ := by
  unfold markedPatternSum
  rw [sum_valid_patterns_eq_sum_eligible_graphTuples hk f r
    (fun H ↦ ∫ u : ↥(selectedUnion (blocksOfPlacement hk f)) → S,
      (Real.exp (-t * internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀/(n:ℝ)) *
        isolationFactor M t n u^(n-(selectedUnion (blocksOfPlacement hk f)).card) *
        internalOddsProduct M t (selectedUnion (blocksOfPlacement hk f)) H u s₀) *
          Ψ (selectedMarks hk f u) ∂Measure.pi (fun _ ↦ M.mu))]
  unfold markedWeightedGraphTupleSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  by_cases hH : ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)
  · simp only [if_pos hH]
    simp_rw [selected_integrand_weight_factorization M t hk f H,card_tupleGraph_eligible f H r hH]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    ring
  · simp only [if_neg hH,mul_zero]

theorem ordinaryWeightedMarkedResidual_continuous_slice {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hn : 0 < n) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) (H : GraphTuple k) :
    Continuous (fun x : (i : Fin q) → Fin (k i) → S ↦
      productOrdinaryWeight M t k r (tupleState x H) *
        (residualObservable M t hk f s₀ (tupleState x H) * Ψ (componentMarks hk (tupleState x H)))) := by
  have hc : Continuous (fun x : (i : Fin q) → Fin (k i) → S ↦ Ψ (componentMarks hk (tupleState x H))) :=
    hΨ.comp (continuous_pi (fun i ↦ (typesMark_continuous (hk i)).comp (continuous_apply i)))
  convert (ordinaryWeightedResidual_continuous_slice M t hn k r hk f s₀ H).mul hc using 1
  funext x
  simp only [Pi.mul_apply,mul_assoc]

theorem weightedMarkedBaseLaw_integral_eq_graphTupleSum {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hn : 0 < n) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    (∫ p, productOrdinaryWeight M t k r p *
      (residualObservable M t hk f s₀ p * Ψ (componentMarks hk p)) ∂baseLaw M k) =
        markedWeightedGraphTupleSum M t k r hk f s₀ Ψ := by
  rw [integral_baseLaw_eq_sum_graph_integrals M k _
    (fun H ↦ (ordinaryWeightedMarkedResidual_continuous_slice M t hn k r hk f s₀ Ψ hΨ H).measurable)
    (fun H ↦ (ordinaryWeightedMarkedResidual_continuous_slice M t hn k r hk f s₀ Ψ hΨ H).integrable_of_hasCompactSupport
      isClosed_closure.isCompact)]
  unfold markedWeightedGraphTupleSum
  apply Finset.sum_congr rfl
  intro H _
  simp_rw [productOrdinaryWeight_tupleState]
  by_cases hH : ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)
  · simp only [if_pos hH]
    have hm (x : (i : Fin q) → Fin (k i) → S) :
        componentMarks hk (tupleState x H) = selectedMarks hk f (selectedTypes hk f x) := by
      funext i
      change typesMark (hk i) (x i) = typesMark (hk i) (blockTypes hk f (selectedTypes hk f x) i)
      rw [blockTypes_selectedTypes]
    convert integral_selectedTypes M hk f
      (fun u ↦ (∏ i, M.graphWeightIntegrand t (H i) (blockTypes hk f u i)) *
        selectedResidual M t hk f H u s₀ * Ψ (selectedMarks hk f u)) using 1
    congr 1
    funext x
    simp only [residualObservable,tupleState,blockTypes_selectedTypes,mul_assoc]
    rw [← hm x]
  · simp only [if_neg hH,zero_mul,integral_zero]

/-- Exact marked selected-pattern expectation under the genuine product Q
law. The graph sum and all coordinate transformations are proved above. -/
theorem markedPatternSum_eq_connectedLaw_expectation {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t) (hn : 0 < n) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField t) (k i) (r i))
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    markedPatternSum M t k r hk f s₀ Ψ =
      (n:ℝ)⁻¹^(∑ i,(k i+r i-1)) * ordinaryNormalizer M t k r *
        ∫ p, residualObservable M t hk f s₀ p * Ψ (componentMarks hk p)
          ∂AnnealedTupleResidualConnectedLawProduct.law M (M.scalarField t) k r hC := by
  rw [markedPatternSum_eq_weightedGraphTupleSum,
    ← weightedMarkedBaseLaw_integral_eq_graphTupleSum M t hn k r hk f s₀ Ψ hΨ,
    ordinary_weighted_integral_eq_normalizer_mul_expectation M t ht k r hC]
  ring

/-- The genuine marked ordered distinct-component expectation has the
paper's exact selection factor, enumerator product, and actual residual
weighted product connected-law expectation. No formula is an input. -/
theorem markedFactorial_expectation_connectedLaw_residual_formula {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t) (hn : 0 < n) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField t) (k i) (r i))
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    (∫ p, markedCount p.1 (AnnealedTypedGraph.graph p) k r Ψ ∂AnnealedTypedGraph.law M t ht.le n) =
      ((n.descFactorial (∑ i,k i):ℝ)/(∏ i,((k i).factorial:ℝ))) *
        ((n:ℝ)⁻¹^(∑ i,(k i+r i-1))) * (∏ i,M.connectedWeight t (k i) (r i)) *
          ∫ p, residualObservable M t hk f s₀ p * Ψ (componentMarks hk p)
            ∂AnnealedTupleResidualConnectedLawProduct.law M (M.scalarField t) k r hC := by
  rw [markedExpectation_selection_factor M t ht.le k r hk f Ψ hΨ,
    placementExpectation_eq_markedPatternSum M t ht.le k r hk f s₀ Ψ hΨ,
    markedPatternSum_eq_connectedLaw_expectation M t ht hn k r hk f s₀ hC Ψ hΨ]
  unfold ordinaryNormalizer
  ring

end PerronWright.AnnealedMarkedFactorialFormula
