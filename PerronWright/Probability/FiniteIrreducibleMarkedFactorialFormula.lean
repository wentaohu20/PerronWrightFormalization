import PerronWright.Probability.AnnealedMarkedFactorialCounting
import PerronWright.Probability.FiniteIrreducibleDeterministicConnectedLawFormula

/-! # Exact deterministic finite marked factorial formula

The source counts genuine ordered distinct graph components, marked by
their actual empirical type probability measures. Exact type-preserving
placement multiplicities retain an arbitrary coupled mark test through
the literal connected-state residual formula.
-/

open MeasureTheory Filter
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleMarkedFactorialFormula

open ComponentCounts AnnealedTupleResidualCounting AnnealedMarkedFactorialCounting
open FiniteIrreducibleFixedTypeExchangeability FiniteIrreducibleFixedTypeFactorialFormula
open FiniteIrreducibleTypePlacementMultiplicity FiniteIrreducibleTypedFactorialIsolationFormula
open FiniteIrreducibleConnectedOddsFactorialFormula FiniteIrreducibleConnectedOddsWeights
open FiniteIrreducibleConnectedLawFiniteSum FiniteIrreducibleDeterministicResidualWeights
open FiniteIrreducibleGraphPatternProducts
open AnnealedTupleResidualConnectedLawGraphTuple AnnealedTupleResidualConnectedLawProduct
open AnnealedMarkedResidualConcentration (componentMarks)
open FiniteIrreducibleDeterministicConnectedLawFormula
open EmpiricalMarkConcentration (typesMark)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def selectedMarks {q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i)
    (y : SelectedVertices k → S) : Fin q → ProbabilityMeasure S :=
  fun i ↦ typesMark (hk i) (fun a ↦ y ⟨i,a⟩)

omit [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S] [BorelSpace S] in
theorem selectedMarks_pooledTypes {q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i)
    (p : TupleState S k) : selectedMarks hk (pooledTypes p) = componentMarks hk p := rfl

omit [MetricSpace S] [DiscreteTopology S] [BorelSpace S] in
theorem marked_expectation_mul_factorials
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t) {n q : ℕ}
    (x : Fin n → S) (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    (∫ G, markedCount x G k r Ψ ∂FiniteIrreducibleTypedGraphLaw.law M t ht x) *
      (∏ i, ((k i).factorial : ℝ)) =
      ∑ f : Placements n k, placementProbability M t ht x k r f * Ψ (placementMarks hk f x) := by
  rw [← integral_mul_const]
  simp_rw [markedCount_mul_factorials_eq_sum_placements x _ k r hk Ψ]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro f _
    unfold placementProbability
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall (fun G ↦ by dsimp only; split_ifs <;> simp)
  · intro f _
    exact Integrable.of_finite

omit [MetricSpace S] [DiscreteTopology S] [BorelSpace S] in
theorem marked_expectation_by_selectedTypes
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t) {n q : ℕ}
    (x : Fin n → S) (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    (∫ G, markedCount x G k r Ψ ∂FiniteIrreducibleTypedGraphLaw.law M t ht x) =
      (∑ y : SelectedVertices k → S,
        (∏ a : S, ((fiberCount x a).descFactorial (fiberCount y a) : ℝ)) *
          (selectedTypeProbability M t ht x k r y * Ψ (selectedMarks hk y))) /
        (∏ i, ((k i).factorial : ℝ)) := by
  apply (eq_div_iff (factorialProduct_pos k).ne').mpr
  rw [marked_expectation_mul_factorials M t ht x k r hk Ψ]
  calc
    _ = ∑ f : Placements n k,
        selectedTypeProbability M t ht x k r (fun v ↦ x (f v)) *
          Ψ (selectedMarks hk (fun v ↦ x (f v))) := by
      apply Finset.sum_congr rfl
      intro f _
      rw [selectedTypeProbability_eq M t ht x k r (fun v ↦ x (f v)) ⟨f, fun _ ↦ rfl⟩]
      rfl
    _ = _ := by
      convert sum_embeddings_by_typePattern x
        (fun y ↦ selectedTypeProbability M t ht x k r y * Ψ (selectedMarks hk y)) using 1
      congr 1
      ext
      simp only [Finset.mem_univ]

omit [MetricSpace S] [DiscreteTopology S] [BorelSpace S] in
theorem marked_expectation_connectedOdds_formula_of_counts
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 ≤ t) {n q : ℕ}
    (x : Fin n → S) (c : S → ℕ) (hc : ∀ a, fiberCount x a = c a)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    (∫ G, markedCount x G k r Ψ ∂FiniteIrreducibleTypedGraphLaw.law M t ht x) =
      (∑ y : SelectedVertices k → S,
        (∏ a : S, ((c a).descFactorial (fiberCount y a) : ℝ)) *
          Real.exp (-(t / (n : ℝ) * countIsolationBudget M c y)) *
            (∏ i, connectedOddsWeight M t n (fun a ↦ y ⟨i,a⟩) (r i)) * Ψ (selectedMarks hk y)) /
        (∏ i, ((k i).factorial : ℝ)) := by
  rw [marked_expectation_by_selectedTypes M t ht x k r hk Ψ]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  rw [selectedTypeProbability_eq_exp_mul_selectedTypePatternOdds M t ht x k r hk y]
  have hh := congrArg (fun z : ℝ ↦ z * Ψ (selectedMarks hk y))
    (weighted_selectedTypePatternOdds_eq_connectedOdds_product M t ht x k r hk y)
  simp only [typedIsolationBudget_eq_countIsolationBudget M x c hc, hc] at hh
  simp only [typedIsolationBudget_eq_countIsolationBudget M x c hc, hc]
  convert hh using 1
  ring

omit [MetricSpace S] [DiscreteTopology S] [BorelSpace S] in
theorem sum_rawTupleWeight_mark_eq_connectedOdds_numerator
    (M : FiniteIrreducibleModel S) (t : ℝ) (n : ℕ) (c : S → ℕ)
    {q : ℕ} (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    (∑ p : TupleState S k, rawTupleWeight M t n c k r p * Ψ (componentMarks hk p)) =
      ∑ y : SelectedVertices k → S,
        (∏ a : S, ((c a).descFactorial (fiberCount y a) : ℝ)) *
          Real.exp (-(t / (n : ℝ) * countIsolationBudget M c y)) *
            (∏ i, connectedOddsWeight M t n (fun a ↦ y ⟨i,a⟩) (r i)) * Ψ (selectedMarks hk y) := by
  let e := stateTupleEquivTypesGraphs (S := S) k
  calc
    _ = ∑ z : ((SelectedVertices k → S) × GraphTuple k),
        rawTupleWeight M t n c k r (e.symm z) * Ψ (componentMarks hk (e.symm z)) :=
      (e.symm.sum_comp (fun p ↦ rawTupleWeight M t n c k r p * Ψ (componentMarks hk p))).symm
    _ = ∑ y : SelectedVertices k → S, ∑ H : GraphTuple k,
        selectionFactor c y * Real.exp (-(t / (n : ℝ) * countIsolationBudget M c y)) *
          (if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i) then
            ∏ i, graphOddsWeight M t n (fun a ↦ y ⟨i,a⟩) (H i) else 0) * Ψ (selectedMarks hk y) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      congr 1
      congr 1
      exact sum_eligibleGraphTuples_eq_prod_sums k r
        (fun i H ↦ graphOddsWeight M t n (fun a ↦ y ⟨i,a⟩) H)

theorem scaled_weighted_mark_integral_eq_sum_rawTupleWeight
    (M : FiniteIrreducibleModel S) (t : ℝ) {n : ℕ} (hn : 0 < n) (c : S → ℕ)
    {q : ℕ} (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    populationScale n k * edgeScale n k r *
      (∫ p, productOrdinaryWeight M.bjrModel t k r p *
        (residual M t n c p * Ψ (componentMarks hk p)) ∂baseLaw M.bjrModel k) =
      ∑ p : TupleState S k, rawTupleWeight M t n c k r p * Ψ (componentMarks hk p) := by
  rw [integral_baseLaw_eq_finite_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [rawTupleWeight_factorization M t hn c k r p]
  ring

/-- Exact marked factorial expectation for the actual fixed assignment,
with arbitrary coupled tests and the genuine connected-state product law. -/
theorem marked_factorial_expectation_connectedLaw_residual_formula
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 < t) {n q : ℕ} (hn : 0 < n)
    (x : Fin n → S) (c : S → ℕ) (hc : ∀ a, fiberCount x a = c a)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (pos : ∀ i, 0 < M.bjrModel.fieldConnectedWeight (M.bjrModel.scalarField t) (k i) (r i))
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) :
    (∫ G, markedCount x G k r Ψ ∂FiniteIrreducibleTypedGraphLaw.law M t ht.le x) =
      (populationScale n k * edgeScale n k r / (∏ i, ((k i).factorial : ℝ))) *
        (∏ i, M.bjrModel.connectedWeight t (k i) (r i)) *
          (∫ p, residual M t n c p * Ψ (componentMarks hk p)
            ∂connectedProductLaw M (M.bjrModel.scalarField t) k r pos) := by
  have he := marked_expectation_connectedOdds_formula_of_counts M t ht.le x c hc k r hk Ψ
  rw [← sum_rawTupleWeight_mark_eq_connectedOdds_numerator M t n c k r hk Ψ,
    ← scaled_weighted_mark_integral_eq_sum_rawTupleWeight M t hn c k r hk Ψ,
    ordinary_weighted_integral_eq_normalizer_mul_expectation M.bjrModel t ht k r pos] at he
  rw [connectedProductLaw_eq_dataProduct]
  unfold ordinaryNormalizer at he
  convert he using 1
  ring

end PerronWright.FiniteIrreducibleMarkedFactorialFormula
