import PerronWright.Probability.FiniteIrreducibleDeterministicResidualWeights
import PerronWright.Probability.FiniteIrreducibleProfileLaplace

/-!
# Exact deterministic finite factorial formula under actual connected laws

The literal connected-odds graph sum is converted to the actual fixed
target-law component-state product measure. The graph probability law
is still the deterministic-assignment law, not the annealed graph law.
A final large-size theorem obtains its positive normalizers from the
proved finite irreducible enumeration, without an interface premise.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleDeterministicConnectedLawFormula

open ComponentCounts AnnealedTupleResidualCounting
open AnnealedTupleResidualConnectedLawGraphTuple AnnealedTupleResidualConnectedLawProduct
open FiniteIrreducibleTypedGraphLaw FiniteIrreducibleTypePlacementMultiplicity
open FiniteIrreducibleConnectedOddsWeights FiniteIrreducibleConnectedOddsFactorialFormula
open FiniteIrreducibleConnectedLawFiniteSum FiniteIrreducibleGraphPatternProducts
open FiniteIrreducibleDeterministicResidualWeights

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- The genuine independent product of the actual finite connected-state
laws. Its one-component factors are not supplied as external profiles. -/
def connectedProductLaw (M : FiniteIrreducibleModel S) (g : C(S, ℝ))
    {q : ℕ} (k r : Fin q → ℕ)
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight g (k i) (r i)) :
    Measure (TupleState S k) :=
  Measure.pi (fun i ↦ FiniteIrreducibleConnectedTypeLaw.law M g (k i) (r i) (hC i))

instance connectedProductLaw_isProbability
    (M : FiniteIrreducibleModel S) (g : C(S, ℝ))
    {q : ℕ} (k r : Fin q → ℕ)
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight g (k i) (r i)) :
    IsProbabilityMeasure (connectedProductLaw M g k r hC) := by
  unfold connectedProductLaw
  infer_instance

theorem connectedProductLaw_eq_dataProduct
    (M : FiniteIrreducibleModel S) (g : C(S, ℝ))
    {q : ℕ} (k r : Fin q → ℕ)
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight g (k i) (r i)) :
    connectedProductLaw M g k r hC =
      AnnealedTupleResidualConnectedLawProduct.law M.bjrModel g k r hC := rfl

theorem residual_integrable_connectedProductLaw
    (M : FiniteIrreducibleModel S) (t : ℝ) (n : ℕ) (c : S → ℕ)
    (g : C(S, ℝ)) {q : ℕ} (k r : Fin q → ℕ)
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight g (k i) (r i)) :
    Integrable (residual M t n c) (connectedProductLaw M g k r hC) :=
  Integrable.of_finite

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
/-- Complete literal graph/type-state finite reindexing of the connected
odds numerator in the genuine arbitrary-count factorial formula. -/
theorem sum_rawTupleWeight_eq_connectedOdds_numerator
    (M : FiniteIrreducibleModel S) (t : ℝ) (n : ℕ) (c : S → ℕ)
    {q : ℕ} (k r : Fin q → ℕ) :
    (∑ p : TupleState S k, rawTupleWeight M t n c k r p) =
      ∑ y : SelectedVertices k → S,
        (∏ a : S, ((c a).descFactorial (fiberCount y a) : ℝ)) *
          Real.exp (-(t / (n : ℝ) * countIsolationBudget M c y)) *
            (∏ i, connectedOddsWeight M t n (fun a ↦ y ⟨i,a⟩) (r i)) := by
  let e := stateTupleEquivTypesGraphs (S := S) k
  calc
    _ = ∑ z : ((SelectedVertices k → S) × GraphTuple k),
        rawTupleWeight M t n c k r (e.symm z) :=
      (e.symm.sum_comp (rawTupleWeight M t n c k r)).symm
    _ = ∑ y : SelectedVertices k → S, ∑ H : GraphTuple k,
        selectionFactor c y * Real.exp (-(t / (n : ℝ) * countIsolationBudget M c y)) *
          (if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i) then
            ∏ i, graphOddsWeight M t n (fun a ↦ y ⟨i,a⟩) (H i) else 0) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.mul_sum]
      congr 1
      exact sum_eligibleGraphTuples_eq_prod_sums k r
        (fun i H ↦ graphOddsWeight M t n (fun a ↦ y ⟨i,a⟩) H)

/-- Actual sampling atom masses and the proved pointwise weight identity
give the exact unnormalized connected-state integral. -/
theorem scaled_weighted_integral_eq_sum_rawTupleWeight
    (M : FiniteIrreducibleModel S) (t : ℝ) {n : ℕ}
    (hn : 0 < n) (c : S → ℕ) {q : ℕ} (k r : Fin q → ℕ) :
    populationScale n k * edgeScale n k r *
      (∫ p, productOrdinaryWeight M.bjrModel t k r p * residual M t n c p
        ∂baseLaw M.bjrModel k) =
      ∑ p : TupleState S k, rawTupleWeight M t n c k r p := by
  rw [integral_baseLaw_eq_finite_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [rawTupleWeight_factorization M t hn c k r p]
  ring

/-- Exact genuine deterministic finite component factorial expectation
under the actual fixed-target connected-state product law, with every
finite-count and normalized edge-odds correction retained. -/
theorem factorial_expectation_connectedLaw_residual_formula
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 < t) {n q : ℕ}
    (hn : 0 < n) (x : Fin n → S) (c : S → ℕ)
    (hc : ∀ a, fiberCount x a = c a) (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight (M.bjrModel.scalarField t) (k i) (r i)) :
    (∫ G, (count G k r : ℝ) ∂FiniteIrreducibleTypedGraphLaw.law M t ht.le x) =
      (populationScale n k * edgeScale n k r / (∏ i, ((k i).factorial : ℝ))) *
        (∏ i, M.bjrModel.connectedWeight t (k i) (r i)) *
          (∫ p, residual M t n c p
            ∂connectedProductLaw M (M.bjrModel.scalarField t) k r hC) := by
  have he := factorial_expectation_connectedOdds_formula_of_counts M t ht.le x c hc k r hk
  rw [← sum_rawTupleWeight_eq_connectedOdds_numerator,
    ← scaled_weighted_integral_eq_sum_rawTupleWeight M t hn c k r,
    ordinary_weighted_integral_eq_normalizer_mul_expectation M.bjrModel t ht k r hC] at he
  rw [connectedProductLaw_eq_dataProduct]
  unfold ordinaryNormalizer at he
  convert he using 1
  ring

/-- No normalizer interface is needed in the actual finite irreducible
branch: bounded surplus and sufficiently large sizes supply the genuine
connected laws and the exact arbitrary-assignment factorial formula. -/
theorem exists_large_size_connectedLaw_residual_formula
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (R : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∀ {n q : ℕ} (_hn : 0 < n)
      (t : ℝ) (ht : 0 < t) (x : Fin n → S) (c : S → ℕ)
      (_hc : ∀ a, fiberCount x a = c a) (k r : Fin q → ℕ),
      (∀ i, K ≤ k i) → (∀ i, r i ≤ R) →
      ∃ hC : ∀ i, 0 < M.bjrModel.fieldConnectedWeight (M.bjrModel.scalarField t) (k i) (r i),
        (∫ G, (count G k r : ℝ) ∂FiniteIrreducibleTypedGraphLaw.law M t ht.le x) =
          (populationScale n k * edgeScale n k r / (∏ i, ((k i).factorial : ℝ))) *
            (∏ i, M.bjrModel.connectedWeight t (k i) (r i)) *
              (∫ p, residual M t n c p
                ∂connectedProductLaw M (M.bjrModel.scalarField t) k r hC) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (FiniteIrreducibleProfileLaplace.eventually_all_field_normalizers_pos M hM R)
  refine ⟨max 1 K, by omega, ?_⟩
  intro n q hn t ht x c hc k r hk hr
  have hC (i : Fin q) :
      0 < M.bjrModel.fieldConnectedWeight (M.bjrModel.scalarField t) (k i) (r i) :=
    hK (k i) ((le_max_right 1 K).trans (hk i)) (r i) (hr i) _
  refine ⟨hC, ?_⟩
  exact factorial_expectation_connectedLaw_residual_formula M t ht hn x c hc k r
    (fun i ↦ by have := hk i; omega) hC

end PerronWright.FiniteIrreducibleDeterministicConnectedLawFormula

