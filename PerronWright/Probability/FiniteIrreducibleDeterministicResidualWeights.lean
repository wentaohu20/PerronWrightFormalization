import PerronWright.Probability.FiniteIrreducibleConnectedLawFiniteSum
import PerronWright.Probability.FiniteIrreducibleConnectedOddsFactorialFormula

/-!
# Exact deterministic target-law connected residual weights

The fixed target atom law is used only for the genuine connected-state
probability law. Every empirical-count discrepancy remains explicitly
in the residual. Zero kernel entries use normalizedOdds 0 = 1, with
no division by a kernel entry and no primitive/B2 restriction.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleDeterministicResidualWeights

open AnnealedTupleResidualCounting AnnealedTupleResidualConnectedLawGraphTuple
open AnnealedTupleResidualConnectedLawProduct FreshTypeAveraging
open FiniteIrreducibleTypePlacementMultiplicity FiniteIrreducibleTypeFiberSums
open FiniteIrreducibleConnectedOddsWeights FiniteIrreducibleConnectedOddsFactorialFormula
open FiniteIrreducibleConnectedLawFiniteSum FiniteIrreducibleGraphPatternProducts

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def selectionFactor (c : S → ℕ) {q : ℕ} {k : Fin q → ℕ}
    (y : SelectedVertices k → S) : ℝ :=
  ∏ a : S, ((c a).descFactorial (fiberCount y a) : ℝ)

def targetSelectionRatio (M : FiniteIrreducibleModel S) (n : ℕ)
    (c : S → ℕ) {q : ℕ} {k : Fin q → ℕ} (y : SelectedVertices k → S) : ℝ :=
  ∏ a : S, ((c a).descFactorial (fiberCount y a) : ℝ) /
    ((n : ℝ) * M.weight a) ^ fiberCount y a

def populationScale (n : ℕ) {q : ℕ} (k : Fin q → ℕ) : ℝ :=
  (n : ℝ) ^ (∑ i, k i)

def edgeScale (n : ℕ) {q : ℕ} (k r : Fin q → ℕ) : ℝ :=
  (n : ℝ)⁻¹ ^ (∑ i, (k i + r i - 1))

def targetDegreeSum (M : FiniteIrreducibleModel S)
    {q : ℕ} {k : Fin q → ℕ} (p : TupleState S k) : ℝ :=
  ∑ i, ∑ a : Fin (k i), M.bjrModel.degreeFunction ((p i).1 a)

theorem targetDegreeSum_eq_typeCount_sum (M : FiniteIrreducibleModel S)
    {q : ℕ} {k : Fin q → ℕ} (p : TupleState S k) :
    targetDegreeSum M p = ∑ a : S, (fiberCount (pooledTypes p) a : ℝ) *
      (∑ b : S, M.kernel a b * M.weight b) := by
  unfold targetDegreeSum
  change (∑ i, ∑ v, M.bjrModel.degreeFunction (pooledTypes p ⟨i,v⟩)) = _
  rw [← Fintype.sum_sigma (fun v : SelectedVertices k ↦
    M.bjrModel.degreeFunction (pooledTypes p v))]
  rw [sum_by_typeFibers (pooledTypes p) M.bjrModel.degreeFunction]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  exact (M.bjrModel.kernel.degreeMap_apply M.bjrModel.mu a).trans
    (M.degree_eq_weighted_sum a)

def tupleEdgeProduct (M : FiniteIrreducibleModel S) (t : ℝ)
    {q : ℕ} {k : Fin q → ℕ} (p : TupleState S k) : ℝ :=
  ∏ i, ∏ e ∈ (p i).2.edgeFinset, M.bjrModel.edgeFactor t (p i).1 e

/-- Actual normalized odds factors, with the proved zero-hazard convention. -/
def oddsCorrection (M : FiniteIrreducibleModel S) (t : ℝ) (n : ℕ)
    {q : ℕ} {k : Fin q → ℕ} (p : TupleState S k) : ℝ :=
  ∏ i, ∏ e ∈ (p i).2.edgeFinset,
    normalizedOdds (M.bjrModel.edgeFactor t (p i).1 e / (n : ℝ))

/-- All empirical-count and exact edge-odds corrections for the actual
deterministic graph, expressed relative to the fixed target law. -/
def residual (M : FiniteIrreducibleModel S) (t : ℝ) (n : ℕ) (c : S → ℕ)
    {q : ℕ} {k : Fin q → ℕ} (p : TupleState S k) : ℝ :=
  targetSelectionRatio M n c (pooledTypes p) *
    Real.exp (t * targetDegreeSum M p -
      t / (n : ℝ) * countIsolationBudget M c (pooledTypes p)) *
    oddsCorrection M t n p

/-- The literal type-count and connected-graph sum integrand, without
replacing its genuine graph eligibility tests. -/
def rawTupleWeight (M : FiniteIrreducibleModel S) (t : ℝ) (n : ℕ) (c : S → ℕ)
    {q : ℕ} (k r : Fin q → ℕ) (p : TupleState S k) : ℝ :=
  selectionFactor c (pooledTypes p) *
    Real.exp (-(t / (n : ℝ) * countIsolationBudget M c (pooledTypes p))) *
    (if ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2 then
      ∏ i, graphOddsWeight M t n (p i).1 (p i).2 else 0)

omit [DecidableEq S] [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem sum_pooled_fiberCount {q : ℕ} (k : Fin q → ℕ) (p : TupleState S k) :
    ∑ a : S, fiberCount (pooledTypes p) a = ∑ i, k i := by
  rw [sum_fiberCount, Fintype.card_sigma]
  simp only [Fintype.card_fin]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem selection_ratio_cancellation (M : FiniteIrreducibleModel S)
    {n : ℕ} (hn : 0 < n) (c : S → ℕ)
    {q : ℕ} (k : Fin q → ℕ) (p : TupleState S k) :
    populationScale n k * samplingWeight M k p *
      targetSelectionRatio M n c (pooledTypes p) =
        selectionFactor c (pooledTypes p) := by
  have hden : (∏ a : S, ((n : ℝ) * M.weight a) ^ fiberCount (pooledTypes p) a) =
      populationScale n k * samplingWeight M k p := by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, sum_pooled_fiberCount,
      samplingWeight_eq_fiberProduct]
    rfl
  have hnonzero : populationScale n k * samplingWeight M k p ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_pos.mpr hn).ne')
      (samplingWeight_pos M k p).ne'
  unfold targetSelectionRatio
  rw [Finset.prod_div_distrib, hden]
  unfold selectionFactor
  exact mul_div_cancel₀ _ hnonzero

theorem edgeFactor_eq_pairKernel (M : FiniteIrreducibleModel S) (t : ℝ)
    {k : ℕ} (y : Fin k → S) (e : Sym2 (Fin k)) :
    M.bjrModel.edgeFactor t y e = t * FiniteIrreducibleTypedGraphLaw.pairKernel M y e := by
  induction e using Sym2.inductionOn with
  | _ i j => rfl

theorem graphOddsWeight_factorization (M : FiniteIrreducibleModel S)
    (t : ℝ) (n : ℕ) {k : ℕ} (y : Fin k → S) (H : SimpleGraph (Fin k)) :
    graphOddsWeight M t n y H =
      (n : ℝ)⁻¹ ^ H.edgeFinset.card *
        (∏ e ∈ H.edgeFinset, M.bjrModel.edgeFactor t y e) *
          (∏ e ∈ H.edgeFinset, normalizedOdds (M.bjrModel.edgeFactor t y e / (n : ℝ))) := by
  unfold graphOddsWeight edgeOdds
  simp_rw [← edgeFactor_eq_pairKernel]
  exact prod_present_odds_factorization M.bjrModel t n y H

theorem tuple_graphOddsWeight_factorization (M : FiniteIrreducibleModel S)
    (t : ℝ) (n : ℕ) {q : ℕ} (k r : Fin q → ℕ) (p : TupleState S k)
    (h : ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2) :
    (∏ i, graphOddsWeight M t n (p i).1 (p i).2) =
      edgeScale n k r * tupleEdgeProduct M t p * oddsCorrection M t n p := by
  unfold edgeScale tupleEdgeProduct oddsCorrection
  simp_rw [graphOddsWeight_factorization, (h _).2]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem productOrdinaryWeight_eq_indicator (M : FiniteIrreducibleModel S)
    (t : ℝ) {q : ℕ} (k r : Fin q → ℕ) (p : TupleState S k) :
    productOrdinaryWeight M.bjrModel t k r p =
      if ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2 then
        ∏ i, M.bjrModel.graphWeightIntegrand t (p i).2 (p i).1 else 0 := by
  unfold productOrdinaryWeight ordinaryWeight
  exact prod_eligible_weights k r (fun i ↦ (p i).2)
    (fun i H ↦ M.bjrModel.graphWeightIntegrand t H (p i).1)

theorem ordinaryWeight_exponential_cancellation (M : FiniteIrreducibleModel S)
    (t : ℝ) {q : ℕ} (k r : Fin q → ℕ) (p : TupleState S k)
    (h : ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2) :
    productOrdinaryWeight M.bjrModel t k r p * Real.exp (t * targetDegreeSum M p) =
      tupleEdgeProduct M t p := by
  rw [productOrdinaryWeight_eq_indicator, if_pos h]
  unfold CompactBJRModel.graphWeightIntegrand tupleEdgeProduct
  rw [Finset.prod_mul_distrib]
  have hv : (∏ i, ∏ a : Fin (k i),
      Real.exp (-t * M.bjrModel.degreeFunction ((p i).1 a))) =
        Real.exp (-t * targetDegreeSum M p) := by
    simp_rw [← Real.exp_sum]
    unfold targetDegreeSum
    congr 1
    simp_rw [← Finset.mul_sum]
  rw [hv]
  calc
    _ = (Real.exp (-t * targetDegreeSum M p) *
        Real.exp (t * targetDegreeSum M p)) *
          (∏ i, ∏ e ∈ (p i).2.edgeFinset, M.bjrModel.edgeFactor t (p i).1 e) := by ring
    _ = _ := by rw [← Real.exp_add]; simp

/-- Pointwise genuine deterministic finite raw weight is the proved
sampling density times the actual connected graph weight and residual.
No eligible graph or type-profile conclusion is assumed. -/
theorem rawTupleWeight_factorization (M : FiniteIrreducibleModel S)
    (t : ℝ) {n : ℕ} (hn : 0 < n) (c : S → ℕ)
    {q : ℕ} (k r : Fin q → ℕ) (p : TupleState S k) :
    rawTupleWeight M t n c k r p =
      populationScale n k * edgeScale n k r * samplingWeight M k p *
        productOrdinaryWeight M.bjrModel t k r p * residual M t n c p := by
  by_cases h : ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2
  · unfold rawTupleWeight residual
    rw [if_pos h, tuple_graphOddsWeight_factorization M t n k r p h]
    have he : Real.exp (t * targetDegreeSum M p -
        t / (n : ℝ) * countIsolationBudget M c (pooledTypes p)) =
        Real.exp (t * targetDegreeSum M p) *
          Real.exp (-(t / (n : ℝ) * countIsolationBudget M c (pooledTypes p))) := by
      rw [← Real.exp_add]
      congr 1
    rw [he]
    symm
    calc
      _ = edgeScale n k r *
          (populationScale n k * samplingWeight M k p *
            targetSelectionRatio M n c (pooledTypes p)) *
          (productOrdinaryWeight M.bjrModel t k r p * Real.exp (t * targetDegreeSum M p)) *
          Real.exp (-(t / (n : ℝ) * countIsolationBudget M c (pooledTypes p))) *
          oddsCorrection M t n p := by ring
      _ = _ := by
        rw [selection_ratio_cancellation M hn c k p,
          ordinaryWeight_exponential_cancellation M t k r p h]
        ring
  · rw [rawTupleWeight, if_neg h, productOrdinaryWeight_eq_indicator, if_neg h]
    ring

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem targetSelectionRatio_nonneg (M : FiniteIrreducibleModel S) (n : ℕ)
    (c : S → ℕ) {q : ℕ} {k : Fin q → ℕ} (y : SelectedVertices k → S) :
    0 ≤ targetSelectionRatio M n c y :=
  Finset.prod_nonneg (fun a _ ↦ div_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (mul_nonneg (Nat.cast_nonneg n) (M.weight_pos a).le) _))

theorem oddsCorrection_pos (M : FiniteIrreducibleModel S) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) {q : ℕ} {k : Fin q → ℕ} (p : TupleState S k) :
    0 < oddsCorrection M t n p := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro e _
  apply FreshTypeCumulantExpansion.normalizedOdds_pos
  rw [edgeFactor_eq_pairKernel]
  exact div_nonneg (mul_nonneg ht
    (FiniteIrreducibleTypedGraphLaw.pairKernel_nonneg M (p i).1 e)) (Nat.cast_nonneg n)

theorem residual_nonneg (M : FiniteIrreducibleModel S) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) (c : S → ℕ) {q : ℕ} {k : Fin q → ℕ}
    (p : TupleState S k) : 0 ≤ residual M t n c p :=
  mul_nonneg (mul_nonneg (targetSelectionRatio_nonneg M n c (pooledTypes p))
    (Real.exp_nonneg _)) (oddsCorrection_pos M ht n p).le

end PerronWright.FiniteIrreducibleDeterministicResidualWeights

