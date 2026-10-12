import PerronWright.Probability.AnnealedTupleResidualConnectedLawCoordinates
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The genuine product-connected-law residual formula

Regularity and finite-graph Fubini are proved for the literal residual,
so the final bridge does not assume an unproved integral identity.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedTupleResidualConnectedLawFormula

open AnnealedGraph ComponentCounts ExactFactorialExpectation
open FreshTypeAveraging AnnealedResidualFixedBlock
open AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
open AnnealedTupleResidualConnectedLawGraphTuple AnnealedTupleResidualConnectedLawWeights
open AnnealedTupleResidualConnectedLawProduct AnnealedTupleResidualConnectedLawCoordinates

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

/-- Fresh-type averaging is jointly continuous in the selected type vector. -/
theorem isolationFactor_continuous {I : Type*} [Fintype I]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ) : Continuous (isolationFactor (I := I) M t n) := by
  have hf : Continuous (Function.uncurry (freshAbsence (I := I) M t n)) := by
    unfold freshAbsence exposure Function.uncurry
    apply Continuous.rexp
    apply Continuous.div_const
    apply Continuous.mul continuous_const
    apply continuous_finsetSum
    intro i _
    exact M.kernel.toContinuousMap.continuous.comp
      (((continuous_apply i).comp continuous_fst).prodMk continuous_snd)
  unfold isolationFactor
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := M.mu) hf isCompact_univ)

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
theorem combineTypes_continuous {n : ℕ} (B : Finset (Fin n)) (s₀ : S) :
    Continuous (fun u : ↥B → S ↦ combineTypes B u (fun _ ↦ s₀)) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ B
  · simp only [combineTypes,dif_pos hi]
    exact continuous_apply (⟨i,hi⟩ : ↥B)
  · simp only [combineTypes,dif_neg hi]
    exact continuous_const

theorem internalPairWeightOn_continuous {n : ℕ} (M : CompactBJRModel S)
    (B : Finset (Fin n)) (s₀ : S) : Continuous (fun u : ↥B → S ↦ internalPairWeightOn M B u s₀) := by
  unfold internalPairWeightOn
  apply continuous_finsetSum
  intro e _
  exact (M.edgeFactor_continuous 1 e.val).comp (combineTypes_continuous B s₀)

theorem internalOddsProduct_continuous {n : ℕ} (M : CompactBJRModel S)
    (t : ℝ) (B : Finset (Fin n)) (H : SimpleGraph (Fin n)) (s₀ : S) :
    Continuous (fun u : ↥B → S ↦ internalOddsProduct M t B H u s₀) := by
  unfold internalOddsProduct
  apply continuous_finsetProd
  intro e _
  cases assignmentOfGraph H e
  · simp only [Bool.false_eq_true,if_false]
    exact continuous_const
  · simp only [if_true,hazard]
    exact ((((M.edgeFactor_continuous t e.val).comp (combineTypes_continuous B s₀)).div_const _).rexp).sub
      continuous_const

def selectedProbabilityIntegrand {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) (s₀ : S) (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) : ℝ :=
  Real.exp (-t * internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀ / (n : ℝ)) *
    isolationFactor M t n u ^ (n-(selectedUnion (blocksOfPlacement hk f)).card) *
    internalOddsProduct M t (selectedUnion (blocksOfPlacement hk f)) (tupleGraph f H) u s₀

theorem selectedProbabilityIntegrand_continuous {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) (s₀ : S) : Continuous (selectedProbabilityIntegrand M t hk f H s₀) := by
  unfold selectedProbabilityIntegrand
  exact (((continuous_const.mul (internalPairWeightOn_continuous M _ s₀)).div_const _).rexp.mul
    ((isolationFactor_continuous M t n).pow _)).mul (internalOddsProduct_continuous M t _ _ s₀)

/-- Weighted residual regularity follows from the exact probability integrand.
No regularity of division by individual, possibly zero kernel entries is assumed. -/
theorem weightedResidual_continuous {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hn : 0 < n) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) (s₀ : S) :
    Continuous (fun u : ↥(selectedUnion (blocksOfPlacement hk f)) → S ↦
      (∏ i, M.graphWeightIntegrand t (H i) (blockTypes hk f u i)) *
        selectedResidual M t hk f H u s₀) := by
  have hnz : (n : ℝ)⁻¹ ^ (tupleGraph f H).edgeFinset.card ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne'))
  have heq : (fun u : ↥(selectedUnion (blocksOfPlacement hk f)) → S ↦
      (∏ i, M.graphWeightIntegrand t (H i) (blockTypes hk f u i)) *
        selectedResidual M t hk f H u s₀) =
      (fun u ↦ selectedProbabilityIntegrand M t hk f H s₀ u /
        ((n : ℝ)⁻¹ ^ (tupleGraph f H).edgeFinset.card)) := by
    funext u
    unfold selectedProbabilityIntegrand
    rw [selected_integrand_weight_factorization]
    field_simp [hnz]
  rw [heq]
  exact (selectedProbabilityIntegrand_continuous M t hk f H s₀).div_const _

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
theorem selectedTypes_continuous {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) :
    Continuous (selectedTypes (S := S) hk f) := by
  apply continuous_pi
  intro v
  exact (continuous_apply ((selectedVerticesEquiv hk f).symm v).2).comp
    (continuous_apply ((selectedVerticesEquiv hk f).symm v).1)

theorem productOrdinaryWeight_tupleState {q : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (k r : Fin q → ℕ) (x : (i : Fin q) → Fin (k i) → S) (H : GraphTuple k) :
    productOrdinaryWeight M t k r (tupleState x H) =
      if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i) then
        ∏ i, M.graphWeightIntegrand t (H i) (x i) else 0 := by
  by_cases hH : ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)
  · simp only [if_pos hH,productOrdinaryWeight,ordinaryWeight,tupleState]
    apply Finset.prod_congr rfl
    intro i _
    exact if_pos (hH i)
  · simp only [if_neg hH]
    obtain ⟨i,hi⟩ := not_forall.mp hH
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      simp only [ordinaryWeight,tupleState,if_neg hi])

theorem ordinaryWeightedResidual_continuous_slice {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hn : 0 < n) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S) (H : GraphTuple k) :
    Continuous (fun x : (i : Fin q) → Fin (k i) → S ↦
      productOrdinaryWeight M t k r (tupleState x H) *
        residualObservable M t hk f s₀ (tupleState x H)) := by
  simp_rw [productOrdinaryWeight_tupleState]
  by_cases hH : ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)
  · simp only [if_pos hH]
    have hc := (weightedResidual_continuous M t hn hk f H s₀).comp (selectedTypes_continuous hk f)
    simpa only [Function.comp_def,blockTypes_selectedTypes,residualObservable,tupleState] using hc
  · simp only [if_neg hH,zero_mul]
    exact continuous_const

/-- The weighted residual is integrable on the literal unweighted joint
component-state law. -/
theorem ordinaryWeightedResidual_integrable {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hn : 0 < n) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S) :
    Integrable (fun p ↦ productOrdinaryWeight M t k r p * residualObservable M t hk f s₀ p)
      (baseLaw M k) := by
  let W : TupleState S k → ℝ :=
    fun p ↦ productOrdinaryWeight M t k r p * residualObservable M t hk f s₀ p
  let e := dependentPiProd (fun i : Fin q ↦ Fin (k i) → S)
    (fun i : Fin q ↦ SimpleGraph (Fin (k i)))
  have hm : Measurable (fun p : ((i : Fin q) → Fin (k i) → S) × GraphTuple k ↦ W (e.symm p)) :=
    measurable_from_prod_countable_left
      (fun H ↦ (ordinaryWeightedResidual_continuous_slice M t hn k r hk f s₀ H).measurable)
  have hi : Integrable (fun p : ((i : Fin q) → Fin (k i) → S) × GraphTuple k ↦ W (e.symm p))
      ((Measure.pi (fun i ↦ typeLaw M (k i))).prod Measure.count) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun H ↦ ?_),Integrable.of_finite⟩
    exact (ordinaryWeightedResidual_continuous_slice M t hn k r hk f s₀ H).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have h := (baseLaw_coordinates M k).integrable_comp_of_integrable hi
  change Integrable (fun p ↦ W (e.symm (e p))) (baseLaw M k) at h
  simpa only [MeasurableEquiv.symm_apply_apply] using h

/-- The literal residual really is an integrable random variable under
the genuine product connected law, including possibly zero kernel entries. -/
theorem residualObservable_integrable_connectedLaw {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t) (hn : 0 < n) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField t) (k i) (r i)) :
    Integrable (residualObservable M t hk f s₀)
      (AnnealedTupleResidualConnectedLawProduct.law M (M.scalarField t) k r hC) := by
  rw [law_eq_withDensity]
  have hd : Measurable (fun p : TupleState S k ↦
      ENNReal.ofReal (normalizedWeight M (M.scalarField t) k r p)) :=
    ENNReal.measurable_ofReal.comp (normalizedWeight_measurable M _ k r)
  rw [integrable_withDensity_iff_integrable_smul' hd
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (normalizedWeight_nonneg M _ k r hC _),smul_eq_mul]
  have hi := ordinaryWeightedResidual_integrable M t hn k r hk f s₀
  have hscale : surplusScale t r ≠ 0 := (surplusScale_pos t ht r).ne'
  have hs : Integrable (fun p ↦ productWeight M (M.scalarField t) k r p *
      residualObservable M t hk f s₀ p) (baseLaw M k) := by
    have hh := hi.div_const (surplusScale t r)
    convert hh using 1
    funext p
    rw [productOrdinaryWeight_scalarField M t ht]
    field_simp
  convert hs.div_const (productNormalizer M (M.scalarField t) k r) using 1
  funext p
  rw [normalizedWeight_eq]
  ring

/-- The weighted state integral is the previously proved actual-pattern
sum after its graph reindexing and type-coordinate change. -/
theorem weighted_baseLaw_integral_eq_graphTupleSum {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hn : 0 < n) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S) :
    (∫ p, productOrdinaryWeight M t k r p * residualObservable M t hk f s₀ p ∂baseLaw M k) =
      ∑ H : GraphTuple k, if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i) then
        (∫ u : ↥(selectedUnion (blocksOfPlacement hk f)) → S,
          (∏ i, M.graphWeightIntegrand t (H i) (blockTypes hk f u i)) *
            selectedResidual M t hk f H u s₀ ∂Measure.pi (fun _ ↦ M.mu)) else 0 := by
  rw [integral_baseLaw_eq_sum_graph_integrals M k
    (fun p ↦ productOrdinaryWeight M t k r p * residualObservable M t hk f s₀ p)
    (fun H ↦ (ordinaryWeightedResidual_continuous_slice M t hn k r hk f s₀ H).measurable)
    (fun H ↦ (ordinaryWeightedResidual_continuous_slice M t hn k r hk f s₀ H).integrable_of_hasCompactSupport
      isClosed_closure.isCompact)]
  apply Finset.sum_congr rfl
  intro H _
  simp_rw [productOrdinaryWeight_tupleState]
  by_cases hH : ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)
  · simp only [if_pos hH]
    convert integral_selectedTypes M hk f
      (fun u ↦ (∏ i, M.graphWeightIntegrand t (H i) (blockTypes hk f u i)) *
        selectedResidual M t hk f H u s₀) using 1
    simp only [blockTypes_selectedTypes,residualObservable,tupleState]
  · simp only [if_neg hH,zero_mul,integral_zero]

/-- Exact genuine product-Q expectation of the literal finite-n residual. -/
theorem selectedPatternSum_eq_connectedLaw_expectation {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t) (hn : 0 < n) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField t) (k i) (r i)) :
    selectedPatternSum M t (blocksOfPlacement hk f) k r s₀ =
      (n : ℝ)⁻¹ ^ (∑ i : Fin q, (k i+r i-1)) * ordinaryNormalizer M t k r *
        ∫ p, residualObservable M t hk f s₀ p
          ∂AnnealedTupleResidualConnectedLawProduct.law M (M.scalarField t) k r hC := by
  rw [selectedPatternSum_eq_weighted_graphTupleSum,
    ← weighted_baseLaw_integral_eq_graphTupleSum M t hn k r hk f s₀,
    ordinary_weighted_integral_eq_normalizer_mul_expectation M t ht k r hC]
  ring

/-- The actual ordered distinct-component expectation has the paper's
literal selection factor, enumerator product, and genuine product-Q
residual expectation.  Every coordinate and normalization bridge above
is proved from the graph/type probability laws and real component count. -/
theorem factorial_expectation_connectedLaw_residual_formula {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t) (hn : 0 < n) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField t) (k i) (r i)) :
    (∫ G, (ComponentCounts.count G k r : ℝ) ∂AnnealedGraph.law M t ht.le n) =
      ((n.descFactorial (∑ i, k i) : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
        ((n : ℝ)⁻¹ ^ (∑ i : Fin q, (k i+r i-1))) *
        (∏ i, M.connectedWeight t (k i) (r i)) *
        ∫ p, residualObservable M t hk f s₀ p
          ∂AnnealedTupleResidualConnectedLawProduct.law M (M.scalarField t) k r hC := by
  rw [factorial_expectation_selected_pattern_formula M t ht.le k r hk f s₀,
    selectedPatternSum_eq_connectedLaw_expectation M t ht hn k r hk f s₀ hC]
  unfold ordinaryNormalizer
  ring

end PerronWright.AnnealedTupleResidualConnectedLawFormula
