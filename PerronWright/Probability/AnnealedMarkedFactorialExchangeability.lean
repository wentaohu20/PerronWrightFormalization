import PerronWright.Probability.AnnealedMarkedFactorialCounting

/-! # Actual typed-graph exchangeability and marked selection multiplicity -/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedMarkedFactorialExchangeability

open AnnealedGraph AnnealedMarkedFactorialCounting AnnealedTupleResidualCounting
  AnnealedTupleResidualExchangeability ComponentCounts

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

theorem typedObservable_integrable_of_continuous_slices {n : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t)
    (F : AnnealedTypedGraph.State S n → ℝ)
    (hF : ∀ a, Continuous (fun x ↦ F (x,a))) :
    Integrable F (AnnealedTypedGraph.law M t ht n) := by
  have hd : Measurable (fun p : AnnealedTypedGraph.State S n ↦
      ENNReal.ofReal (conditionalMass M t p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp (AnnealedTypedGraph.measurable_conditionalMass M t n)
  rw [AnnealedTypedGraph.law,integrable_withDensity_iff_integrable_smul' hd
    (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (conditionalMass_nonneg M ht _ _),smul_eq_mul]
  have hm : Measurable (fun p : AnnealedTypedGraph.State S n ↦ conditionalMass M t p.1 p.2 * F p) :=
    measurable_from_prod_countable_left (fun a ↦ ((conditionalMass_continuous M t a).mul (hF a)).measurable)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun a ↦ ?_),Integrable.of_finite⟩
  exact ((conditionalMass_continuous M t a).mul (hF a)).integrable_of_hasCompactSupport isClosed_closure.isCompact

theorem typedExpectation_eq_typeIntegral {n : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t)
    (F : AnnealedTypedGraph.State S n → ℝ)
    (hF : ∀ a, Continuous (fun x ↦ F (x,a))) :
    (∫ p, F p ∂AnnealedTypedGraph.law M t ht n) =
      ∫ x, ∑ a : Assignment n, conditionalMass M t x a * F (x,a) ∂typeLaw M n :=
  AnnealedTypedGraph.expectation_eq_type_integral M t ht n F (fun a ↦ (hF a).measurable)
    (fun a ↦ ((conditionalMass_continuous M t a).mul (hF a)).integrable_of_hasCompactSupport isClosed_closure.isCompact)

def placementObservable {n q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i)
    (f : Placements n k) (r : Fin q → ℕ) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ)
    (p : AnnealedTypedGraph.State S n) : ℝ :=
  if ∀ i, MatchesBlock (AnnealedTypedGraph.graph p) (blockOfPlacement f i) (k i) (r i)
    then Ψ (placementMarks hk f p.1) else 0

theorem placementObservable_continuous_slice {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) (r : Fin q → ℕ)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) (a : Assignment n) :
    Continuous (fun x ↦ placementObservable hk f r Ψ (x,a)) := by
  change Continuous (fun x : Fin n → S ↦
    if ∀ i, MatchesBlock (toGraph a) (blockOfPlacement f i) (k i) (r i) then Ψ (placementMarks hk f x) else 0)
  by_cases hc : ∀ i, MatchesBlock (toGraph a) (blockOfPlacement f i) (k i) (r i)
  · simp only [if_pos hc]
    exact hΨ.comp (placementMarks_continuous hk f)
  · simp only [if_neg hc]
    exact continuous_const

theorem markedExpectation_mul_factorials_eq_sum_placements {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    (∫ p, markedCount p.1 (AnnealedTypedGraph.graph p) k r Ψ ∂AnnealedTypedGraph.law M t ht n) *
      (∏ i, ((k i).factorial:ℝ)) = ∑ f : Placements n k,
        ∫ p, placementObservable hk f r Ψ p ∂AnnealedTypedGraph.law M t ht n := by
  rw [← integral_mul_const]
  simp_rw [markedCount_mul_factorials_eq_sum_placements _ _ k r hk Ψ]
  rw [integral_finsetSum]
  · rfl
  · intro f _
    exact typedObservable_integrable_of_continuous_slices M t ht _
      (placementObservable_continuous_slice hk f r Ψ hΨ)

/-- Literal relabelling of both sampled types and edge assignments. -/
theorem typedExpectation_permutation {n : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (σ : Equiv.Perm (Fin n))
    (F : AnnealedTypedGraph.State S n → ℝ) (hF : ∀ a, Continuous (fun x ↦ F (x,a))) :
    (∫ p, F (fun i ↦ p.1 (σ i),assignmentPermutation σ p.2) ∂AnnealedTypedGraph.law M t ht n) =
      ∫ p, F p ∂AnnealedTypedGraph.law M t ht n := by
  have hp (a : Assignment n) : Continuous (fun x : Fin n → S ↦
      F (fun i ↦ x (σ i),assignmentPermutation σ a)) :=
    (hF _).comp (continuous_pi (fun i ↦ continuous_apply (σ i)))
  rw [typedExpectation_eq_typeIntegral M t ht _ hp,typedExpectation_eq_typeIntegral M t ht F hF]
  rw [← integral_type_permutation M σ (fun x ↦ ∑ a : Assignment n, conditionalMass M t x a * F (x,a))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← (assignmentPermutation σ).sum_comp
    (fun a ↦ conditionalMass M t (fun i ↦ x (σ i)) a * F (fun i ↦ x (σ i),a))]
  simp_rw [conditionalMass_permutation]

theorem placementExpectation_eq {n q : ℕ} (M : CompactBJRModel S)
    (t : ℝ) (ht : 0 ≤ t) (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (f g : Placements n k) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    (∫ p, placementObservable hk f r Ψ p ∂AnnealedTypedGraph.law M t ht n) =
      ∫ p, placementObservable hk g r Ψ p ∂AnnealedTypedGraph.law M t ht n := by
  obtain ⟨σ,hσ⟩ := exists_permutation_placements f g
  have he (p : AnnealedTypedGraph.State S n) :
      placementObservable hk f r Ψ (fun i ↦ p.1 (σ i),assignmentPermutation σ p.2) =
        placementObservable hk g r Ψ p := by
    have hm : (∀ i, MatchesBlock ((toGraph p.2).comap σ) (blockOfPlacement f i) (k i) (r i)) ↔
        (∀ i, MatchesBlock (toGraph p.2) (blockOfPlacement g i) (k i) (r i)) := by
      apply forall_congr'
      intro i
      rw [matchesBlock_comap_permutation,blockOfPlacement_permutation σ f g hσ]
    have hmark : placementMarks hk f (fun i ↦ p.1 (σ i)) = placementMarks hk g p.1 := by
      funext i
      unfold placementMarks
      congr 1
      funext a
      exact congrArg p.1 (hσ ⟨i,a⟩)
    unfold placementObservable AnnealedTypedGraph.graph
    rw [toGraph_assignmentPermutation]
    exact if_congr hm (congrArg Ψ hmark) rfl
  calc
    _ = ∫ p, placementObservable hk f r Ψ (fun i ↦ p.1 (σ i),assignmentPermutation σ p.2)
        ∂AnnealedTypedGraph.law M t ht n :=
      (typedExpectation_permutation M t ht σ _ (placementObservable_continuous_slice hk f r Ψ hΨ)).symm
    _ = _ := integral_congr_ae (Eventually.of_forall he)

/-- The genuine marked tuple expectation has the same proved selection
factor as the unmarked factorial count, with a literal fixed event. -/
theorem markedExpectation_selection_factor {n q : ℕ} (M : CompactBJRModel S)
    (t : ℝ) (ht : 0 ≤ t) (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (f₀ : Placements n k) (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    (∫ p, markedCount p.1 (AnnealedTypedGraph.graph p) k r Ψ ∂AnnealedTypedGraph.law M t ht n) =
      ((n.descFactorial (∑ i,k i):ℝ)/(∏ i,((k i).factorial:ℝ))) *
        ∫ p, placementObservable hk f₀ r Ψ p ∂AnnealedTypedGraph.law M t ht n := by
  have hh := markedExpectation_mul_factorials_eq_sum_placements (n := n) M t ht k r hk Ψ hΨ
  simp_rw [placementExpectation_eq M t ht k r hk _ f₀ Ψ hΨ] at hh
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_embedding_eq,
    Fintype.card_fin,Fintype.card_sigma] at hh
  simp only [Fintype.card_fin] at hh
  have he := (eq_div_iff (factorialProduct_pos k).ne').mpr hh
  convert he using 1
  ring

end PerronWright.AnnealedMarkedFactorialExchangeability
