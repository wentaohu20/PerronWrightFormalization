import PerronWright.Probability.AnnealedTupleResidualConnectedLawGraphTuple
import PerronWright.Probability.AnnealedTupleResidualConnectedLawProduct

/-!
# Exact weight factorization for the placed labelled graph tuple
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedTupleResidualConnectedLawWeights

open AnnealedGraph ComponentBlocks ComponentCounts SelectedConfiguration
open ExactFactorialExpectation AnnealedResidualFixedBlock FreshTypeAveraging
open AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
open AnnealedTupleResidualConnectedLawGraphTuple

def placedPair {n q : ℕ} {k : Fin q → ℕ} (f : Placements n k)
    (e : Σ i : Fin q, Sym2 (Fin (k i))) : Sym2 (Fin n) :=
  Sym2.map (fun a : Fin (k e.1) ↦ f ⟨e.1,a⟩) e.2

theorem label_injective {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (i : Fin q) : Function.Injective (fun a : Fin (k i) ↦ f ⟨i,a⟩) := by
  intro a b h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (f.injective h)).2

theorem placedPair_injective {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) : Function.Injective (placedPair f) := by
  rintro ⟨i,e⟩ ⟨j,d⟩ h
  have hij : i = j := by
    induction e using Sym2.inductionOn with
    | _ a b =>
      induction d using Sym2.inductionOn with
      | _ c z =>
        change s(f ⟨i,a⟩,f ⟨i,b⟩) = s(f ⟨j,c⟩,f ⟨j,z⟩) at h
        rcases (Sym2.mk_eq_mk_iff (p := (f ⟨i,a⟩,f ⟨i,b⟩))
          (q := (f ⟨j,c⟩,f ⟨j,z⟩))).mp h with h | h
        · exact congrArg Sigma.fst (f.injective (congrArg Prod.fst h))
        · exact congrArg Sigma.fst (f.injective (congrArg Prod.fst h))
  subst j
  have hed : e = d := Sym2.map.injective (label_injective f i) h
  subst d
  rfl

/-- Every component graph edge is placed as one genuine ambient graph edge. -/
def placedGraphEdge {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) (e : Σ i : Fin q, (H i).edgeSet) :
    (tupleGraph f H).edgeSet :=
  ⟨placedPair f ⟨e.1,e.2.val⟩,by
    rcases e with ⟨i,⟨e,he⟩⟩
    induction e using Sym2.inductionOn with
    | _ a b => exact ⟨i,a,b,he,rfl,rfl⟩⟩

theorem placedGraphEdge_bijective {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) : Function.Bijective (placedGraphEdge f H) := by
  constructor
  · rintro ⟨i,e⟩ ⟨j,d⟩ h
    have he := placedPair_injective f (congrArg Subtype.val h)
    have hij : i = j := congrArg Sigma.fst he
    subst j
    have hed : e = d := Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp he).2)
    subst d
    rfl
  · rintro ⟨e,he⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨i,a,b,hab,ha,hb⟩ := he
      refine ⟨⟨i,⟨s(a,b),hab⟩⟩,Subtype.ext ?_⟩
      change s(f ⟨i,a⟩,f ⟨i,b⟩) = s(u,v)
      rw [ha,hb]

def graphEdgesEquiv {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) :
    (Σ i : Fin q, (H i).edgeSet) ≃ (tupleGraph f H).edgeSet :=
  Equiv.ofBijective (placedGraphEdge f H) (placedGraphEdge_bijective f H)

/-- All edge products split into the actual per-component labelled edge products. -/
theorem prod_tupleGraph_edges {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) (W : Sym2 (Fin n) → ℝ) :
    (∏ e ∈ (tupleGraph f H).edgeFinset, W e) =
      ∏ i, ∏ e ∈ (H i).edgeFinset, W (placedPair f ⟨i,e⟩) := by
  unfold SimpleGraph.edgeFinset
  simp_rw [← Finset.prod_set_coe]
  calc
    _ = ∏ e : Σ i : Fin q, (H i).edgeSet, W (placedGraphEdge f H e).val := by
      symm
      exact Fintype.prod_equiv (graphEdgesEquiv f H) _ _ (fun _ ↦ rfl)
    _ = _ := by rw [Fintype.prod_sigma]; rfl

theorem card_tupleGraph_edges {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) :
    (tupleGraph f H).edgeFinset.card = ∑ i, (H i).edgeFinset.card := by
  simp_rw [SimpleGraph.edgeFinset_card]
  rw [← Fintype.card_congr (graphEdgesEquiv f H),Fintype.card_sigma]

/-- The real selected-type integral has now been reindexed from actual
prescribed patterns to the corresponding labelled component graphs. -/
theorem selectedPatternSum_eq_graphTupleSum
    {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]
    {n q : ℕ} (M : CompactBJRModel S) (t : ℝ) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S) :
    selectedPatternSum M t (blocksOfPlacement hk f) k r s₀ =
      ∑ H : GraphTuple k, if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i) then
        (∫ u : {i : Fin n // i ∈ selectedUnion (blocksOfPlacement hk f)} → S,
          Real.exp (-t * internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀ /
            (n : ℝ)) * isolationFactor M t n u ^ (n-(selectedUnion (blocksOfPlacement hk f)).card) *
            internalOddsProduct M t (selectedUnion (blocksOfPlacement hk f)) (tupleGraph f H) u s₀
          ∂Measure.pi (fun _ ↦ M.mu)) else 0 := by
  unfold selectedPatternSum
  exact sum_valid_patterns_eq_sum_eligible_graphTuples hk f r
    (fun G ↦ ∫ u : {i : Fin n // i ∈ selectedUnion (blocksOfPlacement hk f)} → S,
      Real.exp (-t * internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀ /
        (n : ℝ)) * isolationFactor M t n u ^ (n-(selectedUnion (blocksOfPlacement hk f)).card) *
        internalOddsProduct M t (selectedUnion (blocksOfPlacement hk f)) G u s₀
      ∂Measure.pi (fun _ ↦ M.mu))

/-- Placement is a bijection from the labelled component vertices to the
literal selected-union subtype used in the actual probability integral. -/
def selectedVerticesEquiv {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) :
    SelectedVertices k ≃ ↥(selectedUnion (blocksOfPlacement hk f)) :=
  Equiv.ofBijective
    (fun a ↦ ⟨f a,(mem_selectedUnion_placement hk f _).mpr ⟨a,rfl⟩⟩)
    ⟨by
      intro a b h
      exact f.injective (congrArg Subtype.val h),by
      intro u
      obtain ⟨a,ha⟩ := (mem_selectedUnion_placement hk f u.val).mp u.property
      exact ⟨a,Subtype.ext ha⟩⟩

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def blockTypes {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k)
    (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) (i : Fin q) : Fin (k i) → S :=
  fun a ↦ u (selectedVerticesEquiv hk f ⟨i,a⟩)

theorem edgeFactor_placedPair {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) (s₀ : S)
    (i : Fin q) (e : Sym2 (Fin (k i))) :
    M.edgeFactor t (combineTypes (selectedUnion (blocksOfPlacement hk f)) u (fun _ ↦ s₀))
      (placedPair f ⟨i,e⟩) = M.edgeFactor t (blockTypes hk f u i) e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    simp only [placedPair,Sym2.map_mk,CompactBJRModel.edgeFactor_mk]
    have ha : f ⟨i,a⟩ ∈ selectedUnion (blocksOfPlacement hk f) :=
      (mem_selectedUnion_placement hk f _).mpr ⟨⟨i,a⟩,rfl⟩
    have hb : f ⟨i,b⟩ ∈ selectedUnion (blocksOfPlacement hk f) :=
      (mem_selectedUnion_placement hk f _).mpr ⟨⟨i,b⟩,rfl⟩
    simp only [combineTypes,dif_pos ha,dif_pos hb]
    rfl

def selectedGraphWeight {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) (s₀ : S) : ℝ :=
  (∏ v : ↥(selectedUnion (blocksOfPlacement hk f)), Real.exp (-t * M.degreeFunction (u v))) *
    ∏ e ∈ (tupleGraph f H).edgeFinset,
      M.edgeFactor t (combineTypes (selectedUnion (blocksOfPlacement hk f)) u (fun _ ↦ s₀)) e

/-- The selected graph/type weight is exactly the product of the original
labelled graph weights; the vertex and edge changes of coordinates are proved. -/
theorem selectedGraphWeight_eq_product {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) (s₀ : S) :
    selectedGraphWeight M t hk f H u s₀ =
      ∏ i, M.graphWeightIntegrand t (H i) (blockTypes hk f u i) := by
  unfold selectedGraphWeight
  rw [prod_tupleGraph_edges]
  simp_rw [edgeFactor_placedPair]
  have hv : (∏ v : ↥(selectedUnion (blocksOfPlacement hk f)),
      Real.exp (-t * M.degreeFunction (u v))) =
      ∏ i, ∏ a : Fin (k i), Real.exp (-t * M.degreeFunction (blockTypes hk f u i a)) := by
    calc
      _ = ∏ a : SelectedVertices k,
          Real.exp (-t * M.degreeFunction (u (selectedVerticesEquiv hk f a))) := by
        symm
        exact Fintype.prod_equiv (selectedVerticesEquiv hk f) _ _ (fun _ ↦ rfl)
      _ = _ := by rw [Fintype.prod_sigma]; rfl
  rw [hv,← Finset.prod_mul_distrib]
  rfl

theorem presentEdges_tupleGraph_subset_internal {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) (H : GraphTuple k) :
    presentEdges (tupleGraph f H) ⊆ internalEdges (selectedUnion (blocksOfPlacement hk f)) := by
  intro e he
  have hm := (mem_presentEdges _ e).mp he
  rcases e with ⟨e,heDiag⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hs := tupleGraph_adj_selected hk f H hm
    exact (mem_internalEdges _ _).mpr ⟨Or.inl hs.1,hs⟩

/-- The selected internal odds contain precisely the present tuple edges;
all absent pair coordinates contribute the multiplicative identity. -/
theorem internalOddsProduct_eq_tupleGraph_edges {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) (s₀ : S) :
    internalOddsProduct M t (selectedUnion (blocksOfPlacement hk f)) (tupleGraph f H) u s₀ =
      ∏ e ∈ (tupleGraph f H).edgeFinset,
        (Real.exp (M.edgeFactor t
          (combineTypes (selectedUnion (blocksOfPlacement hk f)) u (fun _ ↦ s₀)) e / (n : ℝ)) - 1) := by
  rw [prod_edgeFinset_eq_presentEdges]
  unfold internalOddsProduct
  rw [← Finset.prod_subset (presentEdges_tupleGraph_subset_internal hk f H)]
  · apply Finset.prod_congr rfl
    intro e he
    have ht : assignmentOfGraph (tupleGraph f H) e = true := by
      simpa only [assignmentOfGraph,decide_eq_true_eq] using (mem_presentEdges _ _).mp he
    simp only [ht,if_true,hazard]
  · intro e _ he
    have ht : assignmentOfGraph (tupleGraph f H) e = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have hm : e.val ∈ (tupleGraph f H).edgeSet := by
        simpa only [assignmentOfGraph,decide_eq_true_eq] using h
      exact he ((mem_presentEdges _ _).mpr hm)
    simp only [ht,Bool.false_eq_true,if_false]

def selectedResidual {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) (s₀ : S) : ℝ :=
  Real.exp (t * totalDegree M u - t *
    internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀ / (n : ℝ)) *
    isolationFactor M t n u ^ (n - ∑ i, k i) *
    ∏ e ∈ (tupleGraph f H).edgeFinset,
      normalizedOdds (M.edgeFactor t
        (combineTypes (selectedUnion (blocksOfPlacement hk f)) u (fun _ ↦ s₀)) e / (n : ℝ))

theorem selectedVertexFactor_eq_exp_totalDegree {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) :
    (∏ v : ↥(selectedUnion (blocksOfPlacement hk f)), Real.exp (-t * M.degreeFunction (u v))) =
      Real.exp (-t * totalDegree M u) := by
  rw [← Real.exp_sum]
  congr 1
  unfold totalDegree
  rw [← Finset.mul_sum]

/-- Exact pointwise residual factorization for the selected graph tuple. -/
theorem selected_integrand_weight_factorization {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (H : GraphTuple k) (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) (s₀ : S) :
    Real.exp (-t * internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀ /
      (n : ℝ)) * isolationFactor M t n u ^ (n-(selectedUnion (blocksOfPlacement hk f)).card) *
      internalOddsProduct M t (selectedUnion (blocksOfPlacement hk f)) (tupleGraph f H) u s₀ =
    (n : ℝ)⁻¹ ^ (tupleGraph f H).edgeFinset.card *
      (∏ i, M.graphWeightIntegrand t (H i) (blockTypes hk f u i)) *
        selectedResidual M t hk f H u s₀ := by
  rw [internalOddsProduct_eq_tupleGraph_edges,prod_present_odds_factorization,
    ← selectedGraphWeight_eq_product M t hk f H u s₀,
    selectedUnion_blocksOfPlacement_card]
  unfold selectedGraphWeight selectedResidual
  rw [selectedVertexFactor_eq_exp_totalDegree]
  have he : Real.exp (-t * totalDegree M u) *
      Real.exp (t * totalDegree M u - t *
        internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀ / (n : ℝ)) =
      Real.exp (-t * internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀ / (n : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (n : ℝ)⁻¹ ^ (tupleGraph f H).edgeFinset.card *
        (∏ e ∈ (tupleGraph f H).edgeFinset,
          M.edgeFactor t (combineTypes (selectedUnion (blocksOfPlacement hk f)) u (fun _ ↦ s₀)) e) *
        (Real.exp (-t * totalDegree M u) *
          Real.exp (t * totalDegree M u - t *
            internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀ / (n : ℝ))) *
        isolationFactor M t n u ^ (n-∑ i, k i) *
        (∏ e ∈ (tupleGraph f H).edgeFinset,
          normalizedOdds (M.edgeFactor t
            (combineTypes (selectedUnion (blocksOfPlacement hk f)) u (fun _ ↦ s₀)) e / (n : ℝ))) := by
      rw [he]
      ring
    _ = _ := by ring

theorem card_tupleGraph_eligible {n q : ℕ} {k : Fin q → ℕ}
    (f : Placements n k) (H : GraphTuple k) (r : Fin q → ℕ)
    (hH : ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)) :
    (tupleGraph f H).edgeFinset.card = ∑ i : Fin q, (k i+r i-1) := by
  rw [card_tupleGraph_edges]
  apply Finset.sum_congr rfl
  intro i _
  exact (hH i).2

/-- All graph patterns have now become a product of the literal connected
graph weights times the exact selected residual. -/
theorem selectedPatternSum_eq_weighted_graphTupleSum {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S) :
    selectedPatternSum M t (blocksOfPlacement hk f) k r s₀ =
      (n : ℝ)⁻¹ ^ (∑ i : Fin q, (k i+r i-1)) *
      ∑ H : GraphTuple k, if ∀ i, ConnectedTypeLaw.Eligible (r i) (H i) then
        (∫ u : ↥(selectedUnion (blocksOfPlacement hk f)) → S,
          (∏ i, M.graphWeightIntegrand t (H i) (blockTypes hk f u i)) *
            selectedResidual M t hk f H u s₀ ∂Measure.pi (fun _ ↦ M.mu)) else 0 := by
  rw [selectedPatternSum_eq_graphTupleSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  by_cases hH : ∀ i, ConnectedTypeLaw.Eligible (r i) (H i)
  · simp only [if_pos hH]
    simp_rw [selected_integrand_weight_factorization M t hk f H,
      card_tupleGraph_eligible f H r hH]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    ring
  · simp only [if_neg hH,mul_zero]

end PerronWright.AnnealedTupleResidualConnectedLawWeights
