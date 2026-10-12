import PerronWright.Probability.AnnealedMarkedFactorialExchangeability

/-! # Exact fresh-type averaging with an actual joint empirical mark test -/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedMarkedFactorialPattern

open AnnealedGraph SelectedConfiguration ComponentBlocks ComponentCounts
  ExactFactorialExpectation FreshTypeAveraging AnnealedResidualFixedBlock
  AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
  AnnealedTupleResidualConnectedLawWeights AnnealedTupleResidualConnectedLawCoordinates
  AnnealedMarkedFactorialCounting AnnealedMarkedFactorialExchangeability EmpiricalMarkConcentration

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def selectedMarks {n q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i) (f : Placements n k)
    (u : ↥(selectedUnion (blocksOfPlacement hk f)) → S) : Fin q → ProbabilityMeasure S :=
  fun i ↦ typesMark (hk i) (blockTypes hk f u i)

theorem selectedMarks_continuous {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) : Continuous (selectedMarks (S := S) hk f) := by
  apply continuous_pi
  intro i
  exact (typesMark_continuous (hk i)).comp
    (continuous_pi (fun a ↦ continuous_apply (selectedVerticesEquiv hk f ⟨i,a⟩)))

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
theorem selectedMarks_restrict {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) (x : Fin n → S) :
    selectedMarks hk f (fun v ↦ x v.val) = placementMarks hk f x := rfl

/-- A selected continuous observable factors through the true finite
product Fubini decomposition.  All unused sampled types are integrated. -/
theorem weighted_prescribed_probability_integral {n : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (B : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (hH : Isolated H (B : Set (Fin n))) (s₀ : S)
    (W : (↥B → S) → ℝ) (hW : Continuous W) :
    (∫ x : Fin n → S, (∏ e ∈ prescribedEdges B,
      IndependentEdges.edgeMass (hazard M t x e) (assignmentOfGraph H e)) * W (fun v ↦ x v.val)
        ∂typeLaw M n) =
      ∫ u : ↥B → S, (Real.exp (-t * internalPairWeightOn M B u s₀/(n:ℝ)) *
        isolationFactor M t n u^(n-B.card) * internalOddsProduct M t B H u s₀) * W u
        ∂Measure.pi (fun _ ↦ M.mu) := by
  let F : (Fin n → S) → ℝ := fun x ↦ (∏ e ∈ prescribedEdges B,
    IndependentEdges.edgeMass (hazard M t x e) (assignmentOfGraph H e)) * W (fun v ↦ x v.val)
  have hFc : Continuous F := (prescribed_probability_continuous M t B H).mul
    (hW.comp (continuous_pi (fun v ↦ continuous_apply v.val)))
  have hFi : Integrable F (typeLaw M n) := hFc.integrable_of_hasCompactSupport isClosed_closure.isCompact
  let E := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n ↦ S) (fun i ↦ i ∈ B)
  have hmp := (measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n ↦ M.mu) (fun i ↦ i ∈ B)).symm
  have hpi :
      @Measure.pi {i : Fin n // i ∈ B} (fun _ ↦ S) (Finset.Subtype.fintype B)
        (fun _ ↦ inferInstance) (fun _ ↦ M.mu) =
      @Measure.pi {i : Fin n // i ∈ B} (fun _ ↦ S) (Subtype.fintype (fun i ↦ i ∈ B))
        (fun _ ↦ inferInstance) (fun _ ↦ M.mu) := by
    exact congrArg (fun inst : Fintype {i : Fin n // i ∈ B} ↦
      @Measure.pi {i : Fin n // i ∈ B} (fun _ ↦ S) inst
        (fun _ ↦ inferInstance) (fun _ ↦ M.mu)) (Subsingleton.elim _ _)
  have hi : Integrable
      (fun p : (↥B → S) × ({i : Fin n // i ∉ B} → S) ↦ F (combineTypes B p.1 p.2))
      ((Measure.pi (fun _ : ↥B ↦ M.mu)).prod (Measure.pi (fun _ : {i : Fin n // i ∉ B} ↦ M.mu))) := by
    convert (hmp.integrable_comp_emb E.symm.measurableEmbedding).mpr hFi using 1
    · funext p
      congr 1
    · rw [hpi]
  calc
    _ = ∫ p : (↥B → S) × ({i : Fin n // i ∉ B} → S), F (combineTypes B p.1 p.2)
        ∂((Measure.pi (fun _ : ↥B ↦ M.mu)).prod (Measure.pi (fun _ : {i : Fin n // i ∉ B} ↦ M.mu))) := by
      convert (hmp.integral_comp' F).symm using 1
      congr 1
      rw [hpi]
    _ = ∫ u : ↥B → S, (∫ v : {i : Fin n // i ∉ B} → S, F (combineTypes B u v)
        ∂Measure.pi (fun _ ↦ M.mu)) ∂Measure.pi (fun _ ↦ M.mu) := integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      have hw (v : {i : Fin n // i ∉ B} → S) :
          W (fun i : ↥B ↦ combineTypes B u v i.val) = W u := by
        congr 1
        funext i
        exact combineTypes_inside B u v i
      dsimp only [F]
      simp_rw [hw]
      rw [integral_mul_const,integrate_unused_prescribed_probability M t B H hH u s₀,
        internalBlockProbability_odds]
      ring

def markedPatternSum {n q : ℕ} (M : CompactBJRModel S) (t : ℝ) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) : ℝ :=
  ∑ c : prescribedEdges (selectedUnion (blocksOfPlacement hk f)) → Bool,
    if ∀ i, MatchesBlock (patternGraph (blocksOfPlacement hk f) c) (blockOfPlacement f i) (k i) (r i) then
      (∫ u : ↥(selectedUnion (blocksOfPlacement hk f)) → S,
        (Real.exp (-t * internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀/(n:ℝ)) *
          isolationFactor M t n u^(n-(selectedUnion (blocksOfPlacement hk f)).card) *
          internalOddsProduct M t (selectedUnion (blocksOfPlacement hk f)) (patternGraph (blocksOfPlacement hk f) c) u s₀) *
            Ψ (selectedMarks hk f u) ∂Measure.pi (fun _ ↦ M.mu)) else 0

/-- The fixed actual typed-graph block event becomes its actual finite
selected pattern sum, including the unchanged component empirical marks. -/
theorem placementExpectation_eq_markedPatternSum {n q : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (Ψ : (Fin q → ProbabilityMeasure S) → ℝ) (hΨ : Continuous Ψ) :
    (∫ p, placementObservable hk f r Ψ p ∂AnnealedTypedGraph.law M t ht n) =
      markedPatternSum M t k r hk f s₀ Ψ := by
  let B := blocksOfPlacement hk f
  let P (c : prescribedEdges (selectedUnion B) → Bool) (x : Fin n → S) :=
    (∏ e ∈ prescribedEdges (selectedUnion B),
      IndependentEdges.edgeMass (hazard M t x e) (assignmentOfGraph (patternGraph B c) e)) * Ψ (placementMarks hk f x)
  have hp (c : prescribedEdges (selectedUnion B) → Bool) : Continuous (P c) :=
    (prescribed_probability_continuous M t (selectedUnion B) (patternGraph B c)).mul
      (hΨ.comp (placementMarks_continuous hk f))
  have hpoint (x : Fin n → S) :
      (∑ a : Assignment n, conditionalMass M t x a * placementObservable hk f r Ψ (x,a)) =
      ∑ c : prescribedEdges (selectedUnion B) → Bool,
        if ∀ i, MatchesBlock (patternGraph B c) (blockOfPlacement f i) (k i) (r i) then P c x else 0 := by
    have hlocal (a : Assignment n) : placementObservable hk f r Ψ (x,a) =
        placementObservable hk f r Ψ (x,IndependentEdges.extend (prescribedEdges (selectedUnion B))
          (IndependentEdges.restrict (prescribedEdges (selectedUnion B)) a)) :=
      if_congr (matchesTuple_local B k r a) rfl rfl
    rw [show conditionalMass M t x = IndependentEdges.mass (hazard M t x) from rfl,
      IndependentEdges.sum_mass_mul_local _ _ _ hlocal]
    apply Finset.sum_congr rfl
    intro c _
    simp only [placementObservable,AnnealedTypedGraph.graph,P,patternGraph,assignmentOfGraph_toGraph]
    split_ifs <;> simp only [mul_zero]
  rw [typedExpectation_eq_typeIntegral M t ht _ (placementObservable_continuous_slice hk f r Ψ hΨ)]
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro c _
    by_cases hc : ∀ i, MatchesBlock (patternGraph B c) (blockOfPlacement f i) (k i) (r i)
    · simp only [B] at hc
      simp only [B,if_pos hc]
      have hh := weighted_prescribed_probability_integral M t (selectedUnion B) (patternGraph B c)
        (isolated_selectedUnion _ B k r hc) s₀ (fun u ↦ Ψ (selectedMarks hk f u))
          (hΨ.comp (selectedMarks_continuous hk f))
      simpa only [B,P,selectedMarks_restrict] using hh
    · simp only [B] at hc
      simp only [B,if_neg hc,integral_zero]
  · intro c _
    by_cases hc : ∀ i, MatchesBlock (patternGraph B c) (blockOfPlacement f i) (k i) (r i)
    · simp only [if_pos hc]
      exact (hp c).integrable_of_hasCompactSupport isClosed_closure.isCompact
    · simp only [if_neg hc]
      exact integrable_zero _ _ _

end PerronWright.AnnealedMarkedFactorialPattern
