import PerronWright.Probability.FreshTypeAveraging

/-!
# The actual selected-block event and its fresh-type factor

This file separates the finite edge coordinates of `SelectedConfiguration.Event`
into internal unordered pairs and boundary pairs, and separates the sampled
type coordinates by finite-product Fubini.  The unused types are averaged
exactly, giving the one-fresh-type isolation integral raised to their number.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.AnnealedResidualFixedBlock

open AnnealedGraph SelectedConfiguration FreshTypeAveraging ComponentBlocks

/-- Both vertices of an unordered pair belong to the selected block. -/
def both {n : ℕ} (B : Finset (Fin n)) (e : Sym2 (Fin n)) : Prop :=
  Sym2.lift ⟨fun i j ↦ i ∈ B ∧ j ∈ B, by
    intro i j
    exact propext and_comm⟩ e

@[simp] theorem both_mk {n : ℕ} (B : Finset (Fin n)) (i j : Fin n) :
    both B s(i,j) ↔ i ∈ B ∧ j ∈ B := Iff.rfl

def internalEdges {n : ℕ} (B : Finset (Fin n)) : Finset (Edge n) :=
  (prescribedEdges B).filter (fun e ↦ both B e.val)

def boundaryEdges {n : ℕ} (B : Finset (Fin n)) : Finset (Edge n) :=
  (prescribedEdges B).filter (fun e ↦ ¬both B e.val)

@[simp] theorem mem_internalEdges {n : ℕ} (B : Finset (Fin n)) (e : Edge n) :
    e ∈ internalEdges B ↔ touches B e.val ∧ both B e.val := by
  simp [internalEdges]

@[simp] theorem mem_boundaryEdges {n : ℕ} (B : Finset (Fin n)) (e : Edge n) :
    e ∈ boundaryEdges B ↔ touches B e.val ∧ ¬both B e.val := by
  simp [boundaryEdges]

/-- A selected vertex paired with an unused vertex gives one simple boundary edge. -/
def boundaryEdge {n : ℕ} (B : Finset (Fin n))
    (p : {j : Fin n // j ∉ B} × {i : Fin n // i ∈ B}) : Edge n :=
  ⟨s(p.2.val, p.1.val), by
    intro h
    have heq : p.2.val = p.1.val := Sym2.mk_isDiag_iff.mp h
    exact p.1.property (heq ▸ p.2.property)⟩

theorem boundaryEdge_mem {n : ℕ} (B : Finset (Fin n))
    (p : {j : Fin n // j ∉ B} × {i : Fin n // i ∈ B}) :
    boundaryEdge B p ∈ boundaryEdges B := by
  simp only [mem_boundaryEdges, boundaryEdge, touches_mk, both_mk]
  exact ⟨Or.inl p.2.property, fun h ↦ p.1.property h.2⟩

theorem boundaryEdge_injective {n : ℕ} (B : Finset (Fin n)) :
    Function.Injective (boundaryEdge B) := by
  intro p q heq
  have heq' : s(p.2.val, p.1.val) = s(q.2.val, q.1.val) := congrArg Subtype.val heq
  rcases Sym2.eq_iff.mp heq' with ⟨hi,hj⟩ | ⟨hi,hj⟩
  · exact Prod.ext (Subtype.ext hj) (Subtype.ext hi)
  · exact False.elim (q.1.property (hi ▸ p.2.property))

theorem boundaryEdge_surjective {n : ℕ} (B : Finset (Fin n))
    (e : Edge n) (he : e ∈ boundaryEdges B) :
    ∃ p, boundaryEdge B p = e := by
  rcases e with ⟨e, hdiag⟩
  induction e using Sym2.inductionOn with
  | _ i j =>
    have hb : (i ∈ B ∨ j ∈ B) ∧ ¬(i ∈ B ∧ j ∈ B) :=
      (mem_boundaryEdges B ⟨s(i,j),hdiag⟩).mp he
    by_cases hi : i ∈ B
    · have hj : j ∉ B := fun h ↦ hb.2 ⟨hi,h⟩
      exact ⟨(⟨j,hj⟩,⟨i,hi⟩), Subtype.ext rfl⟩
    · have hj : j ∈ B := hb.1.resolve_left hi
      refine ⟨(⟨i,hi⟩,⟨j,hj⟩), ?_⟩
      apply Subtype.ext
      exact Sym2.eq_swap

/-- Each boundary pair is counted once; there is no orientation factor of two. -/
theorem prod_boundaryEdges {n : ℕ} (B : Finset (Fin n)) (f : Edge n → ℝ) :
    (∏ e ∈ boundaryEdges B, f e) =
      ∏ p : {j : Fin n // j ∉ B} × {i : Fin n // i ∈ B}, f (boundaryEdge B p) := by
  symm
  apply Finset.prod_bij (fun p _ ↦ boundaryEdge B p)
  · intro p _
    exact boundaryEdge_mem B p
  · intro p _ q _ heq
    exact boundaryEdge_injective B heq
  · intro e he
    obtain ⟨p,hp⟩ := boundaryEdge_surjective B e he
    exact ⟨p,Finset.mem_univ _,hp⟩
  · intro p _
    rfl

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Assemble a sampled type vector from its selected and unused coordinates. -/
def combineTypes {n : ℕ} (B : Finset (Fin n))
    (u : {i : Fin n // i ∈ B} → S) (v : {i : Fin n // i ∉ B} → S) : Fin n → S :=
  fun i ↦ if hi : i ∈ B then u ⟨i,hi⟩ else v ⟨i,hi⟩

omit [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem combineTypes_inside {n : ℕ} (B : Finset (Fin n))
    (u : {i : Fin n // i ∈ B} → S) (v : {i : Fin n // i ∉ B} → S)
    (i : {i : Fin n // i ∈ B}) : combineTypes B u v i.val = u i := by
  simp [combineTypes,i.property]

omit [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem combineTypes_outside {n : ℕ} (B : Finset (Fin n))
    (u : {i : Fin n // i ∈ B} → S) (v : {i : Fin n // i ∉ B} → S)
    (i : {i : Fin n // i ∉ B}) : combineTypes B u v i.val = v i := by
  simp [combineTypes,i.property]

theorem hazard_internal_independent {n : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (B : Finset (Fin n)) (u : {i : Fin n // i ∈ B} → S)
    (v w : {i : Fin n // i ∉ B} → S) (e : Edge n)
    (he : e ∈ internalEdges B) :
    hazard M t (combineTypes B u v) e = hazard M t (combineTypes B u w) e := by
  rcases e with ⟨e,hdiag⟩
  induction e using Sym2.inductionOn with
  | _ i j =>
    have hb : i ∈ B ∧ j ∈ B := ((mem_internalEdges B ⟨s(i,j),hdiag⟩).mp he).2
    simp only [hazard, CompactBJRModel.edgeFactor_mk, combineTypes, dif_pos hb.1, dif_pos hb.2]

theorem edgeFactor_internal_independent {n : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (B : Finset (Fin n)) (u : {i : Fin n // i ∈ B} → S)
    (v w : {i : Fin n // i ∉ B} → S) (e : Edge n)
    (he : e ∈ internalEdges B) :
    M.edgeFactor t (combineTypes B u v) e.val =
      M.edgeFactor t (combineTypes B u w) e.val := by
  rcases e with ⟨e,hdiag⟩
  induction e using Sym2.inductionOn with
  | _ i j =>
    have hb : i ∈ B ∧ j ∈ B := ((mem_internalEdges B ⟨s(i,j),hdiag⟩).mp he).2
    simp only [CompactBJRModel.edgeFactor_mk, combineTypes, dif_pos hb.1, dif_pos hb.2]

theorem assignment_boundary_false {n : ℕ} (B : Finset (Fin n))
    (H : SimpleGraph (Fin n)) (hH : Isolated H (B : Set (Fin n)))
    (p : {j : Fin n // j ∉ B} × {i : Fin n // i ∈ B}) :
    assignmentOfGraph H (boundaryEdge B p) = false := by
  have ha : ¬H.Adj p.2.val p.1.val := fun h ↦ p.1.property (hH _ p.2.property _ h)
  simp [assignmentOfGraph,boundaryEdge,ha]

/-- Internal configuration probability with irrelevant unused types filled
by any base type.  The following theorem removes that arbitrary filling. -/
def internalBlockProbability {n : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (B : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (u : {i : Fin n // i ∈ B} → S) (s₀ : S) : ℝ :=
  ∏ e ∈ internalEdges B,
    IndependentEdges.edgeMass (hazard M t (combineTypes B u (fun _ ↦ s₀)) e)
      (assignmentOfGraph H e)

theorem internalBlockProbability_filling_independent {n : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (B : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (u : {i : Fin n // i ∈ B} → S) (s₀ s₁ : S) :
    internalBlockProbability M t B H u s₀ = internalBlockProbability M t B H u s₁ := by
  unfold internalBlockProbability
  apply Finset.prod_congr rfl
  intro e he
  rw [hazard_internal_independent M t B u (fun _ ↦ s₀) (fun _ ↦ s₁) e he]

/-- Exact factorization of the actual selected-block edge constraint product.
The right factor uses every selected-to-unused pair exactly once. -/
theorem prescribed_probability_split {n : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (B : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (hH : Isolated H (B : Set (Fin n)))
    (u : {i : Fin n // i ∈ B} → S) (v : {i : Fin n // i ∉ B} → S) (s₀ : S) :
    (∏ e ∈ prescribedEdges B,
      IndependentEdges.edgeMass (hazard M t (combineTypes B u v) e) (assignmentOfGraph H e)) =
      internalBlockProbability M t B H u s₀ * boundaryAbsence M t n u v := by
  rw [← Finset.prod_filter_mul_prod_filter_not (prescribedEdges B)
    (fun e ↦ both B e.val)]
  change (∏ e ∈ internalEdges B, _) * (∏ e ∈ boundaryEdges B, _) = _
  congr 1
  · unfold internalBlockProbability
    apply Finset.prod_congr rfl
    intro e he
    rw [hazard_internal_independent M t B u v (fun _ ↦ s₀) e he]
  · rw [prod_boundaryEdges, Fintype.prod_prod_type]
    unfold boundaryAbsence
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro i _
    rw [assignment_boundary_false B H hH]
    simp only [IndependentEdges.edgeMass_false, hazard, boundaryEdge,
      CompactBJRModel.edgeFactor_mk, combineTypes_inside, combineTypes_outside]

/-- Actual block constraints averaged over the unused i.i.d. type coordinates. -/
theorem integrate_unused_prescribed_probability {n : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (B : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (hH : Isolated H (B : Set (Fin n)))
    (u : {i : Fin n // i ∈ B} → S) (s₀ : S) :
    (∫ v : {i : Fin n // i ∉ B} → S,
      (∏ e ∈ prescribedEdges B,
        IndependentEdges.edgeMass (hazard M t (combineTypes B u v) e)
          (assignmentOfGraph H e)) ∂Measure.pi (fun _ ↦ M.mu)) =
      internalBlockProbability M t B H u s₀ * isolationFactor M t n u ^ (n-B.card) := by
  simp_rw [prescribed_probability_split M t B H hH u _ s₀]
  rw [integral_const_mul, integral_boundaryAbsence]
  congr 2
  have hc : Fintype.card {i : Fin n // i ∉ B} = n-B.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_subtype_compl (fun i : Fin n ↦ i ∈ B)
  exact hc

/-- The selected-configuration finite product is continuous in all sampled types. -/
theorem prescribed_probability_continuous {n : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (B : Finset (Fin n)) (H : SimpleGraph (Fin n)) :
    Continuous (fun x : Fin n → S ↦ ∏ e ∈ prescribedEdges B,
      IndependentEdges.edgeMass (hazard M t x e) (assignmentOfGraph H e)) := by
  apply continuous_finsetProd
  intro e _
  have hz : Continuous (fun x : Fin n → S ↦ hazard M t x e) :=
    (M.edgeFactor_continuous t e.val).div_const _
  cases assignmentOfGraph H e
  · exact hz.neg.rexp
  · exact continuous_const.sub hz.neg.rexp

/-- Exact probability of the actual annealed selected-block event, after
integrating away every unused sampled type.  The only filling type on the
right is arbitrary and has no effect on its internal-edge probability. -/
theorem probability_event_averaged {n : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (ht : 0 ≤ t) (B : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (hH : Isolated H (B : Set (Fin n))) (s₀ : S) :
    (∫ a : Assignment n, if Event B H a then (1 : ℝ) else 0
      ∂(AnnealedGraph.pmf M t ht n).toMeasure) =
      ∫ u : {i : Fin n // i ∈ B} → S,
        internalBlockProbability M t B H u s₀ * isolationFactor M t n u ^ (n-B.card)
        ∂Measure.pi (fun _ ↦ M.mu) := by
  let F : (Fin n → S) → ℝ := fun x ↦ ∏ e ∈ prescribedEdges B,
    IndependentEdges.edgeMass (hazard M t x e) (assignmentOfGraph H e)
  have hF : Integrable F (typeLaw M n) :=
    (prescribed_probability_continuous M t B H).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  let E := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n ↦ S) (fun i ↦ i ∈ B)
  have hmp := (measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin n ↦ M.mu) (fun i ↦ i ∈ B)).symm
  have hpi :
      @Measure.pi {i : Fin n // i ∈ B} (fun _ ↦ S) (Finset.Subtype.fintype B)
        (fun _ ↦ inferInstance) (fun _ ↦ M.mu) =
      @Measure.pi {i : Fin n // i ∈ B} (fun _ ↦ S) (Subtype.fintype (fun i ↦ i ∈ B))
        (fun _ ↦ inferInstance) (fun _ ↦ M.mu) := by
    exact congrArg (fun inst : Fintype {i : Fin n // i ∈ B} ↦
      @Measure.pi {i : Fin n // i ∈ B} (fun _ ↦ S) inst
        (fun _ ↦ inferInstance) (fun _ ↦ M.mu)) (Subsingleton.elim _ _)
  have hFi : Integrable
      (fun p : ({i : Fin n // i ∈ B} → S) × ({i : Fin n // i ∉ B} → S) ↦
        F (combineTypes B p.1 p.2))
      ((Measure.pi (fun _ : {i : Fin n // i ∈ B} ↦ M.mu)).prod
        (Measure.pi (fun _ : {i : Fin n // i ∉ B} ↦ M.mu))) := by
    convert (hmp.integrable_comp_emb E.symm.measurableEmbedding).mpr hF using 1
    · funext p
      congr 1
    · rw [hpi]
  calc
    _ = ∫ x : Fin n → S, F x ∂typeLaw M n :=
      expectation_prescribed M t ht n (prescribedEdges B) (assignmentOfGraph H)
    _ = ∫ p : ({i : Fin n // i ∈ B} → S) × ({i : Fin n // i ∉ B} → S),
        F (combineTypes B p.1 p.2)
        ∂((Measure.pi (fun _ : {i : Fin n // i ∈ B} ↦ M.mu)).prod
          (Measure.pi (fun _ : {i : Fin n // i ∉ B} ↦ M.mu))) :=
      by
        convert (hmp.integral_comp' F).symm using 1
        congr 1
        rw [hpi]
    _ = ∫ u : {i : Fin n // i ∈ B} → S,
        (∫ v : {i : Fin n // i ∉ B} → S, F (combineTypes B u v)
          ∂Measure.pi (fun _ ↦ M.mu)) ∂Measure.pi (fun _ ↦ M.mu) :=
      integral_prod _ hFi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact integrate_unused_prescribed_probability M t B H hH u s₀

/-- The same exact formula on the literal simple-graph sample space. -/
theorem probability_induce_and_isolated_averaged {n : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (B : Finset (Fin n))
    (H : SimpleGraph (Fin n)) (hH : Isolated H (B : Set (Fin n))) (s₀ : S) :
    (∫ G : SimpleGraph (Fin n),
      if G.induce (B : Set (Fin n)) = H.induce (B : Set (Fin n)) ∧
        Isolated G (B : Set (Fin n)) then (1 : ℝ) else 0
      ∂AnnealedGraph.law M t ht n) =
      ∫ u : {i : Fin n // i ∈ B} → S,
        internalBlockProbability M t B H u s₀ * isolationFactor M t n u ^ (n-B.card)
        ∂Measure.pi (fun _ ↦ M.mu) := by
  calc
    _ = ∫ a : Assignment n,
        if (toGraph a).induce (B : Set (Fin n)) = H.induce (B : Set (Fin n)) ∧
          Isolated (toGraph a) (B : Set (Fin n)) then (1 : ℝ) else 0
        ∂(AnnealedGraph.pmf M t ht n).toMeasure := by
      rw [AnnealedGraph.law_expectation_eq_type_integral]
      exact (AnnealedGraph.expectation_eq_type_integral M t ht n
        (fun G ↦ if G.induce (B : Set (Fin n)) = H.induce (B : Set (Fin n)) ∧
          Isolated G (B : Set (Fin n)) then (1 : ℝ) else 0)).symm
    _ = ∫ a : Assignment n, if Event B H a then (1 : ℝ) else 0
        ∂(AnnealedGraph.pmf M t ht n).toMeasure := by
      apply integral_congr_ae
      filter_upwards [] with a
      rw [event_iff_induce_and_isolated B H hH a]
      split_ifs <;> rfl
    _ = _ := probability_event_averaged M t ht B H hH s₀

/-- The internal pair weight of the selected block, with each unordered
non-diagonal pair counted exactly once.  Its unused filling has no effect. -/
def internalPairWeightOn {n : ℕ} (M : CompactBJRModel S)
    (B : Finset (Fin n)) (u : {i : Fin n // i ∈ B} → S) (s₀ : S) : ℝ :=
  ∑ e ∈ internalEdges B, M.edgeFactor 1 (combineTypes B u (fun _ ↦ s₀)) e.val

theorem internalPairWeightOn_filling_independent {n : ℕ}
    (M : CompactBJRModel S) (B : Finset (Fin n))
    (u : {i : Fin n // i ∈ B} → S) (s₀ s₁ : S) :
    internalPairWeightOn M B u s₀ = internalPairWeightOn M B u s₁ := by
  unfold internalPairWeightOn
  apply Finset.sum_congr rfl
  intro e he
  exact edgeFactor_internal_independent M 1 B u (fun _ ↦ s₀) (fun _ ↦ s₁) e he

/-- Exact odds over present selected internal edges. -/
def internalOddsProduct {n : ℕ} (M : CompactBJRModel S) (t : ℝ)
    (B : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (u : {i : Fin n // i ∈ B} → S) (s₀ : S) : ℝ :=
  ∏ e ∈ internalEdges B,
    if assignmentOfGraph H e then
      Real.exp (hazard M t (combineTypes B u (fun _ ↦ s₀)) e) - 1 else 1

theorem internalOddsProduct_filling_independent {n : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (B : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (u : {i : Fin n // i ∈ B} → S) (s₀ s₁ : S) :
    internalOddsProduct M t B H u s₀ = internalOddsProduct M t B H u s₁ := by
  unfold internalOddsProduct
  apply Finset.prod_congr rfl
  intro e he
  rw [hazard_internal_independent M t B u (fun _ ↦ s₀) (fun _ ↦ s₁) e he]

theorem internalBlockProbability_odds {n : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (B : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (u : {i : Fin n // i ∈ B} → S) (s₀ : S) :
    internalBlockProbability M t B H u s₀ =
      Real.exp (-t * internalPairWeightOn M B u s₀ / (n : ℝ)) *
        internalOddsProduct M t B H u s₀ := by
  unfold internalBlockProbability internalOddsProduct
  rw [IndependentEdges.prescribedMass_odds]
  congr 2
  unfold hazard internalPairWeightOn
  simp_rw [M.edgeFactor_scale t]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  ring

/-- Literal compact annealed selected-component configuration formula.
The finite-graph event on the left is already tied to the actual normalized
annealed law, while the right has exactly the paper's fresh-type power. -/
theorem probability_event_averaged_odds {n : ℕ}
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (B : Finset (Fin n))
    (H : SimpleGraph (Fin n)) (hH : Isolated H (B : Set (Fin n))) (s₀ : S) :
    (∫ a : Assignment n, if Event B H a then (1 : ℝ) else 0
      ∂(AnnealedGraph.pmf M t ht n).toMeasure) =
      ∫ u : {i : Fin n // i ∈ B} → S,
        Real.exp (-t * internalPairWeightOn M B u s₀ / (n : ℝ)) *
          isolationFactor M t n u ^ (n-B.card) * internalOddsProduct M t B H u s₀
        ∂Measure.pi (fun _ ↦ M.mu) := by
  rw [probability_event_averaged M t ht B H hH s₀]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [internalBlockProbability_odds]
  ring

end PerronWright.AnnealedResidualFixedBlock
