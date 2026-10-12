import PerronWright.Probability.SelectedConfiguration
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Exact averaging over unselected sampled types

The one-fresh-type factor is the literal Laplace integral of the exposure
to the selected types.  This file proves, by finite-product Fubini, that
averaging the absent boundary edges over independent unselected types
produces its `(n-k)`-th power.  It also gives the exact exponential-odds
formula for a fixed internal labelled graph, without an asymptotic or an
enumeration assumption.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.FreshTypeAveraging

open AnnealedGraph IndependentEdges

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Kernel exposure of a fresh type to a fixed finite list of selected types. -/
def exposure {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (x : I → S) (y : S) : ℝ := ∑ i, M.kernel (x i) y

/-- Total degree of the fixed selected type list. -/
def totalDegree {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (x : I → S) : ℝ := ∑ i, M.degreeFunction (x i)

theorem exposure_continuous {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (x : I → S) : Continuous (exposure M x) := by
  apply continuous_finsetSum
  intro i _
  exact M.kernel.continuous_left (x i)

theorem exposure_integrable {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (x : I → S) : Integrable (exposure M x) M.mu :=
  (exposure_continuous M x).integrable_of_hasCompactSupport isClosed_closure.isCompact

theorem exposure_nonneg {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (x : I → S) (y : S) : 0 ≤ exposure M x y :=
  Finset.sum_nonneg (fun i _ ↦ M.kernel.nonneg (x i) y)

/-- The mean fresh exposure is exactly the total selected degree. -/
theorem integral_exposure {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (x : I → S) : (∫ y, exposure M x y ∂M.mu) = totalDegree M x := by
  unfold exposure totalDegree CompactBJRModel.degreeFunction
  rw [integral_finsetSum]
  · simp only [ContinuousKernel.degreeMap_apply, ContinuousKernel.degree]
  · intro i _
    exact M.kernel.integrable_left M.mu (x i)

/-- Probability of absent edges to one fresh vertex, conditional on its type. -/
def freshAbsence {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (t : ℝ) (n : ℕ) (x : I → S) (y : S) : ℝ :=
  Real.exp (-t * exposure M x y / (n : ℝ))

/-- The paper's literal one-fresh-type isolation factor `A_n(x)`. -/
def isolationFactor {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (t : ℝ) (n : ℕ) (x : I → S) : ℝ :=
  ∫ y, freshAbsence M t n x y ∂M.mu

theorem freshAbsence_continuous {I : Type*} [Fintype I]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ) (x : I → S) :
    Continuous (freshAbsence M t n x) :=
  ((continuous_const.mul (exposure_continuous M x)).div_const _).rexp

theorem freshAbsence_integrable {I : Type*} [Fintype I]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ) (x : I → S) :
    Integrable (freshAbsence M t n x) M.mu :=
  (freshAbsence_continuous M t n x).integrable_of_hasCompactSupport
    isClosed_closure.isCompact

theorem isolationFactor_pos {I : Type*} [Fintype I]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ) (x : I → S) :
    0 < isolationFactor M t n x := by
  unfold isolationFactor
  apply integral_pos_iff_support_of_nonneg (fun _ ↦ (Real.exp_pos _).le)
    (freshAbsence_integrable M t n x) |>.mpr
  have hs : Function.support (freshAbsence M t n x) = Set.univ := by
    ext y
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (Real.exp_pos _).ne'
  change 0 < M.mu (Function.support (freshAbsence M t n x))
  rw [hs]
  simp

theorem isolationFactor_le_one {I : Type*} [Fintype I]
    (M : CompactBJRModel S) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (x : I → S) :
    isolationFactor M t n x ≤ 1 := by
  calc
    isolationFactor M t n x ≤ ∫ _ : S, (1 : ℝ) ∂M.mu := by
      apply integral_mono (freshAbsence_integrable M t n x) (integrable_const 1)
      intro y
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (exposure_nonneg M x y))
        (Nat.cast_nonneg n)
    _ = 1 := by simp

/-- The probability of no selected-to-unselected edges for a fixed fresh list. -/
def boundaryAbsence {I J : Type*} [Fintype I] [Fintype J]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ) (x : I → S) (y : J → S) : ℝ :=
  ∏ j, ∏ i, Real.exp (-(t * M.kernel (x i) (y j) / (n : ℝ)))

theorem boundaryAbsence_eq_product {I J : Type*} [Fintype I] [Fintype J]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ) (x : I → S) (y : J → S) :
    boundaryAbsence M t n x y = ∏ j, freshAbsence M t n x (y j) := by
  unfold boundaryAbsence freshAbsence exposure
  apply Finset.prod_congr rfl
  intro j _
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  ring

theorem boundaryAbsence_integrable {I J : Type*} [Fintype I] [Fintype J]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ) (x : I → S) :
    Integrable (boundaryAbsence (J := J) M t n x) (Measure.pi (fun _ : J ↦ M.mu)) := by
  change Integrable (fun y : J → S ↦ boundaryAbsence M t n x y) _
  simp_rw [boundaryAbsence_eq_product]
  exact Integrable.fintype_prod (fun _ ↦ freshAbsence_integrable M t n x)

/-- Exact finite-product Fubini: each independent unused type contributes
the same literal Laplace factor, not a fixed-profile exponential. -/
theorem integral_boundaryAbsence {I J : Type*} [Fintype I] [Fintype J]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ) (x : I → S) :
    (∫ y : J → S, boundaryAbsence M t n x y ∂Measure.pi (fun _ : J ↦ M.mu)) =
      isolationFactor M t n x ^ Fintype.card J := by
  simp_rw [boundaryAbsence_eq_product]
  exact integral_fintype_prod_eq_pow (freshAbsence M t n x)

/-- The literal `(n-k)`-th power in the annealed component formula. -/
theorem integral_unused_types (M : CompactBJRModel S) (t : ℝ)
    (n k : ℕ) (x : Fin k → S) :
    (∫ y : Fin (n-k) → S, boundaryAbsence M t n x y ∂typeLaw M (n-k)) =
      isolationFactor M t n x ^ (n-k) := by
  simpa only [Fintype.card_fin] using integral_boundaryAbsence (J := Fin (n-k)) M t n x

/-- This product is the exact event probability under independent Boolean
boundary edges, so the preceding integral really averages an isolation event. -/
theorem conditional_boundary_probability {I J : Type*} [Fintype I] [Fintype J]
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (n : ℕ)
    (x : I → S) (y : J → S) :
    (∫ a : (J × I) → Bool, if ∀ e, a e = false then (1 : ℝ) else 0
      ∂(IndependentEdges.pmf
        (fun e : J × I ↦ t * M.kernel (x e.2) (y e.1) / (n : ℝ))
        (fun _e ↦ div_nonneg (mul_nonneg ht (M.kernel.nonneg _ _))
          (Nat.cast_nonneg n))).toMeasure) = boundaryAbsence M t n x y := by
  have h := IndependentEdges.integral_agreesOn
    (fun e : J × I ↦ t * M.kernel (x e.2) (y e.1) / (n : ℝ))
    (fun e ↦ div_nonneg (mul_nonneg ht (M.kernel.nonneg _ _)) (Nat.cast_nonneg n))
    Finset.univ (fun _ ↦ false)
  simpa only [AgreesOn, Finset.mem_univ, forall_true_left, edgeMass_false,
    Fintype.prod_prod_type, boundaryAbsence] using h

/-- The actual independent boundary-edge probability averaged over exactly
`n-k` independent unused sampled types. -/
theorem averaged_boundary_probability (M : CompactBJRModel S)
    (t : ℝ) (ht : 0 ≤ t) (n k : ℕ) (x : Fin k → S) :
    (∫ y : Fin (n-k) → S,
      (∫ a : (Fin (n-k) × Fin k) → Bool,
        if ∀ e, a e = false then (1 : ℝ) else 0
        ∂(IndependentEdges.pmf
          (fun e ↦ t * M.kernel (x e.2) (y e.1) / (n : ℝ))
          (fun _e ↦ div_nonneg (mul_nonneg ht (M.kernel.nonneg _ _))
            (Nat.cast_nonneg n))).toMeasure)
      ∂typeLaw M (n-k)) = isolationFactor M t n x ^ (n-k) := by
  calc
    _ = ∫ y : Fin (n-k) → S, boundaryAbsence M t n x y ∂typeLaw M (n-k) := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact conditional_boundary_probability M t ht n x y
    _ = _ := integral_unused_types M t n k x

/-- The non-diagonal internal pair weight `P_int(x)`.  Each unordered pair
is counted once, by the same edge coordinates as the actual graph law. -/
def internalPairWeight (M : CompactBJRModel S) {k : ℕ} (x : Fin k → S) : ℝ :=
  ∑ e : Edge k, M.edgeFactor 1 x e.val

/-- Internal hazards use the ambient size `n`, even when the selected graph
has only `k` vertices. -/
def internalHazard (M : CompactBJRModel S) (t : ℝ) (n : ℕ)
    {k : ℕ} (x : Fin k → S) (e : Edge k) : ℝ :=
  M.edgeFactor t x e.val / (n : ℝ)

theorem internalHazard_nonneg (M : CompactBJRModel S) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) {k : ℕ} (x : Fin k → S) (e : Edge k) :
    0 ≤ internalHazard M t n x e :=
  div_nonneg (M.edgeFactor_nonneg t ht x e.val) (Nat.cast_nonneg n)

/-- Exact probability of the specified internal simple graph at ambient size `n`. -/
def internalGraphProbability (M : CompactBJRModel S) (t : ℝ) (n : ℕ)
    {k : ℕ} (x : Fin k → S) (H : SimpleGraph (Fin k)) : ℝ :=
  IndependentEdges.mass (internalHazard M t n x) (assignmentOfGraph H)

/-- Present graph edges are a finite subset of the non-diagonal pair coordinates. -/
def presentEdges {k : ℕ} (H : SimpleGraph (Fin k)) : Finset (Edge k) :=
  Finset.univ.filter (fun e ↦ e.val ∈ H.edgeSet)

@[simp] theorem mem_presentEdges {k : ℕ} (H : SimpleGraph (Fin k)) (e : Edge k) :
    e ∈ presentEdges H ↔ e.val ∈ H.edgeSet := by
  simp [presentEdges]

/-- Move a product over graph edges to its literal Boolean edge coordinates. -/
theorem prod_edgeFinset_eq_presentEdges {k : ℕ} (H : SimpleGraph (Fin k))
    (f : Sym2 (Fin k) → ℝ) :
    (∏ e ∈ H.edgeFinset, f e) = ∏ e ∈ presentEdges H, f e.val := by
  apply Finset.prod_bij (fun e he ↦ ⟨e, H.not_isDiag_of_mem_edgeFinset he⟩)
  · intro e he
    simpa only [mem_presentEdges] using SimpleGraph.mem_edgeFinset.mp he
  · intro e he e' he' heq
    exact congrArg Subtype.val heq
  · intro e he
    refine ⟨e.val, SimpleGraph.mem_edgeFinset.mpr ((mem_presentEdges H e).mp he), ?_⟩
    exact Subtype.ext rfl
  · intro e he
    rfl

theorem sum_internalHazard (M : CompactBJRModel S) (t : ℝ) (n : ℕ)
    {k : ℕ} (x : Fin k → S) :
    (∑ e : Edge k, internalHazard M t n x e) = t * internalPairWeight M x / (n : ℝ) := by
  unfold internalHazard internalPairWeight
  simp_rw [M.edgeFactor_scale t]
  rw [← Finset.sum_div, ← Finset.mul_sum]

/-- Factoring absence from every present internal edge gives the exact
odds product over the graph's actual edge set. -/
theorem internalGraphProbability_odds (M : CompactBJRModel S) (t : ℝ) (n : ℕ)
    {k : ℕ} (x : Fin k → S) (H : SimpleGraph (Fin k)) :
    internalGraphProbability M t n x H =
      Real.exp (-t * internalPairWeight M x / (n : ℝ)) *
        ∏ e ∈ H.edgeFinset, (Real.exp (M.edgeFactor t x e / (n : ℝ)) - 1) := by
  unfold internalGraphProbability IndependentEdges.mass
  rw [IndependentEdges.prescribedMass_odds, sum_internalHazard]
  have hp :
      (∏ e : Edge k, if assignmentOfGraph H e then
        Real.exp (internalHazard M t n x e) - 1 else 1) =
      ∏ e ∈ presentEdges H, (Real.exp (internalHazard M t n x e) - 1) := by
    symm
    unfold presentEdges
    rw [Finset.prod_filter]
    simp only [assignmentOfGraph, decide_eq_true_eq]
  rw [hp]
  rw [prod_edgeFinset_eq_presentEdges H]
  unfold internalHazard
  congr 1
  congr 1
  ring

/-- Literal product probability of the fixed internal graph and absent
boundary edges, conditional on all selected and unselected types. -/
def fixedConfigurationProbability {J : Type*} [Fintype J]
    (M : CompactBJRModel S) (t : ℝ) (n : ℕ) {k : ℕ}
    (x : Fin k → S) (y : J → S) (H : SimpleGraph (Fin k)) : ℝ :=
  internalGraphProbability M t n x H * boundaryAbsence M t n x y

/-- All hazards for the constrained internal and boundary coordinates. -/
def configurationHazard {J : Type*} (M : CompactBJRModel S) (t : ℝ) (n : ℕ)
    {k : ℕ} (x : Fin k → S) (y : J → S) : Edge k ⊕ (J × Fin k) → ℝ :=
  Sum.elim (internalHazard M t n x)
    (fun e ↦ t * M.kernel (x e.2) (y e.1) / (n : ℝ))

theorem configurationHazard_nonneg {J : Type*} (M : CompactBJRModel S) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) {k : ℕ} (x : Fin k → S) (y : J → S)
    (e : Edge k ⊕ (J × Fin k)) : 0 ≤ configurationHazard M t n x y e := by
  cases e with
  | inl e => exact internalHazard_nonneg M ht n x e
  | inr e =>
    exact div_nonneg (mul_nonneg ht (M.kernel.nonneg _ _)) (Nat.cast_nonneg n)

/-- The product above is a genuine prescribed-configuration probability
under the independent Boolean edge law on all selected internal and boundary pairs. -/
theorem conditional_fixedConfiguration_probability {J : Type*} [Fintype J]
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) {k : ℕ}
    (x : Fin k → S) (y : J → S) (H : SimpleGraph (Fin k)) :
    (∫ a : (Edge k ⊕ (J × Fin k)) → Bool,
      if a = Sum.elim (assignmentOfGraph H) (fun _ ↦ false) then (1 : ℝ) else 0
      ∂(IndependentEdges.pmf
        (configurationHazard M t n x y)
        (configurationHazard_nonneg M ht n x y)).toMeasure) =
      fixedConfigurationProbability M t n x y H := by
  have h := IndependentEdges.integral_agreesOn
    (configurationHazard M t n x y)
    (configurationHazard_nonneg M ht n x y)
    Finset.univ (Sum.elim (assignmentOfGraph H) (fun _ ↦ false))
  have heq (a : (Edge k ⊕ (J × Fin k)) → Bool) :
      AgreesOn Finset.univ (Sum.elim (assignmentOfGraph H) (fun _ ↦ false)) a ↔
        a = Sum.elim (assignmentOfGraph H) (fun _ ↦ false) := by
    simp only [AgreesOn, Finset.mem_univ, forall_true_left, funext_iff]
  simp_rw [heq] at h
  simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, edgeMass_false,
    Fintype.prod_prod_type, fixedConfigurationProbability, internalGraphProbability,
    IndependentEdges.mass, boundaryAbsence, configurationHazard] using h

/-- Exact selected-type formula after averaging all fresh types.  This is
the exponential, the `(n-k)`-th power, and the literal present-edge odds
in the paper's fixed-configuration probability. -/
theorem integral_fixedConfigurationProbability (M : CompactBJRModel S)
    (t : ℝ) (n k : ℕ) (x : Fin k → S) (H : SimpleGraph (Fin k)) :
    (∫ y : Fin (n-k) → S, fixedConfigurationProbability M t n x y H
      ∂typeLaw M (n-k)) =
      Real.exp (-t * internalPairWeight M x / (n : ℝ)) *
        isolationFactor M t n x ^ (n-k) *
        ∏ e ∈ H.edgeFinset, (Real.exp (M.edgeFactor t x e / (n : ℝ)) - 1) := by
  unfold fixedConfigurationProbability
  rw [integral_const_mul, integral_unused_types, internalGraphProbability_odds]
  ring

/-- The normalized present-edge odds, with the paper's zero-hazard convention. -/
def normalizedOdds (z : ℝ) : ℝ := if z = 0 then 1 else (Real.exp z - 1) / z

@[simp] theorem normalizedOdds_zero : normalizedOdds 0 = 1 := by
  simp [normalizedOdds]

theorem mul_normalizedOdds (z : ℝ) : z * normalizedOdds z = Real.exp z - 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [normalizedOdds, if_neg hz]
    field_simp

theorem prod_present_odds_factorization (M : CompactBJRModel S) (t : ℝ) (n : ℕ)
    {k : ℕ} (x : Fin k → S) (H : SimpleGraph (Fin k)) :
    (∏ e ∈ H.edgeFinset, (Real.exp (M.edgeFactor t x e / (n : ℝ)) - 1)) =
      (n : ℝ)⁻¹ ^ H.edgeFinset.card *
        (∏ e ∈ H.edgeFinset, M.edgeFactor t x e) *
        ∏ e ∈ H.edgeFinset, normalizedOdds (M.edgeFactor t x e / (n : ℝ)) := by
  have he (e : Sym2 (Fin k)) :
      Real.exp (M.edgeFactor t x e / (n : ℝ)) - 1 =
        ((n : ℝ)⁻¹ * M.edgeFactor t x e) *
          normalizedOdds (M.edgeFactor t x e / (n : ℝ)) := by
    rw [← mul_normalizedOdds, div_eq_mul_inv]
    ring
  simp_rw [he]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]

theorem vertexFactor_eq_exp_totalDegree (M : CompactBJRModel S) (t : ℝ)
    {k : ℕ} (x : Fin k → S) :
    (∏ i : Fin k, Real.exp (-t * M.degreeFunction (x i))) =
      Real.exp (-t * totalDegree M x) := by
  rw [← Real.exp_sum]
  congr 1
  unfold totalDegree
  rw [← Finset.mul_sum]

/-- The fixed-configuration residual before the deterministic vertex-selection
factor and before normalization by the connected-graph partition function. -/
def configurationResidual (M : CompactBJRModel S) (t : ℝ) (n : ℕ)
    {k : ℕ} (x : Fin k → S) (H : SimpleGraph (Fin k)) : ℝ :=
  Real.exp (t * totalDegree M x - t * internalPairWeight M x / (n : ℝ)) *
    isolationFactor M t n x ^ (n-k) *
    ∏ e ∈ H.edgeFinset, normalizedOdds (M.edgeFactor t x e / (n : ℝ))

/-- Exact annealed weight factorization for one selected graph.  The zero
kernel case is included: its edge weight vanishes and its normalized odds
are defined as one.  No division by a nonzero kernel value is assumed. -/
theorem integral_fixedConfiguration_weight_factorization
    (M : CompactBJRModel S) (t : ℝ) (n k : ℕ)
    (x : Fin k → S) (H : SimpleGraph (Fin k)) :
    (∫ y : Fin (n-k) → S, fixedConfigurationProbability M t n x y H
      ∂typeLaw M (n-k)) =
      (n : ℝ)⁻¹ ^ H.edgeFinset.card * M.graphWeightIntegrand t H x *
        configurationResidual M t n x H := by
  rw [integral_fixedConfigurationProbability, prod_present_odds_factorization]
  unfold CompactBJRModel.graphWeightIntegrand configurationResidual
  rw [vertexFactor_eq_exp_totalDegree]
  have he : Real.exp (-t * totalDegree M x) *
      Real.exp (t * totalDegree M x - t * internalPairWeight M x / (n : ℝ)) =
      Real.exp (-t * internalPairWeight M x / (n : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (n : ℝ)⁻¹ ^ H.edgeFinset.card *
        (∏ e ∈ H.edgeFinset, M.edgeFactor t x e) *
        (Real.exp (-t * totalDegree M x) *
          Real.exp (t * totalDegree M x - t * internalPairWeight M x / (n : ℝ))) *
        isolationFactor M t n x ^ (n-k) *
        (∏ e ∈ H.edgeFinset, normalizedOdds (M.edgeFactor t x e / (n : ℝ))) := by
      rw [he]
      ring
    _ = _ := by ring

/-- Type-integrated exact fixed-graph weight identity.  Both the selected and
the unused types are averaged over their literal independent product laws. -/
theorem annealed_fixedConfiguration_weight_factorization
    (M : CompactBJRModel S) (t : ℝ) (n k : ℕ) (H : SimpleGraph (Fin k)) :
    (∫ x : Fin k → S,
      (∫ y : Fin (n-k) → S, fixedConfigurationProbability M t n x y H
        ∂typeLaw M (n-k)) ∂typeLaw M k) =
      (n : ℝ)⁻¹ ^ H.edgeFinset.card *
        ∫ x : Fin k → S,
          M.graphWeightIntegrand t H x * configurationResidual M t n x H
          ∂typeLaw M k := by
  simp_rw [integral_fixedConfiguration_weight_factorization]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end PerronWright.FreshTypeAveraging
