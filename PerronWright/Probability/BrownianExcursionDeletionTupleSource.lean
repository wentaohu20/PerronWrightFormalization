import PerronWright.Probability.BrownianExcursionDeletionWeights

/-! # Fixed rational tuple sources after one genuine excursion deletion

The actual factorial source uses fixed rational-coordinate tuples, while
the proved deletion equivalence reindexes embeddings into path-dependent
representatives. This leaf joins those two literal sums. Joint parameter
and path measurability permits the genuinely random remaining parameter.
No stochastic deletion or Palm law is an input.
-/

open MeasureTheory Topology Set
open scoped Classical NNReal BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionDeletionTupleSource

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionComponents
open FullHorizonExcursionSection FullHorizonExcursionEndpoints BrownianFullHorizonExcursionAreas
open BrownianExcursionDeletionGeometry BrownianExcursionDeletionWeights
open BrownianExcursionTuplePoissonWeights (poissonWeight measurable_poissonWeight)

private def tuplePayload {d : ℕ} (lambda : ℝ) (marks : Fin d → ℕ)
    (H : (Fin d → ℝ) → ℝ≥0∞) (f : Path) (e : Fin d → ℚ) : ℝ≥0∞ :=
  H (fun i ↦ length (e i : ℝ) (driftedReflectionPath lambda f)) *
    ∏ i, poissonWeight (excursionArea (e i : ℝ) lambda f) (marks i)

def sourceSum {d : ℕ} (lambda : ℝ) (marks : Fin d → ℕ)
    (H : (Fin d → ℝ) → ℝ≥0∞) (f : Path) : ℝ≥0∞ :=
  ∑' e : Fin d → ℚ,
    if Function.Injective e ∧ ∀ i, Representative (driftedReflectionPath lambda f) (e i)
    then tuplePayload lambda marks H f e else 0

def survivingSourceSum {d : ℕ} (q : ℚ) (lambda : ℝ) (marks : Fin d → ℕ)
    (H : (Fin d → ℝ) → ℝ≥0∞) (f : Path) : ℝ≥0∞ :=
  ∑' e : Fin d → ℚ,
    if Function.Injective e ∧ ∀ i,
      Representative (driftedReflectionPath lambda f) (e i) ∧ e i ≠ q
    then tuplePayload lambda marks H f e else 0

private theorem measurable_tuplePayload {d : ℕ} (marks : Fin d → ℕ)
    (H : (Fin d → ℝ) → ℝ≥0∞) (hH : Measurable H) (e : Fin d → ℚ) :
    Measurable (fun p : ℝ × Path ↦ tuplePayload p.1 marks H p.2 e) := by
  apply Measurable.mul
  · apply hH.comp
    apply measurable_pi_lambda
    intro i
    exact (measurable_length (e i : ℝ)).comp continuous_driftedReflectionPath.measurable
  · apply Finset.measurable_prod
    intro i _
    exact (measurable_poissonWeight (marks i)).comp
      (measurable_excursionArea_all_parameters (e i : ℝ))

theorem measurable_sourceSum_all_parameters {d : ℕ} (marks : Fin d → ℕ)
    (H : (Fin d → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    Measurable (fun p : ℝ × Path ↦ sourceSum p.1 marks H p.2) := by
  apply Measurable.tsum
  intro e
  apply Measurable.ite _ (measurable_tuplePayload marks H hH e) measurable_const
  apply Measurable.setOf
  exact measurable_const.and (Measurable.forall (fun i ↦ measurableSet_setOfPred.mp
    ((measurableSet_representative (e i)).preimage continuous_driftedReflectionPath.measurable)))

theorem measurable_survivingSourceSum_all_parameters {d : ℕ} (q : ℚ) (marks : Fin d → ℕ)
    (H : (Fin d → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    Measurable (fun p : ℝ × Path ↦ survivingSourceSum q p.1 marks H p.2) := by
  apply Measurable.tsum
  intro e
  apply Measurable.ite _ (measurable_tuplePayload marks H hH e) measurable_const
  apply Measurable.setOf
  exact measurable_const.and (Measurable.forall (fun i ↦
    (measurableSet_setOfPred.mp ((measurableSet_representative (e i)).preimage
      continuous_driftedReflectionPath.measurable)).and measurable_const))

private def representativeTupleEquiv {d : ℕ} (P : ℚ → Prop) :
    (Fin d ↪ {r : ℚ // P r}) ≃
      {e : Fin d → ℚ // Function.Injective e ∧ ∀ i, P (e i)} where
  toFun e := ⟨fun i ↦ (e i).1,
    ⟨fun _ _ h ↦ e.injective (Subtype.ext h), fun i ↦ (e i).2⟩⟩
  invFun e := ⟨fun i ↦ ⟨e.1 i, e.2.2 i⟩,
    fun _ _ h ↦ e.2.1 (congrArg Subtype.val h)⟩
  left_inv e := by ext i; rfl
  right_inv e := by apply Subtype.ext; rfl

private theorem fixed_tuple_sum_eq_embeddings {d : ℕ} (P : ℚ → Prop)
    (K : (Fin d → ℚ) → ℝ≥0∞) :
    (∑' e : Fin d → ℚ, if Function.Injective e ∧ ∀ i, P (e i) then K e else 0) =
      ∑' e : Fin d ↪ {r : ℚ // P r}, K (fun i ↦ (e i).1) := by
  let S : Set (Fin d → ℚ) := {e | Function.Injective e ∧ ∀ i, P (e i)}
  calc
    _ = ∑' e : S, K e.1 := by
      rw [tsum_subtype]
      exact tsum_congr (fun e ↦ by simp only [S, Set.indicator_apply, mem_ofPred_eq])
    _ = _ := (representativeTupleEquiv P).tsum_eq (fun e ↦ K e.1) |>.symm

theorem sourceSum_eq_representative_embeddings {d : ℕ} (lambda : ℝ) (marks : Fin d → ℕ)
    (H : (Fin d → ℝ) → ℝ≥0∞) (f : Path) :
    sourceSum lambda marks H f =
      ∑' e : Fin d ↪ {r : ℚ // Representative (driftedReflectionPath lambda f) r},
        H (fun i ↦ length ((e i).1 : ℝ) (driftedReflectionPath lambda f)) *
          ∏ i, poissonWeight (excursionArea ((e i).1 : ℝ) lambda f) (marks i) :=
  fixed_tuple_sum_eq_embeddings _ _

theorem survivingSourceSum_eq_representative_embeddings {d : ℕ}
    (q : ℚ) (lambda : ℝ) (marks : Fin d → ℕ) (H : (Fin d → ℝ) → ℝ≥0∞)
    (f : Path) (hq : Representative (driftedReflectionPath lambda f) q) :
    survivingSourceSum q lambda marks H f =
      ∑' e : Fin d ↪ survivingRepresentatives q lambda f,
        H (fun i ↦ length ((e i).1 : ℝ) (driftedReflectionPath lambda f)) *
          ∏ i, poissonWeight (excursionArea ((e i).1 : ℝ) lambda f) (marks i) := by
  have he (e : Fin d → ℚ) :
      (Function.Injective e ∧ ∀ i, Representative (driftedReflectionPath lambda f) (e i) ∧ e i ≠ q) ↔
        (Function.Injective e ∧ ∀ i, Representative (driftedReflectionPath lambda f) (e i) ∧
          component (driftedReflectionPath lambda f) (e i : ℝ) ≠
            component (driftedReflectionPath lambda f) (q : ℝ)) := by
    refine and_congr_right (fun _ ↦ forall_congr' (fun i ↦ ?_))
    constructor
    · rintro ⟨hi, hne⟩
      exact ⟨hi, fun hc ↦ hne (representatives_eq_of_component_eq hi hq hc)⟩
    · rintro ⟨hi, hne⟩
      exact ⟨hi, fun h ↦ hne (by rw [h])⟩
  unfold survivingSourceSum
  simp_rw [he]
  simpa only [survivingRepresentatives, tuplePayload] using
    fixed_tuple_sum_eq_embeddings
      (fun r : ℚ ↦ Representative (driftedReflectionPath lambda f) r ∧
        component (driftedReflectionPath lambda f) (r : ℝ) ≠
          component (driftedReflectionPath lambda f) (q : ℝ))
      (tuplePayload lambda marks H f)

theorem survivingSourceSum_eq_deleted_sourceSum {d : ℕ}
    (q : ℚ) (lambda : ℝ) (marks : Fin d → ℕ) (H : (Fin d → ℝ) → ℝ≥0∞)
    (f : Path) (hq : Representative (driftedReflectionPath lambda f) q)
    (hbq : BddAbove (component (driftedReflectionPath lambda f) (q : ℝ)))
    (hfinite : ∀ r : ℚ, BddAbove (component (driftedReflectionPath lambda f) (r : ℝ))) :
    survivingSourceSum q lambda marks H f =
      sourceSum (deletedParameter q lambda f) marks H (deletedPath q lambda f) := by
  rw [survivingSourceSum_eq_representative_embeddings q lambda marks H f hq]
  rw [surviving_poisson_tuple_sum q lambda f hq.1 hbq hfinite d marks H]
  exact (sourceSum_eq_representative_embeddings
    (deletedParameter q lambda f) marks H (deletedPath q lambda f)).symm

set_option backward.isDefEq.respectTransparency true in
theorem measurable_deleted_sourceSum_all_parameters {d : ℕ} (q : ℚ) (marks : Fin d → ℕ)
    (H : (Fin d → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    Measurable (fun p : ℝ × Path ↦
      sourceSum (deletedParameter q p.1 p.2) marks H (deletedPath q p.1 p.2)) := by
  have hm : Measurable (fun p : ℝ × Path ↦
      (deletedParameter q p.1 p.2, deletedPath q p.1 p.2)) :=
    (measurable_deletedParameter_all_parameters q).prodMk
      (measurable_deletedPath_all_parameters q)
  simpa only [Function.comp_def] using
    (measurable_sourceSum_all_parameters marks H hH).comp hm

end PerronWright.BrownianExcursionDeletionTupleSource
