import PerronWright.Probability.BrownianExcursionDeletionTupleSource
import Mathlib.Data.Fin.Tuple.Basic

/-! # Literal ordered head decomposition of complete excursion tuple sources

Fin.cons separates each fixed rational tuple uniquely into its head and
tail. Its injection criterion excludes precisely the selected head from
the surviving tail source. The head's full-area Poisson weight factors
without a finiteness or stochastic Palm hypothesis. Coupled Borel tests
retain the actual head length and are jointly measurable in parameter
and Brownian path.
-/

open MeasureTheory Topology Set
open scoped Classical NNReal BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionTupleHeadDecomposition

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionComponents
open FullHorizonExcursionSection FullHorizonExcursionEndpoints BrownianFullHorizonExcursionAreas
open BrownianExcursionTuplePoissonWeights (poissonWeight measurable_poissonWeight)
open BrownianExcursionDeletionTupleSource

private def tupleContribution {d : ℕ} (lambda : ℝ) (marks : Fin d → ℕ)
    (H : (Fin d → ℝ) → ℝ≥0∞) (f : Path) (e : Fin d → ℚ) : ℝ≥0∞ :=
  if Function.Injective e ∧ ∀ i, Representative (driftedReflectionPath lambda f) (e i)
  then H (fun i ↦ length (e i : ℝ) (driftedReflectionPath lambda f)) *
    ∏ i, poissonWeight (excursionArea (e i : ℝ) lambda f) (marks i)
  else 0

private theorem tuple_gate_cons {d : ℕ} (R : Path) (q : ℚ) (e : Fin d → ℚ) :
    (Function.Injective (Fin.cons q e : Fin (d+1) → ℚ) ∧
      ∀ i, Representative R ((Fin.cons q e : Fin (d+1) → ℚ) i)) ↔
      Representative R q ∧ Function.Injective e ∧ ∀ i, Representative R (e i) ∧ e i ≠ q := by
  rw [Fin.cons_injective_iff, Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro ⟨⟨hnot, hinj⟩, hq, he⟩
    exact ⟨hq, hinj, fun i ↦ ⟨he i, fun h ↦ hnot ⟨i, h⟩⟩⟩
  · rintro ⟨hq, hinj, he⟩
    exact ⟨⟨fun ⟨i, hi⟩ ↦ (he i).2 hi, hinj⟩, hq, fun i ↦ (he i).1⟩

private theorem tupleContribution_cons {d : ℕ} (lambda : ℝ)
    (r : ℕ) (marks : Fin d → ℕ) (H : (Fin (d+1) → ℝ) → ℝ≥0∞)
    (f : Path) (q : ℚ) (e : Fin d → ℚ) :
    tupleContribution lambda (Fin.cons r marks) H f (Fin.cons q e) =
      if Representative (driftedReflectionPath lambda f) q then
        poissonWeight (excursionArea (q : ℝ) lambda f) r *
          (if Function.Injective e ∧ ∀ i, Representative (driftedReflectionPath lambda f) (e i) ∧ e i ≠ q
          then H (Fin.cons (length (q : ℝ) (driftedReflectionPath lambda f))
            (fun i ↦ length (e i : ℝ) (driftedReflectionPath lambda f))) *
              ∏ i, poissonWeight (excursionArea (e i : ℝ) lambda f) (marks i)
          else 0)
      else 0 := by
  have hlength : (fun i ↦ length (((Fin.cons q e : Fin (d+1) → ℚ) i) : ℝ)
      (driftedReflectionPath lambda f)) =
      (Fin.cons (length (q : ℝ) (driftedReflectionPath lambda f))
        (fun i ↦ length (e i : ℝ) (driftedReflectionPath lambda f)) : Fin (d+1) → ℝ) := by
    funext i
    cases i using Fin.cases <;> simp only [Fin.cons_zero, Fin.cons_succ]
  unfold tupleContribution
  simp only [tuple_gate_cons]
  by_cases hq : Representative (driftedReflectionPath lambda f) q
  · by_cases he : Function.Injective e ∧ ∀ i,
        Representative (driftedReflectionPath lambda f) (e i) ∧ e i ≠ q
    · simp only [hq, he, true_and, if_true, hlength, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      split_ifs <;> first | ac_rfl | simp only [mul_zero]
    · simp only [hq, he, true_and, if_false, if_true, mul_zero]
  · simp only [hq, false_and, if_false]

theorem sourceSum_head_decomposition {d : ℕ} (lambda : ℝ)
    (r : ℕ) (marks : Fin d → ℕ) (H : (Fin (d+1) → ℝ) → ℝ≥0∞) (f : Path) :
    sourceSum lambda (Fin.cons r marks) H f =
      ∑' q : ℚ, if Representative (driftedReflectionPath lambda f) q then
        poissonWeight (excursionArea (q : ℝ) lambda f) r *
          survivingSourceSum q lambda marks
            (fun xs ↦ H (Fin.cons (length (q : ℝ) (driftedReflectionPath lambda f)) xs)) f
      else 0 := by
  change (∑' e : Fin (d+1) → ℚ, tupleContribution lambda (Fin.cons r marks) H f e) = _
  rw [← (Fin.consEquiv (fun _ : Fin (d+1) ↦ ℚ)).tsum_eq
    (tupleContribution lambda (Fin.cons r marks) H f), ENNReal.tsum_prod']
  change (∑' q : ℚ, ∑' e : Fin d → ℚ,
    tupleContribution lambda (Fin.cons r marks) H f (Fin.cons q e)) = _
  simp_rw [tupleContribution_cons]
  apply tsum_congr
  intro q
  by_cases hq : Representative (driftedReflectionPath lambda f) q
  · simp only [if_pos hq]
    rw [ENNReal.tsum_mul_left]
    rfl
  · simp only [if_neg hq, tsum_zero]

theorem measurable_coupled_survivingSourceSum_all_parameters {d : ℕ}
    (q : ℚ) (marks : Fin d → ℕ) (H : (Fin (d+1) → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    Measurable (fun p : ℝ × Path ↦ survivingSourceSum q p.1 marks
      (fun xs ↦ H (Fin.cons (length (q : ℝ) (driftedReflectionPath p.1 p.2)) xs)) p.2) := by
  change Measurable (fun p : ℝ × Path ↦ ∑' e : Fin d → ℚ,
    if Function.Injective e ∧ ∀ i, Representative (driftedReflectionPath p.1 p.2) (e i) ∧ e i ≠ q
    then H (Fin.cons (length (q : ℝ) (driftedReflectionPath p.1 p.2))
      (fun i ↦ length (e i : ℝ) (driftedReflectionPath p.1 p.2))) *
        ∏ i, poissonWeight (excursionArea (e i : ℝ) p.1 p.2) (marks i)
    else 0)
  apply Measurable.tsum
  intro e
  have hgate : Measurable (fun p : ℝ × Path ↦ Function.Injective e ∧ ∀ i,
      Representative (driftedReflectionPath p.1 p.2) (e i) ∧ e i ≠ q) :=
    measurable_const.and (Measurable.forall (fun i ↦
      (measurableSet_setOfPred.mp ((measurableSet_representative (e i)).preimage
        continuous_driftedReflectionPath.measurable)).and measurable_const))
  have hvec : Measurable (fun p : ℝ × Path ↦
      (Fin.cons (length (q : ℝ) (driftedReflectionPath p.1 p.2))
        (fun i ↦ length (e i : ℝ) (driftedReflectionPath p.1 p.2)) : Fin (d+1) → ℝ)) := by
    apply measurable_pi_lambda
    intro i
    cases i using Fin.cases with
    | zero =>
      simpa only [Fin.cons_zero, Function.comp_def] using
        (measurable_length (q : ℝ)).comp continuous_driftedReflectionPath.measurable
    | succ i =>
      simpa only [Fin.cons_succ, Function.comp_def] using
        (measurable_length (e i : ℝ)).comp continuous_driftedReflectionPath.measurable
  have hprod : Measurable (fun p : ℝ × Path ↦
      ∏ i, poissonWeight (excursionArea (e i : ℝ) p.1 p.2) (marks i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (measurable_poissonWeight (marks i)).comp
      (measurable_excursionArea_all_parameters (e i : ℝ))
  exact Measurable.ite hgate.setOf ((hH.comp hvec).mul hprod) measurable_const

theorem measurable_head_test_all_parameters {d : ℕ} (q : ℚ)
    (r : ℕ) (marks : Fin d → ℕ) (H : (Fin (d+1) → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    Measurable (fun p : ℝ × Path ↦
      if Representative (driftedReflectionPath p.1 p.2) q then
        poissonWeight (excursionArea (q : ℝ) p.1 p.2) r *
          survivingSourceSum q p.1 marks
            (fun xs ↦ H (Fin.cons (length (q : ℝ) (driftedReflectionPath p.1 p.2)) xs)) p.2
      else 0) :=
  Measurable.ite ((measurableSet_representative q).preimage continuous_driftedReflectionPath.measurable)
    (((measurable_poissonWeight r).comp (measurable_excursionArea_all_parameters (q : ℝ))).mul
      (measurable_coupled_survivingSourceSum_all_parameters q marks H hH)) measurable_const

end PerronWright.BrownianExcursionTupleHeadDecomposition
