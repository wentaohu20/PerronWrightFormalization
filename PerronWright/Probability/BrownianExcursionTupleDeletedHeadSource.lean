import PerronWright.Probability.BrownianExcursionTupleHeadDecomposition
import PerronWright.Probability.BrownianMinimumPointReturnAnchor

/-! # Actual ordered tuple head and the genuinely deleted tail source

The coupled tail test is Borel for every real proposed head length, not
only on selected excursions. The expectation identity uses the actual
bounded-component full set and the proved surviving-component reindexing;
no stochastic Palm or deletion law is supplied as a premise.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace PerronWright.BrownianExcursionTupleDeletedHeadSource

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionComponents
open FullHorizonExcursionSection FullHorizonExcursionEndpoints BrownianFullHorizonExcursionAreas
open BrownianExcursionDeletionGeometry BrownianExcursionDeletionTupleSource
open BrownianExcursionTupleHeadDecomposition BrownianMinimumPointReturnAnchor
open BrownianExcursionTuplePoissonWeights (poissonWeight measurable_poissonWeight)

theorem measurable_headTail_sourceSum {d : ℕ} (lambda : ℝ) (marks : Fin d → ℕ)
    (H : (Fin (d+1) → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    Measurable (fun p : ℝ × Path ↦ sourceSum (lambda-p.1) marks
      (fun xs ↦ H (Fin.cons p.1 xs)) p.2) := by
  classical
  have hparam : Measurable (fun p : ℝ × Path ↦ (lambda-p.1,p.2)) :=
    (measurable_const.sub measurable_fst).prodMk measurable_snd
  have hR : Measurable (fun p : ℝ × Path ↦ driftedReflectionPath (lambda-p.1) p.2) := by
    simpa only [Function.comp_def] using continuous_driftedReflectionPath.measurable.comp hparam
  change Measurable (fun p : ℝ × Path ↦ ∑' e : Fin d → ℚ,
    if Function.Injective e ∧ ∀ i, Representative (driftedReflectionPath (lambda-p.1) p.2) (e i)
    then H (Fin.cons p.1 (fun i ↦ length (e i : ℝ) (driftedReflectionPath (lambda-p.1) p.2))) *
      ∏ i, poissonWeight (excursionArea (e i : ℝ) (lambda-p.1) p.2) (marks i)
    else 0)
  apply Measurable.tsum
  intro e
  have hgate : Measurable (fun p : ℝ × Path ↦ Function.Injective e ∧ ∀ i,
      Representative (driftedReflectionPath (lambda-p.1) p.2) (e i)) :=
    measurable_const.and (Measurable.forall (fun i ↦ measurableSet_setOfPred.mp
      ((measurableSet_representative (e i)).preimage hR)))
  have hvec : Measurable (fun p : ℝ × Path ↦
      (Fin.cons p.1 (fun i ↦ length (e i : ℝ) (driftedReflectionPath (lambda-p.1) p.2)) :
        Fin (d+1) → ℝ)) := by
    apply measurable_pi_lambda
    intro i
    cases i using Fin.cases with
    | zero => simpa only [Fin.cons_zero] using (measurable_fst : Measurable (fun p : ℝ × Path ↦ p.1))
    | succ i =>
      simpa only [Fin.cons_succ,Function.comp_def] using (measurable_length (e i : ℝ)).comp hR
  have hprod : Measurable (fun p : ℝ × Path ↦
      ∏ i, poissonWeight (excursionArea (e i : ℝ) (lambda-p.1) p.2) (marks i)) := by
    apply Finset.measurable_prod
    intro i _
    have ha : Measurable (fun p : ℝ × Path ↦ excursionArea (e i : ℝ) (lambda-p.1) p.2) := by
      simpa only [Function.comp_def] using (measurable_excursionArea_all_parameters (e i : ℝ)).comp hparam
    exact (measurable_poissonWeight (marks i)).comp ha
  apply Measurable.ite hgate.setOf
  · have hval : Measurable (fun p : ℝ × Path ↦
        H (Fin.cons p.1 (fun i ↦ length (e i : ℝ) (driftedReflectionPath (lambda-p.1) p.2)))) := by
      simpa only [Function.comp_def] using hH.comp hvec
    simpa only [Function.comp_def] using measurable_mul.comp (hval.prodMk hprod)
  · exact measurable_const

theorem actual_sourceSum_deleted_head_lintegral {d : ℕ} (lambda : ℝ)
    (r : ℕ) (marks : Fin d → ℕ) (H : (Fin (d+1) → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ f : Path, sourceSum lambda (Fin.cons r marks) H f ∂pathLaw) =
      ∑' q : ℚ, ∫⁻ f : Path,
        if Representative (driftedReflectionPath lambda f) q then
          poissonWeight (excursionArea (q : ℝ) lambda f) r *
            sourceSum (lambda-length (q : ℝ) (driftedReflectionPath lambda f)) marks
              (fun xs ↦ H (Fin.cons (length (q : ℝ) (driftedReflectionPath lambda f)) xs))
                (deletedPath (q : ℝ) lambda f)
        else 0 ∂pathLaw := by
  have hfinite : ∀ᵐ f : Path ∂pathLaw, ∀ q : ℚ,
      BddAbove (component (driftedReflectionPath lambda f) (q : ℝ)) :=
    ae_all_iff.mpr (fun q ↦ ae_actual_parabolic_component_bddAbove lambda (q : ℝ))
  have hm (q : ℚ) : Measurable (fun f : Path ↦
      if Representative (driftedReflectionPath lambda f) q then
        poissonWeight (excursionArea (q : ℝ) lambda f) r *
          survivingSourceSum q lambda marks
            (fun xs ↦ H (Fin.cons (length (q : ℝ) (driftedReflectionPath lambda f)) xs)) f
      else 0) := by
    simpa only [Function.comp_def,id_eq] using
      (measurable_head_test_all_parameters q r marks H hH).comp
        ((measurable_const : Measurable (fun _ : Path ↦ lambda)).prodMk measurable_id)
  calc
    _ = ∫⁻ f : Path, ∑' q : ℚ,
        if Representative (driftedReflectionPath lambda f) q then
          poissonWeight (excursionArea (q : ℝ) lambda f) r *
            survivingSourceSum q lambda marks
              (fun xs ↦ H (Fin.cons (length (q : ℝ) (driftedReflectionPath lambda f)) xs)) f
        else 0 ∂pathLaw :=
      lintegral_congr (fun f ↦ sourceSum_head_decomposition lambda r marks H f)
    _ = ∑' q : ℚ, ∫⁻ f : Path,
        if Representative (driftedReflectionPath lambda f) q then
          poissonWeight (excursionArea (q : ℝ) lambda f) r *
            survivingSourceSum q lambda marks
              (fun xs ↦ H (Fin.cons (length (q : ℝ) (driftedReflectionPath lambda f)) xs)) f
        else 0 ∂pathLaw := lintegral_tsum (fun q ↦ (hm q).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro q
      apply lintegral_congr_ae
      filter_upwards [hfinite] with f hf
      by_cases hq : Representative (driftedReflectionPath lambda f) q
      · rw [if_pos hq,if_pos hq,
          survivingSourceSum_eq_deleted_sourceSum q lambda marks _ f hq (hf q) hf,
          deletedParameter,cutLength_eq_length (q : ℝ) lambda f hq.1 (hf q)]
      · rw [if_neg hq,if_neg hq]

end PerronWright.BrownianExcursionTupleDeletedHeadSource
