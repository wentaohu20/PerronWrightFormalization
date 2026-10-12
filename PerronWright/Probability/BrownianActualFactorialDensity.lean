import PerronWright.Probability.BrownianActualMarkedPalm
import PerronWright.Probability.BrownianExcursionTupleDeletedHeadSource
import PerronWright.Probability.BrownianFactorialDensityDeletion
import PerronWright.Probability.BrownianExcursionFactorialTests
import PerronWright.Probability.BrownianKilledFreeEntranceGeometry

/-! # The actual all-order Brownian--Wright factorial density

The literal ordered full-area source is evaluated by the proved marked
Palm deletion law. All tests are arbitrary nonnegative Borel functions;
neither finite moments nor a factorial-density identity is an input.
-/

open MeasureTheory Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true

namespace PerronWright.BrownianActualFactorialDensity

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionComponents FullHorizonExcursionSection
open FullHorizonExcursionEndpoints BrownianFullHorizonExcursionAreas
open BrownianExcursionDeletionTupleSource BrownianExcursionTupleDeletedHeadSource
open BrownianActualMarkedPalm BrownianFactorialDensityDeletion FactorialDensity
open BrownianKilledFreeEntranceGeometry
open BrownianExcursionWindowPointMeasure BrownianExcursionTupleTests
open BrownianExcursionRectangleFactorials BrownianExcursionFactorialTests
open ComponentGlobalPointProcess

private def positiveOrthant (d : ℕ) : Set (Fin d → ℝ) := {xs | ∀ i, 0 < xs i}

private theorem measurableSet_positiveOrthant (d : ℕ) :
    MeasurableSet (positiveOrthant d) := by
  apply Measurable.setOf
  exact Measurable.forall (fun i ↦ measurableSet_setOfPred.mp
    (measurableSet_lt measurable_const (measurable_pi_apply i)))

private theorem measurable_density {d : ℕ} (lambda : ℝ) (marks : Fin d → ℕ) :
    Measurable (fun xs : Fin d → ℝ ↦ density 1 1 lambda xs marks) := by
  unfold density criticalExponent sizeFactor
  fun_prop

private theorem lintegral_positiveOrthant_cons (d : ℕ)
    (F : (Fin (d+1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ xs in positiveOrthant (d+1), F xs) =
      ∫⁻ l : ℝ in Ioi 0, ∫⁻ xs in positiveOrthant d, F (Fin.cons l xs) := by
  rw [← lintegral_indicator (measurableSet_positiveOrthant (d+1)),
    lintegral_volume_freeCons d (hF.indicator (measurableSet_positiveOrthant (d+1))),
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro l
  by_cases hl : 0 < l
  · rw [indicator_of_mem (show l ∈ Ioi (0 : ℝ) from hl),
      ← lintegral_indicator (measurableSet_positiveOrthant d)]
    apply lintegral_congr
    intro xs
    simp only [freeCons,positiveOrthant,Set.indicator_apply,mem_ofPred_eq,
      Fin.forall_fin_succ,Fin.cons_zero,Fin.cons_succ,hl,true_and]
  · rw [indicator_of_notMem (show l ∉ Ioi (0 : ℝ) from hl)]
    simp only [freeCons,positiveOrthant,Set.indicator_apply,mem_ofPred_eq,
      Fin.forall_fin_succ,Fin.cons_zero,Fin.cons_succ,hl,false_and,if_false,lintegral_zero]

theorem actual_ordered_source_factorial_density {d : ℕ} (lambda : ℝ)
    (marks : Fin d → ℕ) (H : (Fin d → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ f : Path, sourceSum lambda marks H f ∂pathLaw) =
      ∫⁻ xs in {xs : Fin d → ℝ | ∀ i, 0 < xs i},
        ENNReal.ofReal (density 1 1 lambda xs marks)*H xs := by
  induction d generalizing lambda with
  | zero =>
    let v : Fin 0 → ℝ := Fin.elim0
    have hs (f : Path) : sourceSum lambda marks H f = H v := by
      change (∑' e : Fin 0 → ℚ,
        if Function.Injective e ∧ ∀ i, Representative (driftedReflectionPath lambda f) (e i)
        then H (fun i ↦ length (e i : ℝ) (driftedReflectionPath lambda f)) *
          ∏ i, BrownianExcursionTuplePoissonWeights.poissonWeight
            (excursionArea (e i : ℝ) lambda f) (marks i) else 0) = H v
      rw [tsum_eq_single (fun i : Fin 0 ↦ Fin.elim0 i)]
      · have hg : Function.Injective (fun i : Fin 0 ↦ (Fin.elim0 i : ℚ)) ∧
            ∀ i, Representative (driftedReflectionPath lambda f) (Fin.elim0 i) :=
          ⟨fun i ↦ Fin.elim0 i,fun i ↦ Fin.elim0 i⟩
        rw [if_pos hg,Fin.prod_univ_zero,mul_one]
        exact congrArg H (Subsingleton.elim _ _)
      · intro e he
        exact False.elim (he (Subsingleton.elim _ _))
    have hv (xs : Fin 0 → ℝ) : H xs = H v := congrArg H (Subsingleton.elim _ _)
    simp_rw [hs,hv]
    simp [density,criticalExponent,volume_pi,Measure.pi_empty_univ]
  | succ d ih =>
    rw [← Fin.cons_self_tail marks]
    let r := marks 0
    let rs := Fin.tail marks
    let Htail : ℝ × Path → ℝ≥0∞ := fun p ↦
      sourceSum (lambda-p.1) rs (fun xs ↦ H (Fin.cons p.1 xs)) p.2
    have hHtail : Measurable Htail := measurable_headTail_sourceSum lambda rs H hH
    have hh (l : ℝ) : Measurable (fun xs : Fin d → ℝ ↦ H (Fin.cons l xs)) :=
      hH.comp ((continuous_freeCons d).measurable.comp (measurable_const.prodMk measurable_id))
    rw [actual_sourceSum_deleted_head_lintegral lambda r rs H hH,
      actual_marked_palm_lintegral lambda r Htail hHtail]
    calc
      _ = ∫⁻ l : ℝ in Ioi 0, ∫⁻ xs in positiveOrthant d,
          ENNReal.ofReal (Real.exp (-criticalExponent 1 1 lambda l)*sizeFactor 1 l r)*
            (ENNReal.ofReal (density 1 1 (lambda-l) xs rs)*H (Fin.cons l xs)) := by
        apply lintegral_congr
        intro l
        have hi := ih (lambda-l) rs (fun xs ↦ H (Fin.cons l xs)) (hh l)
        change ENNReal.ofReal (Real.exp (-criticalExponent 1 1 lambda l)*sizeFactor 1 l r)*
          (∫⁻ f, sourceSum (lambda-l) rs (fun xs ↦ H (Fin.cons l xs)) f ∂pathLaw) = _
        rw [hi]
        exact (lintegral_const_mul _ ((measurable_density (lambda-l) rs).ennreal_ofReal.mul (hh l))).symm
      _ = ∫⁻ xs in positiveOrthant (d+1),
          ENNReal.ofReal (density 1 1 lambda xs (Fin.cons r rs))*H xs := by
        rw [lintegral_positiveOrthant_cons d
          (fun xs : Fin (d+1) → ℝ ↦ ENNReal.ofReal (density 1 1 lambda xs (Fin.cons r rs))*H xs)
          ((measurable_density lambda (Fin.cons r rs)).ennreal_ofReal.mul hH)]
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
        apply lintegral_congr
        intro xs
        rw [density_cons,ENNReal.ofReal_mul
          (mul_pos (Real.exp_pos _)
            (sizeFactor_pos (beta := (1 : ℝ)) (x := l) (by norm_num) hl r)).le,mul_assoc]
      _ = _ := rfl

private def lengthBox {d : ℕ} (a b : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {xs | ∀ i, xs i ∈ Icc (a i) (b i)}

private theorem measurableSet_lengthBox {d : ℕ} (a b : Fin d → ℝ) :
    MeasurableSet (lengthBox a b) := by
  apply Measurable.setOf
  exact Measurable.forall (fun i ↦ measurableSet_setOfPred.mp
    ((measurable_pi_apply i) measurableSet_Icc))

/-- The literal intrinsic fixed-surplus window factorial test, allowing
overlapping slot windows and arbitrary coupled Borel length tests. -/
theorem actual_window_factorial_density {d : ℕ} (lambda : ℝ)
    (a b : Fin d → ℝ) (marks : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (H : (Fin d → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ η, factorialTest a b marks
      (fun z ↦ H (fun i ↦ (z i).1.val)) η
      ∂(BrownianExcursionCompactWindows.law lambda (windowSet a b marks)
        (isCompact_windowSet a b marks ha) : Measure _)) =
      ∫⁻ xs in {xs : Fin d → ℝ | ∀ i, xs i ∈ Icc (a i) (b i)},
        ENNReal.ofReal (density 1 1 lambda xs marks)*H xs := by
  let B := lengthBox a b
  have hB : MeasurableSet B := measurableSet_lengthBox a b
  have hΨ : Measurable (fun z : Fin d → PositiveSizeSurplus ↦ H (fun i ↦ (z i).1.val)) := by
    apply hH.comp
    apply measurable_pi_lambda
    intro i
    exact measurable_subtype_coe.comp (measurable_fst.comp (measurable_pi_apply i))
  have hs (f : Path) : sourceSum lambda marks (B.indicator H) f =
      ∑' e : Fin d → ℚ,
        if BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e f then
          (∏ i, BrownianExcursionTuplePoissonWeights.poissonWeight
            (excursionArea (e i : ℝ) lambda f) (marks i)) *
              H (fun i ↦ (markedTuple lambda marks e f i).1.val) else 0 := by
    change (∑' e : Fin d → ℚ,
      if Function.Injective e ∧ ∀ i, Representative (driftedReflectionPath lambda f) (e i)
      then B.indicator H (fun i ↦ lengthValue lambda (e i) f) *
        ∏ i, BrownianExcursionTuplePoissonWeights.poissonWeight
          (excursionArea (e i : ℝ) lambda f) (marks i) else 0) = _
    apply tsum_congr
    intro e
    by_cases hg : Function.Injective e ∧
        ∀ i, Representative (driftedReflectionPath lambda f) (e i)
    · by_cases hb : (fun i ↦ lengthValue lambda (e i) f) ∈ B
      · have he : BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e f :=
          ⟨hg.1,fun i ↦ ⟨hg.2 i,hb i⟩⟩
        have hp (i : Fin d) : 0 < lengthValue lambda (e i) f := (ha i).trans_le (hb i).1
        have ht : (fun i ↦ (markedTuple lambda marks e f i).1.val) =
            fun i ↦ lengthValue lambda (e i) f :=
          funext (markedTuple_size lambda marks e f hp)
        rw [if_pos hg,indicator_of_mem hb,if_pos he,ht,mul_comm]
      · have he : ¬BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e f :=
          fun he ↦ hb (fun i ↦ (he.2 i).2)
        rw [if_pos hg,indicator_of_notMem hb,if_neg he,zero_mul]
    · have he : ¬BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e f :=
        fun he ↦ hg ⟨he.1,fun i ↦ (he.2 i).1⟩
      rw [if_neg hg,if_neg he]
  rw [windowLaw_factorial_test_complete_area_formula lambda (windowSet a b marks)
    (isCompact_windowSet a b marks ha) a b marks ha (cells_subset_windowSet a b marks) _ hΨ,
    ← lintegral_congr hs,actual_ordered_source_factorial_density lambda marks _ (hH.indicator hB)]
  change (∫⁻ xs in positiveOrthant d, ENNReal.ofReal (density 1 1 lambda xs marks)*B.indicator H xs) =
    ∫⁻ xs in B, ENNReal.ofReal (density 1 1 lambda xs marks)*H xs
  rw [← lintegral_indicator (measurableSet_positiveOrthant d),← lintegral_indicator hB]
  apply lintegral_congr
  intro xs
  by_cases hb : xs ∈ B
  · have hp : xs ∈ positiveOrthant d := fun i ↦ (ha i).trans_le (hb i).1
    rw [indicator_of_mem hp,indicator_of_mem hb,indicator_of_mem hb]
  · by_cases hp : xs ∈ positiveOrthant d
    · rw [indicator_of_mem hp,indicator_of_notMem hb,indicator_of_notMem hb,mul_zero]
    · rw [indicator_of_notMem hp,indicator_of_notMem hb]

end PerronWright.BrownianActualFactorialDensity
