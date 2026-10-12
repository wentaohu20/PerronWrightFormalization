import PerronWright.Probability.FinitePointMeasureFactorialKernel
import PerronWright.Probability.BrownianExcursionTupleTests
import PerronWright.Probability.BrownianExcursionRectangleFactorials

/-!
# Actual intrinsic coupled-test factorial expectation of full excursions

The test statistic is the integral against the intrinsic factorial
measure of the actual finite-window point measure, not a tuple law
declared to be intrinsic. All finite atom representations agree, the
weak-Borel statistic is measurable, and the exceptional path gate is
removed almost everywhere using the constructed Brownian source.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionFactorialTests

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionSection
open BrownianExcursionAtomicMeasure BrownianExcursionPointProcessLaw
open BrownianExcursionWindowPointMeasure BrownianFullHorizonPoissonMarks
open BrownianFullHorizonExcursionAreas ComponentGlobalPointProcess
open FinitePointMeasureCompact FinitePointMeasureFactorialKernel
open BrownianExcursionRectangleFactorials

variable {d : ℕ}

def factorialTest (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (η : PointMeasure PositiveSizeSurplus) : ℝ≥0∞ :=
  rectangleTest (cells a b r) Ψ η

theorem measurable_factorialTest (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    Measurable (factorialTest a b r Ψ) :=
  measurable_rectangleTest (cells a b r) (measurableSet_cells a b r) Ψ hΨ

theorem selected_tuple_iff (lambda : ℝ) (K : Set PositiveSizeSurplus)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (hK : ∀ i, cells a b r i ⊆ K) (p : Path × (ℕ → ℕ)) (hg : Good lambda p.1)
    (e : Fin d → ℚ) :
    (Function.Injective e ∧ ∀ i,
      e i ∈ BrownianExcursionCompactWindows.selection lambda K (pathInput p) ∧
      atom lambda (pathInput p) (e i) ∈ cells a b r i) ↔
      BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e p.1 ∧
        ∀ i, rationalCount p.2 (e i) = r i := by
  constructor
  · rintro ⟨he,hs⟩
    have ht i := (selection_cell_iff lambda K a b r ha hK p hg i (e i)).mp (hs i)
    exact ⟨⟨he,fun i ↦ ⟨(ht i).1,(ht i).2.1⟩⟩,fun i ↦ (ht i).2.2⟩
  · rintro ⟨⟨he,hs⟩,hm⟩
    exact ⟨he,fun i ↦ (selection_cell_iff lambda K a b r ha hK p hg i (e i)).mpr
      ⟨(hs i).1,(hs i).2,hm i⟩⟩

theorem window_factorialTest_eq_tuple_statistic (lambda : ℝ)
    (K : Set PositiveSizeSurplus) (hKc : IsCompact K)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (hK : ∀ i, cells a b r i ⊆ K)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (hΨ : Measurable Ψ)
    (p : Path × (ℕ → ℕ)) (hg : Good lambda p.1) :
    factorialTest a b r Ψ (BrownianExcursionCompactWindows.window lambda K (pathInput p)) =
      BrownianExcursionTupleTests.statistic lambda a b r Ψ p := by
  unfold factorialTest BrownianExcursionCompactWindows.window
  rw [rectangleTest_pointMeasure _ _ _
    (BrownianExcursionCompactWindows.finite_selection lambda K hKc (pathInput p))
    _ (measurableSet_cells a b r) Ψ hΨ]
  unfold BrownianExcursionTupleTests.statistic
  apply tsum_congr
  intro e
  rw [BrownianExcursionTupleTests.contribution_eq_actual_tuple]
  simp only [selected_tuple_iff lambda K a b r ha hK p hg e]

theorem ae_window_factorialTest_eq_tuple_statistic (lambda : ℝ)
    (K : Set PositiveSizeSurplus) (hKc : IsCompact K)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (hK : ∀ i, cells a b r i ⊆ K)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∀ᵐ p ∂pathJointLaw lambda,
      factorialTest a b r Ψ (BrownianExcursionCompactWindows.window lambda K (pathInput p)) =
        BrownianExcursionTupleTests.statistic lambda a b r Ψ p := by
  have hg : ∀ᵐ p ∂pathJointLaw lambda, Good lambda p.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [pathJointLaw_source]
    exact ae_good lambda
  exact hg.mono (fun p hp ↦ window_factorialTest_eq_tuple_statistic lambda K hKc a b r ha hK Ψ hΨ p hp)

/-- Genuine intrinsic finite-window factorial test expectation, not a
postulated factorial-moment or conditional-independence identity. -/
theorem windowLaw_factorial_test_formula (lambda : ℝ)
    (K : Set PositiveSizeSurplus) (hKc : IsCompact K)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (hK : ∀ i, cells a b r i ⊆ K)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ η, factorialTest a b r Ψ η
      ∂(BrownianExcursionCompactWindows.law lambda K hKc : Measure _)) =
    ∫⁻ f, ∑' e : Fin d → ℚ, BrownianExcursionTupleTests.weight lambda a b r Ψ e f ∂pathLaw := by
  change (∫⁻ η, factorialTest a b r Ψ η
    ∂((pathJointLaw lambda).map (BrownianExcursionCompactWindows.window lambda K ∘ pathInput))) = _
  rw [lintegral_map (measurable_factorialTest a b r Ψ hΨ)
    ((BrownianExcursionCompactWindows.measurable_window lambda K hKc.measurableSet).comp measurable_pathInput)]
  calc
    _ = ∫⁻ p, BrownianExcursionTupleTests.statistic lambda a b r Ψ p ∂pathJointLaw lambda :=
      lintegral_congr_ae (ae_window_factorialTest_eq_tuple_statistic lambda K hKc a b r ha hK Ψ hΨ)
    _ = _ := BrownianExcursionTupleTests.joint_expectation_eq_source_weights lambda a b r Ψ hΨ

theorem windowLaw_factorial_test_complete_area_formula (lambda : ℝ)
    (K : Set PositiveSizeSurplus) (hKc : IsCompact K)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (hK : ∀ i, cells a b r i ⊆ K)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ η, factorialTest a b r Ψ η
      ∂(BrownianExcursionCompactWindows.law lambda K hKc : Measure _)) =
    ∫⁻ f, ∑' e : Fin d → ℚ,
      if BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e f then
        (∏ i, BrownianExcursionTuplePoissonWeights.poissonWeight
          (excursionArea (e i : ℝ) lambda f) (r i)) *
            Ψ (BrownianExcursionTupleTests.markedTuple lambda r e f) else 0 ∂pathLaw := by
  rw [windowLaw_factorial_test_formula lambda K hKc a b r ha hK Ψ hΨ]
  exact lintegral_congr (fun f ↦ tsum_congr (fun e ↦
    BrownianExcursionTupleTests.weight_eq_complete_area lambda a b r Ψ e f))

theorem windowLaw_factorial_test_original_source (lambda : ℝ)
    (K : Set PositiveSizeSurplus) (hKc : IsCompact K)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (hK : ∀ i, cells a b r i ⊆ K)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ η, factorialTest a b r Ψ η
      ∂(BrownianExcursionCompactWindows.law lambda K hKc : Measure _)) =
    ∫⁻ x, ∑' e : Fin d → ℚ,
      if BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e (measurablePath x) then
        (∏ i, BrownianExcursionTuplePoissonWeights.poissonWeight
          (excursionArea (e i : ℝ) lambda (measurablePath x)) (r i)) *
            Ψ (BrownianExcursionTupleTests.markedTuple lambda r e (measurablePath x)) else 0
      ∂BrownianGaussianSkeleton.rationalLaw := by
  rw [windowLaw_factorial_test_formula lambda K hKc a b r ha hK Ψ hΨ,pathLaw,
    lintegral_map (Measurable.tsum (fun e ↦
      BrownianExcursionTupleTests.measurable_weight lambda a b r Ψ hΨ e)) measurable_measurablePath]
  exact lintegral_congr (fun x ↦ tsum_congr (fun e ↦
    BrownianExcursionTupleTests.weight_eq_complete_area lambda a b r Ψ e (measurablePath x)))

/-- Arbitrary Borel nonnegative coupled test, every order, and the
minimal genuine compact union window. Only positive size lower bounds
are required; neither moment finiteness nor excursion density is input. -/
theorem factorial_test_formula (lambda : ℝ)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ η, factorialTest a b r Ψ η
      ∂(BrownianExcursionCompactWindows.law lambda (windowSet a b r)
        (isCompact_windowSet a b r ha) : Measure _)) =
    ∫⁻ x, ∑' e : Fin d → ℚ,
      if BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e (measurablePath x) then
        (∏ i, BrownianExcursionTuplePoissonWeights.poissonWeight
          (excursionArea (e i : ℝ) lambda (measurablePath x)) (r i)) *
            Ψ (BrownianExcursionTupleTests.markedTuple lambda r e (measurablePath x)) else 0
      ∂BrownianGaussianSkeleton.rationalLaw :=
  windowLaw_factorial_test_original_source lambda (windowSet a b r)
    (isCompact_windowSet a b r ha) a b r ha (cells_subset_windowSet a b r) Ψ hΨ

theorem continuous_factorial_test_formula (lambda : ℝ)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0) (hΨ : Continuous Ψ) :
    (∫⁻ η, factorialTest a b r (fun z ↦ (Ψ z : ℝ≥0∞)) η
      ∂(BrownianExcursionCompactWindows.law lambda (windowSet a b r)
        (isCompact_windowSet a b r ha) : Measure _)) =
    ∫⁻ x, ∑' e : Fin d → ℚ,
      if BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e (measurablePath x) then
        (∏ i, BrownianExcursionTuplePoissonWeights.poissonWeight
          (excursionArea (e i : ℝ) lambda (measurablePath x)) (r i)) *
            (Ψ (BrownianExcursionTupleTests.markedTuple lambda r e (measurablePath x)) : ℝ≥0∞) else 0
      ∂BrownianGaussianSkeleton.rationalLaw :=
  factorial_test_formula lambda a b r ha _ (ENNReal.continuous_coe.measurable.comp hΨ.measurable)

end PerronWright.BrownianExcursionFactorialTests
