import PerronWright.Probability.BrownianExcursionRectangleFactorials

/-!
# Usual mixed descending factorials of the actual full-process counts

Repeated surplus labels are handled by their exact slot multiplicities.
The rectangle factorial therefore reduces to the usual mixed count
polynomial, and its actual Brownian window expectation has the complete
excursion Poisson area weights in every order.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionMixedCountFactorials

open BrownianPathLaw BrownianFullHorizonExcursionAreas ComponentGlobalPointProcess
open BrownianExcursionCampbellWeights (cell)
open BrownianExcursionRectangleFactorials
open FinitePointMeasureCompact FinitePointMeasureRectangleFactorials

variable {d R : ℕ}

theorem surplus_cells_pairwise_disjoint (a b : ℝ) :
    Pairwise (fun r s : Fin (R+1) ↦ Disjoint (cell a b r.val) (cell a b s.val)) := by
  intro r s hrs
  apply Set.disjoint_left.mpr
  intro z hr hs
  exact hrs (Fin.ext (hr.2.symm.trans hs.2))

def occurrences (r : Fin d → Fin (R+1)) (s : Fin (R+1)) : ℕ :=
  Fintype.card {i : Fin d // r i = s}

def mixedStatistic (a b : ℝ) (r : Fin d → Fin (R+1))
    (η : PointMeasure PositiveSizeSurplus) : ℝ≥0∞ :=
  (∏ s : Fin (R+1), (count η (cell a b s.val)).descFactorial (occurrences r s) : ℕ)

theorem factorialStatistic_eq_mixedStatistic (a b : ℝ) (r : Fin d → Fin (R+1))
    (η : PointMeasure PositiveSizeSurplus) :
    factorialStatistic (fun _ ↦ a) (fun _ ↦ b) (fun i ↦ (r i).val) η =
      mixedStatistic a b r η := by
  unfold factorialStatistic mixedStatistic occurrences cells
  simpa only [Fintype.card_eq_nat_card] using
    congrArg (fun n : ℕ ↦ (n : ℝ≥0∞))
    (rectangleFactorial_disjoint_labels η (fun s : Fin (R+1) ↦ cell a b s.val) r
      (surplus_cells_pairwise_disjoint a b)
      (fun s ↦ BrownianExcursionCampbellWeights.measurableSet_cell a b s.val))

theorem measurable_mixedStatistic (a b : ℝ) (r : Fin d → Fin (R+1)) :
    Measurable (mixedStatistic a b r) := by
  have h : mixedStatistic a b r = factorialStatistic (fun _ ↦ a) (fun _ ↦ b)
      (fun i ↦ (r i).val) := by
    funext η
    exact (factorialStatistic_eq_mixedStatistic a b r η).symm
  rw [h]
  exact measurable_factorialStatistic _ _ _

theorem cells_subset_common_window (a b : ℝ) (r : Fin d → Fin (R+1)) (i : Fin d) :
    cells (fun _ ↦ a) (fun _ ↦ b) (fun j ↦ (r j).val) i ⊆ positiveWindowSet a b R := by
  intro z hz
  change z.1.val ∈ Icc a b ∧ z.2 ≤ R
  exact ⟨hz.1.1,hz.2 ▸ Nat.le_of_lt_succ (r i).isLt⟩

/-- The familiar mixed count factorial of the genuine common compact
window law, with arbitrary repeated surplus labels and every order. -/
theorem windowLaw_mixed_factorial_formula (lambda a b : ℝ) (ha : 0 < a)
    (r : Fin d → Fin (R+1)) :
    (∫⁻ η, mixedStatistic a b r η
      ∂(BrownianExcursionCompactWindows.law lambda (positiveWindowSet a b R)
        (isCompact_positiveWindowSet a b R ha) : Measure _)) =
    ∫⁻ f, ∑' e : Fin d → ℚ,
      if BrownianExcursionTuplePoissonWeights.sourceEvent lambda (fun _ ↦ a) (fun _ ↦ b) e f then
        ∏ i, BrownianExcursionTuplePoissonWeights.poissonWeight
          (excursionArea (e i : ℝ) lambda f) ((r i).val) else 0 ∂pathLaw := by
  simpa only [factorialStatistic_eq_mixedStatistic] using
    windowLaw_rectangle_factorial_complete_area_formula lambda (positiveWindowSet a b R)
      (isCompact_positiveWindowSet a b R ha) (fun _ ↦ a) (fun _ ↦ b) (fun i ↦ (r i).val)
      (fun _ ↦ ha) (cells_subset_common_window a b r)

theorem windowLaw_mixed_factorial_original_source (lambda a b : ℝ) (ha : 0 < a)
    (r : Fin d → Fin (R+1)) :
    (∫⁻ η, mixedStatistic a b r η
      ∂(BrownianExcursionCompactWindows.law lambda (positiveWindowSet a b R)
        (isCompact_positiveWindowSet a b R ha) : Measure _)) =
    ∫⁻ x, ∑' e : Fin d → ℚ,
      BrownianExcursionTuplePoissonWeights.weight lambda (fun _ ↦ a) (fun _ ↦ b)
        (fun i ↦ (r i).val) e (measurablePath x) ∂BrownianGaussianSkeleton.rationalLaw := by
  simpa only [factorialStatistic_eq_mixedStatistic] using
    windowLaw_rectangle_factorial_original_source lambda (positiveWindowSet a b R)
      (isCompact_positiveWindowSet a b R ha) (fun _ ↦ a) (fun _ ↦ b) (fun i ↦ (r i).val)
      (fun _ ↦ ha) (cells_subset_common_window a b r)

end PerronWright.BrownianExcursionMixedCountFactorials
