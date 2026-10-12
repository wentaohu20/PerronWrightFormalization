import PerronWright.Probability.BrownianExcursionTuplePoissonWeights
import PerronWright.Probability.BrownianExcursionAtomicMeasure

/-!
# Genuine full-excursion tuple weights with arbitrary coupled Borel tests

The test is evaluated on the actual size--surplus atoms. Conditional
count probabilities are the proved independent full-area Poisson law.
All formulas use nonnegative extended integrals and Tonelli.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionTupleTests

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionSection
open BrownianExcursionAtomicMeasure BrownianExcursionPointProcessLaw
open BrownianFullHorizonPoissonMarks BrownianFullHorizonExcursionAreas
open ComponentGlobalPointProcess

variable {d : ℕ}

def markedTuple (lambda : ℝ) (r : Fin d → ℕ) (e : Fin d → ℚ) (f : Path) :
    Fin d → PositiveSizeSurplus :=
  fun i ↦ atom lambda (f,fun _ : ℚ ↦ r i) (e i)

theorem measurable_markedTuple (lambda : ℝ) (r : Fin d → ℕ) (e : Fin d → ℚ) :
    Measurable (markedTuple lambda r e) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_atom lambda (e i)).comp (measurable_id.prodMk measurable_const)

theorem markedTuple_eq_actual_atoms (lambda : ℝ) (r : Fin d → ℕ) (e : Fin d → ℚ)
    (p : Path × (ℕ → ℕ)) (hm : ∀ i, rationalCount p.2 (e i) = r i) :
    markedTuple lambda r e p.1 = fun i ↦ atom lambda (pathInput p) (e i) := by
  funext i
  apply Prod.ext
  · rfl
  · exact (hm i).symm

theorem markedTuple_size (lambda : ℝ) (r : Fin d → ℕ) (e : Fin d → ℚ) (f : Path)
    (hp : ∀ i, 0 < BrownianExcursionWindowPointMeasure.lengthValue lambda (e i) f) (i : Fin d) :
    (markedTuple lambda r e f i).1.val =
      BrownianExcursionWindowPointMeasure.lengthValue lambda (e i) f := by
  simp only [markedTuple,atom,positiveSize,dif_pos (hp i)]

theorem markedTuple_surplus (lambda : ℝ) (r : Fin d → ℕ) (e : Fin d → ℚ) (f : Path) (i : Fin d) :
    (markedTuple lambda r e f i).2 = r i := rfl

def contribution (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞)
    (e : Fin d → ℚ) (p : Path × (ℕ → ℕ)) : ℝ≥0∞ :=
  BrownianExcursionTuplePoissonWeights.contribution lambda a b r e p * Ψ (markedTuple lambda r e p.1)

theorem contribution_eq_actual_tuple (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (e : Fin d → ℚ) (p : Path × (ℕ → ℕ)) :
    contribution lambda a b r Ψ e p =
      if BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e p.1 ∧
        ∀ i, rationalCount p.2 (e i) = r i then
        Ψ (fun i ↦ atom lambda (pathInput p) (e i)) else 0 := by
  by_cases h : BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e p.1 ∧
      ∀ i, rationalCount p.2 (e i) = r i
  · simp only [contribution,BrownianExcursionTuplePoissonWeights.contribution,if_pos h,one_mul]
    rw [markedTuple_eq_actual_atoms lambda r e p h.2]
  · simp only [contribution,BrownianExcursionTuplePoissonWeights.contribution,if_neg h,zero_mul]

theorem measurable_contribution (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (hΨ : Measurable Ψ) (e : Fin d → ℚ) :
    Measurable (contribution lambda a b r Ψ e) :=
  (BrownianExcursionTuplePoissonWeights.measurable_contribution lambda a b r e).mul
    (hΨ.comp ((measurable_markedTuple lambda r e).comp measurable_fst))

def weight (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (e : Fin d → ℚ) (f : Path) : ℝ≥0∞ :=
  BrownianExcursionTuplePoissonWeights.weight lambda a b r e f * Ψ (markedTuple lambda r e f)

theorem measurable_weight (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (hΨ : Measurable Ψ) (e : Fin d → ℚ) :
    Measurable (weight lambda a b r Ψ e) :=
  (BrownianExcursionTuplePoissonWeights.measurable_weight lambda a b r e).mul
    (hΨ.comp (measurable_markedTuple lambda r e))

theorem weight_eq_complete_area (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (e : Fin d → ℚ) (f : Path) :
    weight lambda a b r Ψ e f =
      if BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e f then
        (∏ i, BrownianExcursionTuplePoissonWeights.poissonWeight
          (excursionArea (e i : ℝ) lambda f) (r i)) * Ψ (markedTuple lambda r e f) else 0 := by
  rw [weight,BrownianExcursionTuplePoissonWeights.weight_eq_full_area]
  split_ifs <;> simp

theorem conditional_contribution (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (e : Fin d → ℚ) (f : Path) :
    (∫⁻ m, contribution lambda a b r Ψ e (f,m) ∂markLaw lambda f) =
      weight lambda a b r Ψ e f := by
  unfold contribution weight
  have hm : Measurable (fun m : ℕ → ℕ ↦
      BrownianExcursionTuplePoissonWeights.contribution lambda a b r e (f,m)) := by
    simpa only [Function.comp_def,id_eq] using
      (BrownianExcursionTuplePoissonWeights.measurable_contribution lambda a b r e).comp
        ((measurable_const : Measurable (fun _ : ℕ → ℕ ↦ f)).prodMk measurable_id)
  change (∫⁻ m, BrownianExcursionTuplePoissonWeights.contribution lambda a b r e (f,m) *
    Ψ (markedTuple lambda r e f) ∂markLaw lambda f) = _
  rw [lintegral_mul_const _ hm,
    BrownianExcursionTuplePoissonWeights.conditional_contribution]

def statistic (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (p : Path × (ℕ → ℕ)) : ℝ≥0∞ :=
  ∑' e : Fin d → ℚ, contribution lambda a b r Ψ e p

theorem measurable_statistic (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    Measurable (statistic lambda a b r Ψ) :=
  Measurable.tsum (fun e ↦ measurable_contribution lambda a b r Ψ hΨ e)

theorem conditional_statistic (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (hΨ : Measurable Ψ) (f : Path) :
    (∫⁻ m, statistic lambda a b r Ψ (f,m) ∂markLaw lambda f) =
      ∑' e : Fin d → ℚ, weight lambda a b r Ψ e f := by
  change (∫⁻ m, ∑' e : Fin d → ℚ, contribution lambda a b r Ψ e (f,m) ∂markLaw lambda f) = _
  rw [lintegral_tsum]
  · exact tsum_congr (fun e ↦ conditional_contribution lambda a b r Ψ e f)
  · intro e
    exact ((measurable_contribution lambda a b r Ψ hΨ e).comp
      (measurable_const.prodMk measurable_id)).aemeasurable

theorem joint_expectation_eq_source_weights (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (Ψ : (Fin d → PositiveSizeSurplus) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ p, statistic lambda a b r Ψ p ∂pathJointLaw lambda) =
      ∫⁻ f, ∑' e : Fin d → ℚ, weight lambda a b r Ψ e f ∂pathLaw := by
  rw [pathJointLaw,CountablePoissonKernel.jointLaw,
    Measure.lintegral_compProd (measurable_statistic lambda a b r Ψ hΨ)]
  exact lintegral_congr (conditional_statistic lambda a b r Ψ hΨ)

end PerronWright.BrownianExcursionTupleTests
