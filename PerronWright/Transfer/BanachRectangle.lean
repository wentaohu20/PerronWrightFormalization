import Mathlib.Analysis.Complex.CauchyIntegral

/-!
Exact rectangular contour identities for complex Banach-valued analytic
functions.  They are the vector-valued counterpart of `DeltaMixedContour`
and do not identify a keyhole contour with a Taylor coefficient.
-/

open Complex MeasureTheory Set
noncomputable section

namespace PerronWright.Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def banachRectBoundary (F : ℂ → E) (x₀ x₁ y₀ y₁ : ℝ) : E :=
  (∫ x in x₀..x₁, F (x + y₀ * I)) -
    (∫ x in x₀..x₁, F (x + y₁ * I)) +
    I • (∫ y in y₀..y₁, F (x₁ + y * I)) -
    I • (∫ y in y₀..y₁, F (x₀ + y * I))

/-- Cauchy--Goursat on an actual rectangle, with values in an arbitrary
complex Banach space. -/
theorem banachRectBoundary_eq_zero_of_differentiableOn
    {F : ℂ → E} {x₀ x₁ y₀ y₁ : ℝ}
    (hF : DifferentiableOn ℂ F
      (Set.uIcc x₀ x₁ ×ℂ Set.uIcc y₀ y₁)) :
    banachRectBoundary F x₀ x₁ y₀ y₁ = 0 := by
  unfold banachRectBoundary
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    F ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ hF

/-- A shared vertical edge cancels in the vector-valued boundary integral. -/
theorem banachRectBoundary_split_x {F : ℂ → E} (hF : Continuous F)
    (x₀ xm x₁ y₀ y₁ : ℝ) :
    banachRectBoundary F x₀ x₁ y₀ y₁ =
      banachRectBoundary F x₀ xm y₀ y₁ +
        banachRectBoundary F xm x₁ y₀ y₁ := by
  have hcont (y : ℝ) : Continuous (fun x : ℝ => F (x + y * I)) := by
    fun_prop
  have hbot := intervalIntegral.integral_add_adjacent_intervals
    ((hcont y₀).intervalIntegrable (μ := volume) x₀ xm)
    ((hcont y₀).intervalIntegrable (μ := volume) xm x₁)
  have htop := intervalIntegral.integral_add_adjacent_intervals
    ((hcont y₁).intervalIntegrable (μ := volume) x₀ xm)
    ((hcont y₁).intervalIntegrable (μ := volume) xm x₁)
  unfold banachRectBoundary
  rw [← hbot, ← htop]
  abel

/-- A shared horizontal edge cancels in the vector-valued boundary integral. -/
theorem banachRectBoundary_split_y {F : ℂ → E} (hF : Continuous F)
    (x₀ x₁ y₀ ym y₁ : ℝ) :
    banachRectBoundary F x₀ x₁ y₀ y₁ =
      banachRectBoundary F x₀ x₁ y₀ ym +
        banachRectBoundary F x₀ x₁ ym y₁ := by
  have hcont (x : ℝ) : Continuous (fun y : ℝ => F (x + y * I)) := by
    fun_prop
  have hright := intervalIntegral.integral_add_adjacent_intervals
    ((hcont x₁).intervalIntegrable (μ := volume) y₀ ym)
    ((hcont x₁).intervalIntegrable (μ := volume) ym y₁)
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    ((hcont x₀).intervalIntegrable (μ := volume) y₀ ym)
    ((hcont x₀).intervalIntegrable (μ := volume) ym y₁)
  unfold banachRectBoundary
  rw [← hright, ← hleft]
  simp only [smul_add]
  abel

/-- All internal vertical edges cancel in a finite vector-valued strip. -/
theorem banachRectBoundary_sum_x {F : ℂ → E} (hF : Continuous F)
    (x : ℕ → ℝ) (k : ℕ) (y₀ y₁ : ℝ) :
    ∑ i ∈ Finset.range k,
        banachRectBoundary F (x i) (x (i + 1)) y₀ y₁ =
      banachRectBoundary F (x 0) (x k) y₀ y₁ := by
  induction k with
  | zero => simp [banachRectBoundary]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      exact (banachRectBoundary_split_x hF
        (x 0) (x k) (x (k + 1)) y₀ y₁).symm

/-- All internal horizontal edges cancel in a finite vector-valued strip. -/
theorem banachRectBoundary_sum_y {F : ℂ → E} (hF : Continuous F)
    (y : ℕ → ℝ) (k : ℕ) (x₀ x₁ : ℝ) :
    ∑ j ∈ Finset.range k,
        banachRectBoundary F x₀ x₁ (y j) (y (j + 1)) =
      banachRectBoundary F x₀ x₁ (y 0) (y k) := by
  induction k with
  | zero => simp [banachRectBoundary]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      exact (banachRectBoundary_split_y hF
        x₀ x₁ (y 0) (y k) (y (k + 1))).symm

/-- A finite rectangular grid has just its outer boundary after exact
algebraic cancellation of every internal edge. -/
theorem banachRectBoundary_grid_sum {F : ℂ → E} (hF : Continuous F)
    (x y : ℕ → ℝ) (k m : ℕ) :
    ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range m,
        banachRectBoundary F (x i) (x (i + 1)) (y j) (y (j + 1)) =
      banachRectBoundary F (x 0) (x k) (y 0) (y m) := by
  calc
    _ = ∑ i ∈ Finset.range k,
        banachRectBoundary F (x i) (x (i + 1)) (y 0) (y m) := by
          apply Finset.sum_congr rfl
          intro i _
          exact banachRectBoundary_sum_y hF y m (x i) (x (i + 1))
    _ = _ := banachRectBoundary_sum_x hF x k (y 0) (y m)

end PerronWright.Transfer
