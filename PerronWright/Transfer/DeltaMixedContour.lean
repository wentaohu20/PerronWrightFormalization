import Mathlib.Analysis.Complex.CauchyIntegral

/-!
Rectangular subdivision identities for a future mixed-center keyhole
deformation.  These are exact contour identities with real interval
integrals; no coefficient contour equivalence is assumed.
-/

open Complex MeasureTheory Set
noncomputable section

namespace PerronWright.Transfer

def rectBoundary (F : ℂ → ℂ) (x₀ x₁ y₀ y₁ : ℝ) : ℂ :=
  (∫ x in x₀..x₁, F (x + y₀ * I)) -
    (∫ x in x₀..x₁, F (x + y₁ * I)) +
    I • (∫ y in y₀..y₁, F (x₁ + y * I)) -
    I • (∫ y in y₀..y₁, F (x₀ + y * I))

/-- Cauchy--Goursat for the genuine oriented rectangle boundary. -/
theorem rectBoundary_eq_zero_of_differentiableOn {F : ℂ → ℂ}
    {x₀ x₁ y₀ y₁ : ℝ}
    (hF : DifferentiableOn ℂ F
      (Set.uIcc x₀ x₁ ×ℂ Set.uIcc y₀ y₁)) :
    rectBoundary F x₀ x₁ y₀ y₁ = 0 := by
  unfold rectBoundary
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    F ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ hF

/-- On subdividing a rectangle by a vertical line, the common vertical
edge cancels exactly. -/
theorem rectBoundary_split_x {F : ℂ → ℂ} (hF : Continuous F)
    (x₀ xm x₁ y₀ y₁ : ℝ) :
    rectBoundary F x₀ x₁ y₀ y₁ =
      rectBoundary F x₀ xm y₀ y₁ + rectBoundary F xm x₁ y₀ y₁ := by
  have hcont (y : ℝ) : Continuous (fun x : ℝ => F (x + y * I)) := by
    fun_prop
  have hbot := intervalIntegral.integral_add_adjacent_intervals
    ((hcont y₀).intervalIntegrable (μ := volume) x₀ xm)
    ((hcont y₀).intervalIntegrable (μ := volume) xm x₁)
  have htop := intervalIntegral.integral_add_adjacent_intervals
    ((hcont y₁).intervalIntegrable (μ := volume) x₀ xm)
    ((hcont y₁).intervalIntegrable (μ := volume) xm x₁)
  unfold rectBoundary
  rw [← hbot, ← htop]
  simp only [smul_eq_mul]
  ring

/-- On subdividing a rectangle by a horizontal line, the common horizontal
edge cancels exactly. -/
theorem rectBoundary_split_y {F : ℂ → ℂ} (hF : Continuous F)
    (x₀ x₁ y₀ ym y₁ : ℝ) :
    rectBoundary F x₀ x₁ y₀ y₁ =
      rectBoundary F x₀ x₁ y₀ ym + rectBoundary F x₀ x₁ ym y₁ := by
  have hcont (x : ℝ) : Continuous (fun y : ℝ => F (x + y * I)) := by
    fun_prop
  have hright := intervalIntegral.integral_add_adjacent_intervals
    ((hcont x₁).intervalIntegrable (μ := volume) y₀ ym)
    ((hcont x₁).intervalIntegrable (μ := volume) ym y₁)
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    ((hcont x₀).intervalIntegrable (μ := volume) y₀ ym)
    ((hcont x₀).intervalIntegrable (μ := volume) ym y₁)
  unfold rectBoundary
  rw [← hright, ← hleft]
  simp only [smul_eq_mul]
  ring

/-- All internal vertical edges cancel in a finite strip of rectangles. -/
theorem rectBoundary_sum_x {F : ℂ → ℂ} (hF : Continuous F)
    (x : ℕ → ℝ) (k : ℕ) (y₀ y₁ : ℝ) :
    ∑ i ∈ Finset.range k,
        rectBoundary F (x i) (x (i + 1)) y₀ y₁ =
      rectBoundary F (x 0) (x k) y₀ y₁ := by
  induction k with
  | zero => simp [rectBoundary]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      exact (rectBoundary_split_x hF (x 0) (x k) (x (k + 1)) y₀ y₁).symm

/-- All internal horizontal edges cancel in a finite strip. -/
theorem rectBoundary_sum_y {F : ℂ → ℂ} (hF : Continuous F)
    (y : ℕ → ℝ) (k : ℕ) (x₀ x₁ : ℝ) :
    ∑ j ∈ Finset.range k,
        rectBoundary F x₀ x₁ (y j) (y (j + 1)) =
      rectBoundary F x₀ x₁ (y 0) (y k) := by
  induction k with
  | zero => simp [rectBoundary]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      exact (rectBoundary_split_y hF x₀ x₁ (y 0) (y k) (y (k + 1))).symm

/-- A complete finite rectangular grid has exactly the boundary integral
of its outer rectangle; every internal edge cancels algebraically. -/
theorem rectBoundary_grid_sum {F : ℂ → ℂ} (hF : Continuous F)
    (x y : ℕ → ℝ) (k m : ℕ) :
    ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range m,
        rectBoundary F (x i) (x (i + 1)) (y j) (y (j + 1)) =
      rectBoundary F (x 0) (x k) (y 0) (y m) := by
  calc
    _ = ∑ i ∈ Finset.range k,
        rectBoundary F (x i) (x (i + 1)) (y 0) (y m) := by
          apply Finset.sum_congr rfl
          intro i _
          exact rectBoundary_sum_y hF y m (x i) (x (i + 1))
    _ = _ := rectBoundary_sum_x hF x k (y 0) (y m)


end PerronWright.Transfer
