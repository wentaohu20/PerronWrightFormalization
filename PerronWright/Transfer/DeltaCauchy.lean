import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
The concrete Cauchy--Goursat identity on a logarithmic sector around the
singularity `z = 1`.  The map `w ↦ 1 + exp w` sends the four sides of a
rectangle to two radial segments and two circular arcs.  This is genuine
contour deformation on that local sector, not an assumed interface.
-/

open Complex Set MeasureTheory
open scoped Interval
noncomputable section

namespace PerronWright.Transfer

def shiftedExp (w : ℂ) : ℂ := 1 + exp w

def transformedCauchy (F : ℂ → ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  F (shiftedExp w) * (shiftedExp w)⁻¹ ^ (n + 1) * exp w

theorem shiftedExp_differentiable : Differentiable ℂ shiftedExp := by
  intro w
  unfold shiftedExp
  fun_prop

theorem transformedCauchy_differentiableOn {F : ℂ → ℂ} {s : Set ℂ} {n : ℕ}
    (hF : ∀ w ∈ s, DifferentiableAt ℂ F (shiftedExp w))
    (hzero : ∀ w ∈ s, shiftedExp w ≠ 0) :
    DifferentiableOn ℂ (transformedCauchy F n) s := by
  intro w hw
  have hφ : DifferentiableAt ℂ shiftedExp w := shiftedExp_differentiable w
  have hcomp : DifferentiableAt ℂ (F ∘ shiftedExp) w :=
    (hF w hw).comp w hφ
  have hinv : DifferentiableAt ℂ (fun u => (shiftedExp u)⁻¹) w :=
    hφ.inv (hzero w hw)
  have hpow : DifferentiableAt ℂ (fun u => (shiftedExp u)⁻¹ ^ (n + 1)) w :=
    hinv.pow _
  have hexp : DifferentiableAt ℂ Complex.exp w := Complex.differentiable_exp w
  exact ((hcomp.mul hpow).mul hexp).differentiableWithinAt

/-- The four oriented integrals on the image of a logarithmic rectangle
sum to zero. The hypotheses are solely the actual local differentiability
and nonvanishing of the denominator on this rectangle. -/
theorem log_sector_boundary_zero {F : ℂ → ℂ} {n : ℕ}
    {x₀ x₁ y₀ y₁ : ℝ}
    (hF : ∀ w ∈ ([[x₀, x₁]] ×ℂ [[y₀, y₁]]),
      DifferentiableAt ℂ F (shiftedExp w))
    (hzero : ∀ w ∈ ([[x₀, x₁]] ×ℂ [[y₀, y₁]]),
      shiftedExp w ≠ 0) :
    (∫ x in x₀..x₁, transformedCauchy F n (x + y₀ * I)) -
      (∫ x in x₀..x₁, transformedCauchy F n (x + y₁ * I)) +
      I • (∫ y in y₀..y₁, transformedCauchy F n (x₁ + y * I)) -
      I • (∫ y in y₀..y₁, transformedCauchy F n (x₀ + y * I)) = 0 := by
  have hG := transformedCauchy_differentiableOn (n := n) hF hzero
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (transformedCauchy F n) ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ hG
  simpa using h

/-- A logarithmic radius strictly below `1` keeps the transformed
Cauchy denominator away from its pole at `z = 0`. -/
theorem shiftedExp_ne_zero_of_re_neg {w : ℂ} (hw : w.re < 0) :
    shiftedExp w ≠ 0 := by
  have hnorm : ‖exp w‖ < 1 := by
    rw [Complex.norm_exp]
    simpa only [← Real.exp_zero] using Real.exp_lt_exp.mpr hw
  intro hzero
  have heq : exp w = -(1 : ℂ) := by
    dsimp [shiftedExp] at hzero
    linear_combination hzero
  rw [heq, norm_neg, norm_one] at hnorm
  exact (lt_irrefl (1 : ℝ)) hnorm

/-- Local sector contour identity with no nonvanishing hypothesis: it is
proved from `x₁ < 0`, i.e. the outer radius around `1` is less than `1`. -/
theorem log_sector_boundary_zero_of_outer_lt_one {F : ℂ → ℂ} {n : ℕ}
    {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hx₁ : x₁ < 0)
    (hF : ∀ w ∈ ([[x₀, x₁]] ×ℂ [[y₀, y₁]]),
      DifferentiableAt ℂ F (shiftedExp w)) :
    (∫ x in x₀..x₁, transformedCauchy F n (x + y₀ * I)) -
      (∫ x in x₀..x₁, transformedCauchy F n (x + y₁ * I)) +
      I • (∫ y in y₀..y₁, transformedCauchy F n (x₁ + y * I)) -
      I • (∫ y in y₀..y₁, transformedCauchy F n (x₀ + y * I)) = 0 := by
  apply log_sector_boundary_zero hF
  intro w hw
  have hwre : w.re ≤ x₁ := by
    have h := hw.1
    have hmax : max x₀ x₁ = x₁ := max_eq_right hx
    exact hmax ▸ h.2
  exact shiftedExp_ne_zero_of_re_neg (lt_of_le_of_lt hwre hx₁)


end PerronWright.Transfer
