import PerronWright.Transfer.BanachRectangle
import PerronWright.Transfer.DeltaSideParam

/-!
The genuine logarithmic-sector Cauchy--Goursat identity with values in a
complex Banach space.  This supplies the local contour identity required
for field-derivative transfer; joining it to the outer circle centered at
zero remains a separate geometric step.
-/

open Complex Set MeasureTheory
open scoped Interval
noncomputable section

namespace PerronWright.Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def transformedBanachCauchy (F : ℂ → E) (n : ℕ) (w : ℂ) : E :=
  (exp w * (shiftedExp w)⁻¹ ^ (n + 1)) • F (shiftedExp w)

theorem transformedBanachCauchy_differentiableOn
    {F : ℂ → E} {s : Set ℂ} {n : ℕ}
    (hF : ∀ w ∈ s, DifferentiableAt ℂ F (shiftedExp w))
    (hzero : ∀ w ∈ s, shiftedExp w ≠ 0) :
    DifferentiableOn ℂ (transformedBanachCauchy F n) s := by
  intro w hw
  have hφ : DifferentiableAt ℂ shiftedExp w :=
    shiftedExp_differentiable w
  have hcomp : DifferentiableAt ℂ (F ∘ shiftedExp) w :=
    (hF w hw).comp w hφ
  have hinv : DifferentiableAt ℂ
      (fun u => (shiftedExp u)⁻¹) w :=
    hφ.inv (hzero w hw)
  have hpow : DifferentiableAt ℂ
      (fun u => (shiftedExp u)⁻¹ ^ (n + 1)) w :=
    hinv.pow _
  have hscalar : DifferentiableAt ℂ
      (fun u => exp u * (shiftedExp u)⁻¹ ^ (n + 1)) w :=
    (Complex.differentiable_exp w).mul hpow
  exact (hscalar.smul hcomp).differentiableWithinAt

/-- The actual four oriented Banach-valued integrals on a logarithmic
sector around `z=1` sum to zero. -/
theorem banach_log_sector_boundary_zero
    {F : ℂ → E} {n : ℕ} {x₀ x₁ y₀ y₁ : ℝ}
    (hF : ∀ w ∈ ([[x₀, x₁]] ×ℂ [[y₀, y₁]]),
      DifferentiableAt ℂ F (shiftedExp w))
    (hzero : ∀ w ∈ ([[x₀, x₁]] ×ℂ [[y₀, y₁]]),
      shiftedExp w ≠ 0) :
    banachRectBoundary (transformedBanachCauchy F n)
      x₀ x₁ y₀ y₁ = 0 :=
  banachRectBoundary_eq_zero_of_differentiableOn
    (transformedBanachCauchy_differentiableOn hF hzero)

/-- If the outer logarithmic radius is below one, the transformed
Cauchy denominator cannot hit zero, so the Banach-valued sector identity
needs no extra nonvanishing assumption. -/
theorem banach_log_sector_boundary_zero_of_outer_lt_one
    {F : ℂ → E} {n : ℕ} {x₀ x₁ y₀ y₁ : ℝ}
    (hx : x₀ ≤ x₁) (hx₁ : x₁ < 0)
    (hF : ∀ w ∈ ([[x₀, x₁]] ×ℂ [[y₀, y₁]]),
      DifferentiableAt ℂ F (shiftedExp w)) :
    banachRectBoundary (transformedBanachCauchy F n)
      x₀ x₁ y₀ y₁ = 0 := by
  apply banach_log_sector_boundary_zero hF
  intro w hw
  have hwre : w.re ≤ x₁ := by
    have h := hw.1
    have hmax : max x₀ x₁ = x₁ := max_eq_right hx
    exact hmax ▸ h.2
  exact shiftedExp_ne_zero_of_re_neg (lt_of_le_of_lt hwre hx₁)

/-- A vertical logarithmic side is the actual angular Cauchy integrand
on the corresponding circle centered at one, also in the Banach target. -/
theorem transformedBanachCauchy_vertical_side
    (F : ℂ → E) (n : ℕ) (x y : ℝ) :
    I • transformedBanachCauchy F n ((x : ℂ) + (y : ℂ) * I) =
      (deriv (circleMap 1 (Real.exp x)) y *
        (circleMap 1 (Real.exp x) y)⁻¹ ^ (n + 1)) •
          F (circleMap 1 (Real.exp x) y) := by
  rw [transformedBanachCauchy, shiftedExp_on_sides,
    deriv_circleMap]
  have hexp : exp ((x : ℂ) + (y : ℂ) * I) =
      circleMap 0 (Real.exp x) y := by
    simp [circleMap, Complex.exp_add, Complex.ofReal_exp]
  rw [hexp, smul_smul]
  congr 1
  ring

/-- A horizontal logarithmic side is the derivative-weighted Banach
Cauchy integrand on the exponential radial path. -/
theorem transformedBanachCauchy_horizontal_side
    (F : ℂ → E) (n : ℕ) (x y : ℝ) :
    transformedBanachCauchy F n ((x : ℂ) + (y : ℂ) * I) =
      (deriv (fun t : ℝ => circleMap 1 (Real.exp t) y) x *
        (circleMap 1 (Real.exp x) y)⁻¹ ^ (n + 1)) •
          F (circleMap 1 (Real.exp x) y) := by
  have hExp : HasDerivAt (fun t : ℝ => (Real.exp t : ℂ))
      (Real.exp x : ℂ) x := (Real.hasDerivAt_exp x).ofReal_comp
  have hPath : HasDerivAt (fun t : ℝ => circleMap 1 (Real.exp t) y)
      (circleMap 0 (Real.exp x) y) x := by
    have h := hExp.mul_const (Complex.exp ((y : ℂ) * I))
      |>.const_add (1 : ℂ)
    simpa [circleMap] using h
  rw [hPath.deriv, transformedBanachCauchy, shiftedExp_on_sides]
  have hexp : exp ((x : ℂ) + (y : ℂ) * I) =
      circleMap 0 (Real.exp x) y := by
    simp [circleMap, Complex.exp_add, Complex.ofReal_exp]
  rw [hexp]

end PerronWright.Transfer
