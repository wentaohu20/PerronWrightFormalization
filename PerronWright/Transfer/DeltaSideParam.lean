import PerronWright.Transfer.DeltaCauchy
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
Exact parameterization of the sides in the logarithmic-sector
Cauchy--Goursat theorem.  These equations expose the center mismatch:
the circular sides are centered at `1`, whereas a Taylor coefficient
outer arc is centered at `0`.
-/

open Complex MeasureTheory
noncomputable section

namespace PerronWright.Transfer

/-- A horizontal line in logarithmic coordinates is a radial ray from `1`;
a vertical line is a circle centered at `1`. -/
theorem shiftedExp_on_sides (x y : ℝ) :
    PerronWright.Transfer.shiftedExp ((x : ℂ) + (y : ℂ) * I) =
      circleMap 1 (Real.exp x) y := by
  simp [PerronWright.Transfer.shiftedExp, circleMap, Complex.exp_add,
    Complex.ofReal_exp]

/-- The transformed Cauchy integrand on a vertical side is exactly the
ordinary angular path integrand on the `1`-centered circle. -/
theorem transformedCauchy_vertical_side (F : ℂ → ℂ) (n : ℕ)
    (x y : ℝ) :
    I * PerronWright.Transfer.transformedCauchy F n ((x : ℂ) + (y : ℂ) * I) =
      deriv (circleMap 1 (Real.exp x)) y *
        (F (circleMap 1 (Real.exp x) y) *
          (circleMap 1 (Real.exp x) y)⁻¹ ^ (n + 1)) := by
  rw [PerronWright.Transfer.transformedCauchy, shiftedExp_on_sides,
    deriv_circleMap]
  have hexp : exp ((x : ℂ) + (y : ℂ) * I) = circleMap 0 (Real.exp x) y := by
    simp [circleMap, Complex.exp_add, Complex.ofReal_exp]
  rw [hexp]
  ring

/-- The horizontal transformed integrand is the derivative-weighted
integrand on the exponential radial path. -/
theorem transformedCauchy_horizontal_side (F : ℂ → ℂ) (n : ℕ)
    (x y : ℝ) :
    PerronWright.Transfer.transformedCauchy F n ((x : ℂ) + (y : ℂ) * I) =
      deriv (fun t : ℝ => circleMap 1 (Real.exp t) y) x *
        (F (circleMap 1 (Real.exp x) y) *
          (circleMap 1 (Real.exp x) y)⁻¹ ^ (n + 1)) := by
  have hExp : HasDerivAt (fun t : ℝ => (Real.exp t : ℂ))
      (Real.exp x : ℂ) x := (Real.hasDerivAt_exp x).ofReal_comp
  have hPath : HasDerivAt (fun t : ℝ => circleMap 1 (Real.exp t) y)
      (circleMap 0 (Real.exp x) y) x := by
    have h := hExp.mul_const (Complex.exp ((y : ℂ) * I)) |>.const_add (1 : ℂ)
    simpa [circleMap] using h
  rw [hPath.deriv, PerronWright.Transfer.transformedCauchy, shiftedExp_on_sides]
  have hexp : Complex.exp ((x : ℂ) + (y : ℂ) * I) =
      circleMap 0 (Real.exp x) y := by
    simp [circleMap, Complex.exp_add, Complex.ofReal_exp]
  rw [hexp]
  ring


end PerronWright.Transfer
