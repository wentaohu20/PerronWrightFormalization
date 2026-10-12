import PerronWright.Transfer.CoefficientCauchy

/-! Cauchy's coefficient identity with values in a complex Banach space. -/

open Complex MeasureTheory
noncomputable section

namespace PerronWright.Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

def banachTaylorCoefficient (F : ℂ → E) (n : ℕ) : E :=
  (n.factorial : ℂ)⁻¹ • iteratedDeriv n F 0

theorem circleIntegral_eq_banachTaylorCoefficient
    {F : ℂ → E} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (Metric.closedBall 0 R)) (n : ℕ) :
    (∮ z in C((0 : ℂ), R), z⁻¹ ^ (n + 1) • F z) =
      (2 * Real.pi * I) • banachTaylorCoefficient F n := by
  have h := hF.circleIntegral_one_div_sub_center_pow_smul hR n
  simpa only [sub_zero, one_div, inv_pow, one_mul,
    banachTaylorCoefficient, div_eq_mul_inv, smul_smul,
    mul_assoc, mul_comm, mul_left_comm] using h

end PerronWright.Transfer
