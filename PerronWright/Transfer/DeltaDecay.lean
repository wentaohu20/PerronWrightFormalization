import PerronWright.Transfer.DeltaContour
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Asymptotics MeasureTheory
noncomputable section

namespace PerronWright.Transfer

/-- A fixed outer Cauchy arc is exponentially negligible against any
algebraic coefficient scale. -/
theorem exp_neg_nat_isLittleO_rpow {c : ℝ} (hc : 0 < c) (a : ℝ) :
    (fun n : ℕ => Real.exp (-(c * (n : ℝ)))) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) := by
  simpa only [neg_mul] using
    (isLittleO_exp_neg_mul_rpow_atTop hc a).natCast_atTop

/-- The actual outer-arc Cauchy integral is smaller than every algebraic
power when its radius is fixed above `1`. -/
theorem outer_arc_integral_isLittleO {F : ℂ → ℂ}
    {R B θ₀ θ₁ : ℝ} (hR : 1 < R) (hB : 0 ≤ B) (hθ : θ₀ ≤ θ₁)
    (hF : ∀ θ ∈ Set.Icc θ₀ θ₁,
      ‖F (circleMap 0 R θ)‖ ≤ B) (a : ℝ) :
    (fun n : ℕ => ∫ θ in θ₀..θ₁,
        deriv (circleMap 0 R) θ *
          (F (circleMap 0 R θ) *
            ((circleMap 0 R θ)⁻¹ ^ (n + 1)))) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) := by
  let c := Real.log R / 2
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (Real.log_pos hR) (by norm_num)
  have hdom :
      (fun n : ℕ => ∫ θ in θ₀..θ₁,
        deriv (circleMap 0 R) θ *
          (F (circleMap 0 R θ) *
            ((circleMap 0 R θ)⁻¹ ^ (n + 1)))) =O[atTop]
        (fun n : ℕ => Real.exp (-(c * (n : ℝ)))) := by
    rw [isBigO_iff]
    refine ⟨(θ₁ - θ₀) * R * B, Filter.Eventually.of_forall ?_⟩
    intro n
    have hb := outer_arc_bound hR hB hθ hF (n := n)
    have hnorm : ‖Real.exp (-(c * (n : ℝ)))‖ =
        Real.exp (-(c * (n : ℝ))) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hnorm]
    refine hb.trans_eq ?_
    dsimp [c]
    ring_nf
  exact hdom.trans_isLittleO (exp_neg_nat_isLittleO_rpow hc a)

end PerronWright.Transfer
