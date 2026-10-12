import PerronWright.Probability.CriticalScaling
import PerronWright.Analysis.FinitePopulationLog

/-! # Actual quadratic and cubic residual coefficients at critical time -/

open Filter Topology
open scoped Real Topology

noncomputable section
set_option maxHeartbeats 600000

namespace PerronWright.CriticalResidualScaling

theorem twoThird_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
  rw [← Real.rpow_natCast _ 3,← Real.rpow_mul hx]
  norm_num only [Nat.cast_ofNat,show (2 / 3 : ℝ) * 3 = 2 by norm_num,Real.rpow_two]

theorem negativeThird_mul_twoThird_sq {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 / 3 : ℝ)) * (x ^ (2 / 3 : ℝ)) ^ 2 = x := by
  rw [← Real.rpow_natCast _ 2,← Real.rpow_mul hx.le,← Real.rpow_add hx]
  norm_num

/-- The exact cubic profile coefficient for a literal size sequence. -/
theorem cubic_size_coefficient_tendsto (N K : ℕ → ℕ)
    (_hN : ∀ m, 0 < N m) {s : ℝ}
    (hs : Tendsto (fun m ↦ (K m : ℝ) / (N m : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 s)) :
    Tendsto (fun m ↦ (K m : ℝ) ^ 3 / (N m : ℝ) ^ 2) atTop (𝓝 (s ^ 3)) := by
  apply (hs.pow 3).congr'
  exact Eventually.of_forall (fun m ↦ by
    dsimp only
    rw [div_pow,twoThird_cube (Nat.cast_nonneg (N m))])

/-- The literal critical time has the actual limiting thermal quadratic
coefficient, not just an order-of-magnitude upper bound. -/
theorem thermal_size_coefficient_tendsto (N K : ℕ → ℕ)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop) (lambda : ℝ) {s : ℝ}
    (hs : Tendsto (fun m ↦ (K m : ℝ) / (N m : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 s)) :
    Tendsto (fun m ↦ (CriticalScaling.time lambda (N m)-1) * (K m : ℝ) ^ 2 / (N m : ℝ))
      atTop (𝓝 (lambda * s ^ 2)) := by
  apply (hs.pow 2 |>.const_mul lambda).congr'
  filter_upwards [hNt.eventually (CriticalScaling.time_eq_raw_eventually lambda)] with m hm
  have hnR : (0 : ℝ) < N m := Nat.cast_pos.mpr (hN m)
  rw [hm]
  have hp := negativeThird_mul_twoThird_sq hnR
  have hscale : (N m : ℝ) ^ (-(1 / 3 : ℝ)) / (N m : ℝ) =
      ((N m : ℝ) ^ (2 / 3 : ℝ))⁻¹ ^ 2 := by
    apply (div_eq_iff hnR.ne').mpr
    have hz : (N m : ℝ) ^ (2 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hnR _).ne'
    field_simp
    nlinarith only [hp]
  rw [div_pow]
  calc
    lambda * ((K m : ℝ)^2 / ((N m : ℝ)^(2/3 : ℝ))^2) =
        lambda * (K m : ℝ)^2 * ((N m : ℝ)^(2/3 : ℝ))⁻¹^2 := by ring
    _ = lambda * (K m : ℝ)^2 * ((N m : ℝ)^(-(1/3 : ℝ)) / (N m : ℝ)) := by
      rw [hscale]
    _ = (1 + lambda * (N m : ℝ)^(-(1/3 : ℝ)) - 1) * (K m : ℝ)^2 / (N m : ℝ) := by ring

/-- The thermal and cubic contributions give the explicit deterministic
Perron exponent appearing in the annealed residual asymptotic. -/
theorem perron_residual_exponent_tendsto (N K : ℕ → ℕ)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop) (lambda α β : ℝ) {s : ℝ}
    (hs : Tendsto (fun m ↦ (K m : ℝ) / (N m : ℝ) ^ (2 / 3 : ℝ)) atTop (𝓝 s)) :
    Tendsto (fun m ↦ α / 2 * ((CriticalScaling.time lambda (N m)-1) * (K m : ℝ)^2 / (N m : ℝ)) -
      β / 6 * ((K m : ℝ)^3 / (N m : ℝ)^2)) atTop (𝓝 (lambda * α * s^2 / 2 - β * s^3 / 6)) := by
  have h := ((thermal_size_coefficient_tendsto N K hN hNt lambda hs).const_mul (α / 2)).sub
    ((cubic_size_coefficient_tendsto N K hN hs).const_mul (β / 6))
  have hlim : α / 2 * (lambda * s^2) - β / 6 * s^3 =
      lambda * α * s^2 / 2 - β * s^3 / 6 := by ring
  simpa only [hlim] using h

end PerronWright.CriticalResidualScaling
