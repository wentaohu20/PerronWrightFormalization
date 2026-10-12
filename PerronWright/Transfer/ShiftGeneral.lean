import PerronWright.Transfer.NegativeHalfRate

/-!
# Fixed-shift coefficient ratios without positivity of the exponent

The usual finite-product coefficient ratio argument only needs the
generalized binomial coefficients to be nonzero. We prove that criterion
from the absence of a nonnegative integral zero in `s+j`, then obtain a
quantitative `O(1/n)` fixed-shift error for both positive half-integer powers.
-/

open Filter Asymptotics
open scoped Topology
noncomputable section

namespace PerronWright.Transfer

private def shiftFactorGeneral (s : ℝ) (j n : ℕ) : ℝ :=
  ((n : ℝ) - j) / ((n : ℝ) - j + s - 1)

private theorem shiftFactorGeneral_scaled_tendsto (s : ℝ) (j : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (shiftFactorGeneral s j n - 1))
      atTop (𝓝 (1 - s)) := by
  have h := (tendsto_natCast_div_add_atTop (s - 1 - j)).const_mul (1 - s)
  simp only [mul_one] at h
  apply h.congr'
  have he : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) + (s - 1 - j) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hnat.eventually (eventually_gt_atTop (-(s - 1 - j)))] with n hn
    linarith
  filter_upwards [he] with n hn
  unfold shiftFactorGeneral
  have hd : (n : ℝ) - j + s - 1 ≠ 0 := by linarith
  have heq : (n : ℝ) + (s - 1 - j) = (n : ℝ) - j + s - 1 := by ring
  rw [heq]
  field_simp
  ring

private theorem shiftFactorGeneral_tendsto (s : ℝ) (j : ℕ) :
    Tendsto (shiftFactorGeneral s j) atTop (𝓝 1) := by
  have h := (shiftFactorGeneral_scaled_tendsto s j).mul
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  simp only [mul_zero] at h
  have h' := h.add_const 1
  simp only [zero_add] at h'
  apply h'.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

theorem coefficient_nonzero_of_no_nat_root (s : ℝ)
    (hs : ∀ j : ℕ, s + j ≠ 0) (n : ℕ) : coefficient s n ≠ 0 := by
  unfold coefficient
  apply div_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact hs j
  · exact_mod_cast Nat.factorial_ne_zero n

private theorem coefficient_shift_step_general (s : ℝ)
    (hs : ∀ j : ℕ, s + j ≠ 0) (j n : ℕ) (hn : j < n) :
    coefficient s (n - (j + 1)) / coefficient s n =
      (coefficient s (n - j) / coefficient s n) * shiftFactorGeneral s j n := by
  have hi : n - j = (n - (j + 1)) + 1 := by omega
  have heq : ((n : ℝ) - j) = (n - (j + 1) : ℕ) + 1 := by
    rw [← Nat.cast_sub (by omega), hi, Nat.cast_add, Nat.cast_one]
  rw [hi, coefficient_succ]
  unfold shiftFactorGeneral
  rw [heq]
  have hc : coefficient s n ≠ 0 := coefficient_nonzero_of_no_nat_root s hs n
  have hd : (s + (n - (j + 1) : ℕ)) ≠ 0 := hs _
  have hd' : ((n - (j + 1) : ℕ) : ℝ) + 1 + s - 1 ≠ 0 := by
    convert hd using 1
    ring
  have hm : ((n - (j + 1) : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem shifted_coefficient_scaled_error_tendsto_of_no_nat_root (s : ℝ)
    (hs : ∀ j : ℕ, s + j ≠ 0) (j : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (coefficient s (n - j) / coefficient s n - 1))
      atTop (𝓝 ((j : ℝ) * (1 - s))) := by
  induction j with
  | zero =>
      have heq : (fun n : ℕ => (n : ℝ) * (coefficient s (n - 0) / coefficient s n - 1)) =
          fun _ => (0 : ℝ) := by
        funext n
        simp [div_self (coefficient_nonzero_of_no_nat_root s hs n)]
      rw [heq]
      simp
  | succ j ih =>
      have h := (ih.mul (shiftFactorGeneral_tendsto s j)).add
        (shiftFactorGeneral_scaled_tendsto s j)
      have hlim : (j : ℝ) * (1 - s) * 1 + (1 - s) =
          ((j + 1 : ℕ) : ℝ) * (1 - s) := by
        push_cast
        ring
      rw [hlim] at h
      apply h.congr'
      filter_upwards [eventually_gt_atTop j] with n hn
      rw [coefficient_shift_step_general s hs j n hn]
      ring

theorem shifted_coefficient_error_isBigO_of_no_nat_root (s : ℝ)
    (hs : ∀ j : ℕ, s + j ≠ 0) (j : ℕ) :
    (fun n : ℕ => coefficient s (n - j) / coefficient s n - 1) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  have h := (shifted_coefficient_scaled_error_tendsto_of_no_nat_root s hs j).isBigO_one ℝ
  have h' := h.mul (isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop)
  simp only [one_mul] at h'
  apply h'.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

theorem coefficient_neg_half_no_nat_root (j : ℕ) :
    (-(1 / 2 : ℝ)) + j ≠ 0 := by
  intro h
  have hnat : 2 * j = 1 := by exact_mod_cast (by linarith : 2 * (j : ℝ) = 1)
  omega

theorem coefficient_neg_three_halves_no_nat_root (j : ℕ) :
    (-(3 / 2 : ℝ)) + j ≠ 0 := by
  intro h
  have hnat : 2 * j = 3 := by exact_mod_cast (by linarith : 2 * (j : ℝ) = 3)
  omega

theorem shifted_coefficient_neg_half_error_isBigO (j : ℕ) :
    (fun n : ℕ => coefficient (-(1 / 2)) (n - j) /
      coefficient (-(1 / 2)) n - 1) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) :=
  shifted_coefficient_error_isBigO_of_no_nat_root (-(1 / 2))
    coefficient_neg_half_no_nat_root j

theorem shifted_coefficient_neg_three_halves_error_isBigO (j : ℕ) :
    (fun n : ℕ => coefficient (-(3 / 2)) (n - j) /
      coefficient (-(3 / 2)) n - 1) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) :=
  shifted_coefficient_error_isBigO_of_no_nat_root (-(3 / 2))
    coefficient_neg_three_halves_no_nat_root j

end PerronWright.Transfer
