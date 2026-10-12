import PerronWright.Transfer.Base

/-!
# Quantitative fixed-shift coefficient ratios

For each fixed real `s > 0` and natural shift `j`, the coefficients of
`(1-z)^(-s)` satisfy an exact finite-product ratio formula and
`n * (coefficient s (n-j) / coefficient s n - 1) → j * (1-s)`.
In particular, the fixed-shift ratio has relative error `O(1/n)`.

This does not give an `O(1/n)` error relative to the pure-power main term
`n^(s-1)/Gamma(s)`, or bounds uniform in the exponent or shift.
-/

open Filter Asymptotics
open scoped Topology

noncomputable section

namespace PerronWright.Transfer

theorem coefficient_pos (s : ℝ) (hs : 0 < s) (n : ℕ) : 0 < coefficient s n := by
  apply div_pos
  · apply Finset.prod_pos
    intro j _
    exact add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg j)
  · exact_mod_cast Nat.factorial_pos n

theorem coefficient_succ (s : ℝ) (n : ℕ) :
    coefficient s (n + 1) = coefficient s n * (s + n) / (n + 1) := by
  unfold coefficient
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private def shiftFactor (s : ℝ) (j n : ℕ) : ℝ :=
  ((n : ℝ) - j) / ((n : ℝ) - j + s - 1)

private theorem shiftFactor_scaled_tendsto (s : ℝ) (j : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (shiftFactor s j n - 1))
      atTop (𝓝 (1 - s)) := by
  have h := (tendsto_natCast_div_add_atTop (s - 1 - j)).const_mul (1 - s)
  simp only [mul_one] at h
  apply h.congr'
  have he : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) + (s - 1 - j) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hnat.eventually (eventually_gt_atTop (-(s - 1 - j)))] with n hn
    linarith
  filter_upwards [he] with n hn
  unfold shiftFactor
  have hd : (n : ℝ) - j + s - 1 ≠ 0 := by linarith
  have heq : (n : ℝ) + (s - 1 - j) = (n : ℝ) - j + s - 1 := by ring
  rw [heq]
  field_simp
  ring

private theorem shiftFactor_tendsto (s : ℝ) (j : ℕ) :
    Tendsto (shiftFactor s j) atTop (𝓝 1) := by
  have h := (shiftFactor_scaled_tendsto s j).mul
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  simp only [mul_zero] at h
  have h' := h.add_const 1
  simp only [zero_add] at h'
  apply h'.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

private theorem coefficient_shift_step (s : ℝ) (hs : 0 < s) (j n : ℕ) (hn : j < n) :
    coefficient s (n - (j + 1)) / coefficient s n =
      (coefficient s (n - j) / coefficient s n) * shiftFactor s j n := by
  have hi : n - j = (n - (j + 1)) + 1 := by omega
  have heq : ((n : ℝ) - j) = (n - (j + 1) : ℕ) + 1 := by
    rw [← Nat.cast_sub (by omega), hi, Nat.cast_add, Nat.cast_one]
  rw [hi, coefficient_succ]
  unfold shiftFactor
  rw [heq]
  have hc : coefficient s n ≠ 0 := (coefficient_pos s hs n).ne'
  have hd : (s + (n - (j + 1) : ℕ)) ≠ 0 :=
    (add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg _)).ne'
  have hd' : ((n - (j + 1) : ℕ) : ℝ) + 1 + s - 1 ≠ 0 := by
    convert hd using 1
    ring
  have hm : ((n - (j + 1) : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Exact coefficient ratio, before passing to the limit in the index. -/
theorem coefficient_shift_ratio_eq_prod (s : ℝ) (hs : 0 < s) (j n : ℕ) (hj : j ≤ n) :
    coefficient s (n - j) / coefficient s n =
      ∏ i ∈ Finset.range j, ((n : ℝ) - i) / ((n : ℝ) - i + s - 1) := by
  induction j with
  | zero => simp [div_self (coefficient_pos s hs n).ne']
  | succ j ih =>
      rw [coefficient_shift_step s hs j n (by omega), ih (by omega),
        Finset.prod_range_succ]
      rfl

/-- The first-order correction to a fixed-shift coefficient ratio. -/
theorem shifted_coefficient_scaled_error_tendsto (s : ℝ) (hs : 0 < s) (j : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (coefficient s (n - j) / coefficient s n - 1))
      atTop (𝓝 ((j : ℝ) * (1 - s))) := by
  induction j with
  | zero =>
      have heq : (fun n : ℕ => (n : ℝ) * (coefficient s (n - 0) / coefficient s n - 1)) =
          fun _ => (0 : ℝ) := by
        funext n
        simp [div_self (coefficient_pos s hs n).ne']
      rw [heq]
      simp
  | succ j ih =>
      have h := (ih.mul (shiftFactor_tendsto s j)).add (shiftFactor_scaled_tendsto s j)
      have hlim : (j : ℝ) * (1 - s) * 1 + (1 - s) = ((j + 1 : ℕ) : ℝ) * (1 - s) := by
        push_cast
        ring
      rw [hlim] at h
      apply h.congr'
      filter_upwards [eventually_gt_atTop j] with n hn
      rw [coefficient_shift_step s hs j n hn]
      ring

/-- The fixed-shift ratio is `1 + O(1/n)`, with `s` and `j` fixed. -/
theorem shifted_coefficient_error_isBigO (s : ℝ) (hs : 0 < s) (j : ℕ) :
    (fun n : ℕ => coefficient s (n - j) / coefficient s n - 1) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  have h := (shifted_coefficient_scaled_error_tendsto s hs j).isBigO_one ℝ
  have h' := h.mul (isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop)
  simp only [one_mul] at h'
  apply h'.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

end PerronWright.Transfer
