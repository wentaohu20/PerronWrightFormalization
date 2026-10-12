import PerronWright.Transfer.HalfCoefficientRate

/-!
# Quantitative coefficients for positive half-integer powers

The exact algebraic relations with the negative-half singularity propagate
the explicit `1/n` relative rate to `(1-z)^(1/2)` and `(1-z)^(3/2)`.
-/

open Filter Asymptotics
open scoped Topology
noncomputable section

namespace PerronWright.Transfer

theorem coefficient_neg_half_normalized_eq (n : ℕ) (hn : 2 ≤ n) :
    coefficient (-(1 / 2)) n *
        (-(2 * Real.sqrt Real.pi * (n : ℝ) * Real.sqrt (n : ℝ))) =
      (coefficient (1 / 2) n * Real.sqrt Real.pi * Real.sqrt (n : ℝ)) *
        (2 * (n : ℝ) / (2 * (n : ℝ) - 1)) := by
  have hd : 2 * (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    linarith
  rw [coefficient_neg_half_relation]
  field_simp [hd]

theorem coefficient_neg_half_relative_error_bound (n : ℕ) (hn : 2 ≤ n) :
    |coefficient (-(1 / 2)) n *
      (-(2 * Real.sqrt Real.pi * (n : ℝ) * Real.sqrt (n : ℝ))) - 1| ≤
      (n : ℝ)⁻¹ := by
  let R := coefficient (1 / 2) n * Real.sqrt Real.pi * Real.sqrt (n : ℝ)
  let T := 2 * (n : ℝ) / (2 * (n : ℝ) - 1)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hden : 0 < 2 * (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hR := coefficient_half_normalized_bounds n hn
  have hR0 : 0 ≤ R := by
    dsimp [R] at hR ⊢
    have hni : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
      (by exact_mod_cast (by omega : 1 ≤ n))
    linarith
  have hTlo : 1 ≤ T := by
    dsimp [T]
    apply (le_div_iff₀ hden).2
    linarith
  have hThi : T ≤ 1 + (n : ℝ)⁻¹ := by
    dsimp [T]
    apply (div_le_iff₀ hden).2
    field_simp [hnpos.ne']
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast (by omega : 1 ≤ n)]
  have hSlo : 1 - (n : ℝ)⁻¹ ≤ R * T := by
    calc
      _ ≤ R := hR.1
      _ = R * 1 := by ring
      _ ≤ R * T := mul_le_mul_of_nonneg_left hTlo hR0
  have hShi : R * T ≤ 1 + (n : ℝ)⁻¹ := by
    calc
      _ ≤ 1 * T := mul_le_mul_of_nonneg_right hR.2 (by linarith)
      _ = T := one_mul _
      _ ≤ _ := hThi
  rw [coefficient_neg_half_normalized_eq n hn]
  change |R * T - 1| ≤ _
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem coefficient_neg_half_relative_error_isBigO :
    (fun n : ℕ => coefficient (-(1 / 2)) n *
      (-(2 * Real.sqrt Real.pi * (n : ℝ) * Real.sqrt (n : ℝ))) - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply isBigO_iff.mpr
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  simpa only [Real.norm_eq_abs, one_mul,
    abs_of_nonneg (show 0 ≤ ((n : ℝ)⁻¹) by positivity)] using
      coefficient_neg_half_relative_error_bound n hn

theorem coefficient_neg_three_halves_normalized_eq (n : ℕ) (hn : 3 ≤ n) :
    coefficient (-(3 / 2)) n *
        (4 * Real.sqrt Real.pi * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 3) =
      (coefficient (1 / 2) n * Real.sqrt Real.pi * Real.sqrt (n : ℝ)) *
        (4 * (n : ℝ) ^ 2 /
          ((2 * (n : ℝ) - 3) * (2 * (n : ℝ) - 1))) := by
  have hd1 : 2 * (n : ℝ) - 3 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hd2 : 2 * (n : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [coefficient_neg_three_halves_relation]
  field_simp [hd1, hd2]

theorem coefficient_neg_three_halves_relative_error_bound (n : ℕ) (hn : 3 ≤ n) :
    |coefficient (-(3 / 2)) n *
      (4 * Real.sqrt Real.pi * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 3) - 1| ≤
      6 * (n : ℝ)⁻¹ := by
  let R := coefficient (1 / 2) n * Real.sqrt Real.pi * Real.sqrt (n : ℝ)
  let T := 4 * (n : ℝ) ^ 2 /
    ((2 * (n : ℝ) - 3) * (2 * (n : ℝ) - 1))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hden : 0 < (2 * (n : ℝ) - 3) * (2 * (n : ℝ) - 1) := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : 0 < 2 * (n : ℝ) - 3 := by linarith
    have h2 : 0 < 2 * (n : ℝ) - 1 := by linarith
    exact mul_pos h1 h2
  have hR := coefficient_half_normalized_bounds n (by omega : 2 ≤ n)
  have hR0 : 0 ≤ R := by
    dsimp [R] at hR ⊢
    have hni : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀
      (by exact_mod_cast (by omega : 1 ≤ n))
    linarith
  have hTlo : 1 ≤ T := by
    dsimp [T]
    apply (le_div_iff₀ hden).2
    nlinarith [show (3 : ℝ) ≤ n by exact_mod_cast hn]
  have hThi : T ≤ 1 + 6 * (n : ℝ)⁻¹ := by
    dsimp [T]
    apply (div_le_iff₀ hden).2
    field_simp [hnpos.ne']
    have hthree : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 3)]
  have hSlo : 1 - (n : ℝ)⁻¹ ≤ R * T := by
    calc
      _ ≤ R := hR.1
      _ = R * 1 := by ring
      _ ≤ R * T := mul_le_mul_of_nonneg_left hTlo hR0
  have hShi : R * T ≤ 1 + 6 * (n : ℝ)⁻¹ := by
    calc
      _ ≤ 1 * T := mul_le_mul_of_nonneg_right hR.2 (by linarith)
      _ = T := one_mul _
      _ ≤ _ := hThi
  rw [coefficient_neg_three_halves_normalized_eq n hn]
  change |R * T - 1| ≤ _
  exact abs_le.mpr ⟨by nlinarith [inv_nonneg.mpr hnpos.le], by linarith⟩

theorem coefficient_neg_three_halves_relative_error_isBigO :
    (fun n : ℕ => coefficient (-(3 / 2)) n *
      (4 * Real.sqrt Real.pi * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 3) - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply isBigO_iff.mpr
  refine ⟨6, ?_⟩
  filter_upwards [eventually_ge_atTop 3] with n hn
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ ((n : ℝ)⁻¹) by positivity)] using
      coefficient_neg_three_halves_relative_error_bound n hn

end PerronWright.Transfer
