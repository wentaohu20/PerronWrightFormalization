import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Quantitative finite-population selection corrections

These are estimates for the literal falling-factorial selection ratio,
not an assumed finite-population asymptotic interface.
-/

open Finset Set Filter Topology
open scoped BigOperators Topology

noncomputable section

namespace PerronWright.FinitePopulationLog

theorem log_one_sub_quadratic_error {x : ℝ} (hx : 0 ≤ x) (hhalf : x ≤ 1 / 2) :
    |Real.log (1 - x) + x + x ^ 2 / 2| ≤ 2 * x ^ 3 := by
  have hsmall : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hsmall 2
  norm_num [sum_range_succ, abs_of_nonneg hx] at h
  have hden : 0 < 1 - x := by linarith
  have hb : x ^ 3 / (1 - x) ≤ 2 * x ^ 3 := by
    apply (div_le_iff₀ hden).mpr
    have hhalf' : 1 / 2 ≤ 1 - x := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left hhalf' (pow_nonneg hx 3)]
  have he : (x + x ^ 2 / 2) + Real.log (1 - x) = Real.log (1 - x) + x + x ^ 2 / 2 := by ring
  rw [he] at h
  exact h.trans hb

theorem log_selection_ratio {n K : ℕ} (hn : 0 < n) (hK : K ≤ n) :
    Real.log ((n.descFactorial K : ℝ) / (n : ℝ) ^ K) =
      ∑ j ∈ range K, Real.log (1 - (j : ℝ) / n) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hfactor (j : ℕ) (hj : j ∈ range K) : 0 < 1 - (j : ℝ) / n := by
    have hjn : j < n := (mem_range.mp hj).trans_le hK
    have hdiv : (j : ℝ) / n < 1 := (div_lt_one hnR).mpr (Nat.cast_lt.mpr hjn)
    linarith
  have he : (n.descFactorial K : ℝ) / (n : ℝ) ^ K =
      ∏ j ∈ range K, (1 - (j : ℝ) / n) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hcast : ∀ j ∈ range K, ((n - j : ℕ) : ℝ) = (n : ℝ) - j := by
      intro j hj
      exact Nat.cast_sub ((mem_range.mp hj).le.trans hK)
    simp_rw [Finset.prod_congr rfl hcast]
    calc
      _ = (∏ j ∈ range K, ((n : ℝ) - j)) / (∏ _j ∈ range K, (n : ℝ)) := by simp
      _ = ∏ j ∈ range K, (((n : ℝ) - j) / n) := (prod_div_distrib ..).symm
      _ = _ := by
        apply prod_congr rfl
        intro j _
        field_simp
  rw [he, Real.log_prod (fun j hj ↦ (hfactor j hj).ne')]

theorem log_selection_quadratic_error {n K : ℕ} (hn : 0 < n)
    (hK : (K : ℝ) ≤ (n : ℝ) / 2) :
    |Real.log ((n.descFactorial K : ℝ) / (n : ℝ) ^ K) +
      ∑ j ∈ range K, (j : ℝ) / n +
      ∑ j ∈ range K, ((j : ℝ) / n) ^ 2 / 2| ≤
        2 * (K : ℝ) * ((K : ℝ) / n) ^ 3 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hKn : K ≤ n := by
    have hr : (K : ℝ) ≤ n := by linarith
    exact_mod_cast hr
  rw [log_selection_ratio hn hKn, ← sum_add_distrib, ← sum_add_distrib]
  calc
    _ ≤ ∑ j ∈ range K, |Real.log (1 - (j : ℝ) / n) + (j : ℝ) / n + ((j : ℝ) / n) ^ 2 / 2| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range K, 2 * ((K : ℝ) / n) ^ 3 := by
      apply sum_le_sum
      intro j hj
      have hjK : (j : ℝ) ≤ K := Nat.cast_le.mpr (mem_range.mp hj).le
      have hjs : (j : ℝ) / n ≤ 1 / 2 := by
        apply (div_le_iff₀ hnR).mpr
        linarith
      have h := log_one_sub_quadratic_error (div_nonneg (Nat.cast_nonneg j) hnR.le) hjs
      exact h.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg j) hnR.le)
          (div_le_div_of_nonneg_right hjK hnR.le) 3) (by norm_num))
    _ = _ := by simp; ring

theorem sum_range_cast (K : ℕ) :
    (∑ j ∈ range K, (j : ℝ)) = (K : ℝ) * ((K : ℝ) - 1) / 2 := by
  induction K with
  | zero => norm_num
  | succ K hK =>
    rw [sum_range_succ, hK]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem sum_range_cast_sq (K : ℕ) :
    (∑ j ∈ range K, (j : ℝ) ^ 2) =
      (K : ℝ) * ((K : ℝ) - 1) * (2 * (K : ℝ) - 1) / 6 := by
  induction K with
  | zero => norm_num
  | succ K hK =>
    rw [sum_range_succ, hK]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- Exact polynomial correction and uniform fourth-order error for the
literal falling-factorial selection ratio. -/
theorem log_selection_polynomial_error {n K : ℕ} (hn : 0 < n)
    (hK : (K : ℝ) ≤ (n : ℝ) / 2) :
    |Real.log ((n.descFactorial K : ℝ) / (n : ℝ) ^ K) +
      (K : ℝ) * ((K : ℝ) - 1) / (2 * n) +
      (K : ℝ) * ((K : ℝ) - 1) * (2 * (K : ℝ) - 1) / (12 * (n : ℝ) ^ 2)| ≤
        2 * (K : ℝ) ^ 4 / (n : ℝ) ^ 3 := by
  have hs1 : (∑ j ∈ range K, (j : ℝ) / n) =
      (K : ℝ) * ((K : ℝ) - 1) / (2 * n) := by
    rw [← sum_div, sum_range_cast]
    ring
  have hs2 : (∑ j ∈ range K, ((j : ℝ) / n) ^ 2 / 2) =
      (K : ℝ) * ((K : ℝ) - 1) * (2 * (K : ℝ) - 1) / (12 * (n : ℝ) ^ 2) := by
    simp_rw [div_pow, div_div]
    rw [← sum_div, sum_range_cast_sq]
    ring
  have h := log_selection_quadratic_error hn hK
  rw [hs1, hs2] at h
  convert h using 1
  ring

theorem fourth_remainder_bound {n K : ℕ} {C : ℝ} (hn : 0 < n)
    (_hC : 0 ≤ C) (hsize : (K : ℝ) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) :
    2 * (K : ℝ) ^ 4 / (n : ℝ) ^ 3 ≤
      2 * C ^ 4 * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg K) hsize 4
  rw [mul_pow] at hp
  have hscale : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 4 / (n : ℝ) ^ 3 =
      (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hnR.le,
      ← Real.rpow_natCast _ 3, ← Real.rpow_sub hnR]
    norm_num
  calc
    _ ≤ 2 * (C ^ 4 * ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 4) / (n : ℝ) ^ 3 := by
      gcongr
    _ = 2 * C ^ 4 * (((n : ℝ) ^ (2 / 3 : ℝ)) ^ 4 / (n : ℝ) ^ 3) := by ring
    _ = _ := by rw [hscale]

/-- On the actual critical size scale, the literal selection ratio has
the proved polynomial logarithmic correction with vanishing error. -/
theorem critical_size_ratio_tendsto_zero
    (N K : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Filter.Tendsto N Filter.atTop Filter.atTop)
    {C : ℝ} (_hC : 0 ≤ C)
    (hsize : ∀ᶠ m in Filter.atTop, (K m : ℝ) ≤ C * (N m : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun m ↦ (K m : ℝ) / N m) atTop (𝓝 0) := by
  have hp : Filter.Tendsto (fun m ↦ (N m : ℝ) ^ (-(1 / 3 : ℝ))) Filter.atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      (tendsto_natCast_atTop_atTop.comp hNt)
  have hupper : ∀ᶠ m in Filter.atTop,
      (K m : ℝ) / N m ≤ C * (N m : ℝ) ^ (-(1 / 3 : ℝ)) := by
    filter_upwards [hsize] with m hm
    have hnR : (0 : ℝ) < N m := Nat.cast_pos.mpr (hN m)
    have he : (N m : ℝ) ^ (2 / 3 : ℝ) / N m = (N m : ℝ) ^ (-(1 / 3 : ℝ)) := by
      have hh := Real.rpow_sub hnR (2 / 3 : ℝ) 1
      norm_num only [Real.rpow_one] at hh
      convert hh.symm using 1
    calc
      _ ≤ (C * (N m : ℝ) ^ (2 / 3 : ℝ)) / N m := div_le_div_of_nonneg_right hm hnR.le
      _ = C * ((N m : ℝ) ^ (2 / 3 : ℝ) / N m) := by ring
      _ = _ := by rw [he]
  exact squeeze_zero' (Filter.Eventually.of_forall (fun m ↦ by positivity)) hupper
    (by simpa only [mul_zero] using hp.const_mul C)

theorem eventually_critical_size_le_half
    (N K : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ᶠ m in atTop, (K m : ℝ) ≤ C * (N m : ℝ) ^ (2 / 3 : ℝ)) :
    ∀ᶠ m in atTop, (K m : ℝ) ≤ (N m : ℝ) / 2 := by
  filter_upwards [(critical_size_ratio_tendsto_zero N K hN hNt hC hsize).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with m hm
  have hh := (div_le_iff₀ (Nat.cast_pos.mpr (hN m))).mp hm.le
  linarith

theorem log_selection_remainder_tendsto
    (N K : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ᶠ m in atTop, (K m : ℝ) ≤ C * (N m : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun m ↦ Real.log (((N m).descFactorial (K m) : ℝ) / (N m : ℝ) ^ (K m)) +
      (K m : ℝ) * ((K m : ℝ) - 1) / (2 * N m) +
      (K m : ℝ) * ((K m : ℝ) - 1) * (2 * (K m : ℝ) - 1) / (12 * (N m : ℝ) ^ 2))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun m ↦ (N m : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      (tendsto_natCast_atTop_atTop.comp hNt)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m ↦ norm_nonneg _))
    (hsize.and (eventually_critical_size_le_half N K hN hNt hC hsize) |>.mono ?_)
    (by simpa only [mul_zero] using hp.const_mul (2 * C ^ 4))
  intro m hm
  rw [Real.norm_eq_abs]
  exact (log_selection_polynomial_error (hN m) hm.2).trans
    (fourth_remainder_bound (hN m) hC hm.1)

/-- Multiplicative correction of the actual finite-population selection
ratio, derived from its proved logarithmic remainder. -/
theorem selection_exponential_correction_tendsto_one
    (N K : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ᶠ m in atTop, (K m : ℝ) ≤ C * (N m : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun m ↦ (((N m).descFactorial (K m) : ℝ) / (N m : ℝ) ^ (K m)) *
      Real.exp ((K m : ℝ) * ((K m : ℝ) - 1) / (2 * N m) +
        (K m : ℝ) * ((K m : ℝ) - 1) * (2 * (K m : ℝ) - 1) / (12 * (N m : ℝ) ^ 2)))
      atTop (𝓝 1) := by
  have ht := (Real.continuous_exp.tendsto (0 : ℝ)).comp
    (log_selection_remainder_tendsto N K hN hNt hC hsize)
  simp only [Real.exp_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_critical_size_le_half N K hN hNt hC hsize] with m hm
  have hKn : K m ≤ N m := by
    have hr : (K m : ℝ) ≤ N m := by linarith [(Nat.cast_nonneg (N m) : (0 : ℝ) ≤ N m)]
    exact_mod_cast hr
  have hratio : (0 : ℝ) < ((N m).descFactorial (K m) : ℝ) / (N m : ℝ) ^ (K m) :=
    div_pos (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hKn))
      (pow_pos (Nat.cast_pos.mpr (hN m)) _)
  dsimp only [Function.comp_def]
  rw [Real.exp_add, Real.exp_add, Real.exp_log hratio, Real.exp_add]
  ring

/-- The simplified quadratic/cubic finite-population exponent used in
the critical component formula has the same vanishing remainder. -/
theorem log_selection_leading_remainder_tendsto
    (N K : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ᶠ m in atTop, (K m : ℝ) ≤ C * (N m : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun m ↦ Real.log (((N m).descFactorial (K m) : ℝ) / (N m : ℝ) ^ (K m)) +
      (K m : ℝ) ^ 2 / (2 * N m) + (K m : ℝ) ^ 3 / (6 * (N m : ℝ) ^ 2))
      atTop (𝓝 0) := by
  have hr := critical_size_ratio_tendsto_zero N K hN hNt hC hsize
  have hn : Tendsto (fun m ↦ (N m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hNt)
  have hc := ((hr.div_const 2).add ((hr.pow 2).div_const 4)).sub ((hr.mul hn).div_const 12)
  have ht := (log_selection_remainder_tendsto N K hN hNt hC hsize).add hc
  norm_num only [zero_div, zero_add, zero_pow, zero_mul, sub_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun m ↦ by simp only [div_pow]; ring)

/-- The actual falling-factorial ratio, multiplied by the paper's
quadratic/cubic correction, tends to one on the full critical size scale. -/
theorem selection_leading_correction_tendsto_one
    (N K : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hsize : ∀ᶠ m in atTop, (K m : ℝ) ≤ C * (N m : ℝ) ^ (2 / 3 : ℝ)) :
    Tendsto (fun m ↦ (((N m).descFactorial (K m) : ℝ) / (N m : ℝ) ^ (K m)) *
      Real.exp ((K m : ℝ) ^ 2 / (2 * N m) + (K m : ℝ) ^ 3 / (6 * (N m : ℝ) ^ 2)))
      atTop (𝓝 1) := by
  have ht := (Real.continuous_exp.tendsto (0 : ℝ)).comp
    (log_selection_leading_remainder_tendsto N K hN hNt hC hsize)
  simp only [Real.exp_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_critical_size_le_half N K hN hNt hC hsize] with m hm
  have hKn : K m ≤ N m := by
    have hr : (K m : ℝ) ≤ N m := by linarith [(Nat.cast_nonneg (N m) : (0 : ℝ) ≤ N m)]
    exact_mod_cast hr
  have hratio : (0 : ℝ) < ((N m).descFactorial (K m) : ℝ) / (N m : ℝ) ^ (K m) :=
    div_pos (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hKn))
      (pow_pos (Nat.cast_pos.mpr (hN m)) _)
  dsimp only [Function.comp_def]
  rw [Real.exp_add, Real.exp_add, Real.exp_log hratio, Real.exp_add]
  ring

end PerronWright.FinitePopulationLog
