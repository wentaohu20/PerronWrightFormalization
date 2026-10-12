import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# A quantitative Stirling estimate

This file upgrades mathlib's convergence form of Stirling's formula to the
relative `O(1 / n)` estimate used when labelled exponential generating
function coefficients are converted back to labelled weights.

The proof uses only the sharp one-step logarithmic estimate already available
as `Stirling.log_stirlingSeq_sdiff_le`.  Subtracting `1 / (12 n)` makes the
logarithmic Stirling sequence monotone increasing; its known limit then gives
the global logarithmic remainder bound.  Exponentiation costs only a factor
two.
-/

open Filter Asymptotics
open scoped Topology Real Nat

noncomputable section

namespace PerronWright.Transfer

/-- The main term in Stirling's formula, in the normalization used to pass
from labelled EGF coefficients to labelled weights. -/
def factorialStirlingMainTerm (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi * (n : ℝ)) *
    ((n : ℝ) / Real.exp 1) ^ n

private theorem correctedLogStirling_monotone :
    Monotone (fun n : ℕ ↦
      Real.log (Stirling.stirlingSeq (n + 1)) -
        1 / (12 * ((n + 1 : ℕ) : ℝ))) := by
  apply monotone_nat_of_le_succ
  intro n
  have hstep := Stirling.log_stirlingSeq_sdiff_le (n + 1)
  have htel :
      1 / (12 * ((n + 1 : ℕ) : ℝ)) -
          1 / (12 * (((n + 1 : ℕ) : ℝ) + 1)) =
        1 / (12 * ((n + 1 : ℕ) : ℝ) *
          (((n + 1 : ℕ) : ℝ) + 1)) := by
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hn2 : ((n + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn1, hn2]; ring
  rw [← htel] at hstep
  have hcast : (((n + 1 : ℕ) + 1 : ℕ) : ℝ) =
      ((n + 1 : ℕ) : ℝ) + 1 := by norm_num
  rw [hcast]
  linarith

private theorem correctedLogStirling_tendsto :
    Tendsto (fun n : ℕ ↦
      Real.log (Stirling.stirlingSeq (n + 1)) -
        1 / (12 * ((n + 1 : ℕ) : ℝ))) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) := by
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  have hseq : Tendsto (fun n : ℕ ↦ Stirling.stirlingSeq (n + 1)) atTop
      (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun n : ℕ ↦
      Real.log (Stirling.stirlingSeq (n + 1))) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log hsqrt).tendsto.comp hseq
  have hcorr : Tendsto (fun n : ℕ ↦
      1 / (12 * ((n + 1 : ℕ) : ℝ))) atTop
      (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (1 / 12 : ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, div_eq_mul_inv, one_mul,
      mul_inv_rev, mul_comm] using h
  simpa only [sub_zero] using hlog.sub hcorr

/-- Robbins' logarithmic remainder, in a form directly centered at the
Stirling limit. -/
theorem log_stirlingSeq_relative_error_bound (n : ℕ) (hn : 0 < n) :
    0 ≤ Real.log (Stirling.stirlingSeq n) -
        Real.log (Real.sqrt Real.pi) ∧
      Real.log (Stirling.stirlingSeq n) -
          Real.log (Real.sqrt Real.pi) ≤
        1 / (12 * (n : ℝ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hseq : 0 < Stirling.stirlingSeq (k + 1) :=
    Stirling.stirlingSeq'_pos k
  constructor
  · exact sub_nonneg.mpr <|
      (Real.log_le_log_iff hsqrt hseq).2
        (Stirling.sqrt_pi_le_stirlingSeq (Nat.succ_ne_zero k))
  · have hcorr := correctedLogStirling_monotone.ge_of_tendsto
      correctedLogStirling_tendsto k
    linarith

/-- Explicit relative error for mathlib's Stirling sequence.  The constant
`1/6` is deliberately simple; the logarithmic input has the sharper constant
`1/12`. -/
theorem stirlingSeq_relative_error_bound (n : ℕ) (hn : 0 < n) :
    |Stirling.stirlingSeq n / Real.sqrt Real.pi - 1| ≤
      1 / (6 * (n : ℝ)) := by
  let x := Real.log (Stirling.stirlingSeq n) -
    Real.log (Real.sqrt Real.pi)
  have hx := log_stirlingSeq_relative_error_bound n hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hseqpos : 0 < Stirling.stirlingSeq n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact Stirling.stirlingSeq'_pos k
  have hxnonneg : 0 ≤ x := hx.1
  have hxupper : x ≤ 1 / (12 * (n : ℝ)) := hx.2
  have hxone : |x| ≤ 1 := by
    rw [abs_of_nonneg hxnonneg]
    calc
      x ≤ 1 / (12 * (n : ℝ)) := hxupper
      _ ≤ 1 := by
        have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [div_le_one (by positivity)]
        nlinarith
  have hratio :
      Stirling.stirlingSeq n / Real.sqrt Real.pi = Real.exp x := by
    dsimp only [x]
    rw [Real.exp_sub,
      Real.exp_log hseqpos,
      Real.exp_log (Real.sqrt_pos.2 Real.pi_pos)]
  rw [hratio]
  calc
    |Real.exp x - 1| ≤ 2 * |x| := Real.abs_exp_sub_one_le hxone
    _ = 2 * x := by rw [abs_of_nonneg hxnonneg]
    _ ≤ 2 * (1 / (12 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hxupper (by norm_num)
    _ = 1 / (6 * (n : ℝ)) := by ring

/-- The usual factorial/main-term quotient is exactly mathlib's Stirling
sequence divided by `sqrt pi`. -/
theorem factorial_div_stirlingMainTerm_eq (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) / factorialStirlingMainTerm n =
      Stirling.stirlingSeq n / Real.sqrt Real.pi := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrt2n : Real.sqrt (2 * (n : ℝ)) ≠ 0 := by positivity
  have hpow : ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := by positivity
  have hmain :
      factorialStirlingMainTerm n =
        Real.sqrt Real.pi *
          (Real.sqrt (2 * (n : ℝ)) *
            ((n : ℝ) / Real.exp 1) ^ n) := by
    unfold factorialStirlingMainTerm
    simp [Real.sqrt_mul']; ring
  rw [hmain, Stirling.stirlingSeq]
  field_simp [hsqrtpi, hsqrt2n, hpow]

/-- A direct, effective relative-error estimate for factorials. -/
theorem factorial_stirling_relative_error_bound (n : ℕ) (hn : 0 < n) :
    |(n.factorial : ℝ) / factorialStirlingMainTerm n - 1| ≤
      1 / (6 * (n : ℝ)) := by
  rw [factorial_div_stirlingMainTerm_eq n hn]
  exact stirlingSeq_relative_error_bound n hn

/-- Quantitative Stirling in the asymptotic form needed by the final
Perron--Wright normalization. -/
theorem factorial_stirling_relative_error_isBigO :
    (fun n : ℕ ↦
      (n.factorial : ℝ) / factorialStirlingMainTerm n - 1)
      =O[atTop] (fun n : ℕ ↦ (n : ℝ)⁻¹) := by
  apply isBigO_iff.mpr
  refine ⟨1 / 6, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := by omega
  have h := factorial_stirling_relative_error_bound n hnpos
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  calc
    ‖(n.factorial : ℝ) / factorialStirlingMainTerm n - 1‖ =
        |(n.factorial : ℝ) / factorialStirlingMainTerm n - 1| :=
      Real.norm_eq_abs _
    _ ≤ 1 / (6 * (n : ℝ)) := h
    _ = (1 / 6 : ℝ) * ‖(n : ℝ)⁻¹‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnreal)]
      field_simp [hnreal.ne']

end PerronWright.Transfer
