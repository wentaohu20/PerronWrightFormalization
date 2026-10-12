import PerronWright.Transfer.HalfCoefficientRate
import PerronWright.Transfer.ShiftError

/-!
# Quantitative coefficients of positive half-integer singularities

For every positive half-integer `s`, the exact coefficient of
`(1-z)⁻ˢ`, normalized by its Gamma main term, differs from one by
`O(1/n)`.  The proof starts from the already established half-power
estimate and the exact exponent-one case, and raises the exponent by one
through the Gamma recurrence.  This is the pure-singularity estimate needed
for every fixed positive surplus.
-/

open Filter Asymptotics
open scoped Topology

noncomputable section

namespace PerronWright.Transfer

/-- The exact binomial coefficient divided by its leading Gamma asymptotic. -/
def normalizedPowerCoefficient (s : ℝ) (n : ℕ) : ℝ :=
  coefficient s n * Real.Gamma s * (n : ℝ) ^ (1 - s)

theorem coefficient_one (n : ℕ) : coefficient 1 n = 1 := by
  unfold coefficient
  have hprod :
      (∏ j ∈ Finset.range n, ((1 : ℝ) + j)) = (n.factorial : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
        push_cast
        ring
  rw [hprod, div_self]
  exact_mod_cast Nat.factorial_ne_zero n

theorem normalizedPowerCoefficient_half_error_isBigO :
    (fun n : ℕ => normalizedPowerCoefficient (1 / 2) n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply coefficient_half_relative_error_isBigO.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [normalizedPowerCoefficient, Real.Gamma_one_half_eq]
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow]
  · exact Filter.EventuallyEq.rfl

theorem normalizedPowerCoefficient_one_error_isBigO :
    (fun n : ℕ => normalizedPowerCoefficient 1 n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  have hzero :
      (fun n : ℕ => normalizedPowerCoefficient 1 n - 1) =
        fun _ : ℕ => (0 : ℝ) := by
    funext n
    simp [normalizedPowerCoefficient, coefficient_one, Real.Gamma_one]
  rw [hzero]
  exact isBigO_zero _ _

/-- Raising the singular exponent by one multiplies its exact coefficient
by `(n+s)/s`. -/
theorem coefficient_exponent_add_one (s : ℝ) (hs : 0 < s) (n : ℕ) :
    coefficient (s + 1) n = ((n : ℝ) + s) / s * coefficient s n := by
  rw [coefficient_eq_gamma (s + 1) (by linarith), coefficient_eq_gamma s hs]
  have hsn : s + (n : ℝ) ≠ 0 :=
    (add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg n)).ne'
  rw [show s + 1 + (n : ℝ) = (s + (n : ℝ)) + 1 by ring,
    Real.Gamma_add_one hsn, Real.Gamma_add_one hs.ne']
  have hGs : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos hs).ne'
  have hGn : Real.Gamma ((n : ℝ) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  field_simp [hs.ne', hGs, hGn]
  ring

theorem normalizedPowerCoefficient_add_one
    (s : ℝ) (hs : 0 < s) (n : ℕ) (hn : 0 < n) :
    normalizedPowerCoefficient (s + 1) n =
      normalizedPowerCoefficient s n * (1 + s * (n : ℝ)⁻¹) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow :
      (n : ℝ) ^ (1 - s) = (n : ℝ) ^ (-s) * (n : ℝ) := by
    calc
      (n : ℝ) ^ (1 - s) = (n : ℝ) ^ (-s + 1) := by
        congr 1
        ring
      _ = (n : ℝ) ^ (-s) * (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_add hnreal]
      _ = (n : ℝ) ^ (-s) * (n : ℝ) := by rw [Real.rpow_one]
  unfold normalizedPowerCoefficient
  rw [coefficient_exponent_add_one s hs n, Real.Gamma_add_one hs.ne',
    show 1 - (s + 1) = -s by ring, hpow]
  field_simp [hs.ne', hnreal.ne']

/-- An `O(1/n)` relative coefficient estimate propagates when the
singularity exponent is raised by one. -/
theorem normalizedPowerCoefficient_add_one_error_isBigO
    (s : ℝ) (hs : 0 < s)
    (h : (fun n : ℕ => normalizedPowerCoefficient s n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹)) :
    (fun n : ℕ => normalizedPowerCoefficient (s + 1) n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  let invNat : ℕ → ℝ := fun n => (n : ℝ)⁻¹
  have hinvOne : invNat =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).isBigO_one ℝ
  have hsInv : (fun n : ℕ => s * invNat n) =O[atTop] invNat :=
    (isBigO_refl invNat atTop).const_mul_left s
  have hfactorTendsto :
      Tendsto (fun n : ℕ => 1 + s * invNat n) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa only [invNat, mul_zero, add_zero] using
      hone.add
        ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul s)
  have hfactor :
      (fun n : ℕ => 1 + s * invNat n) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := hfactorTendsto.isBigO_one ℝ
  have hprod := h.mul hfactor
  simp only [mul_one] at hprod
  have hsum := hprod.add hsInv
  apply hsum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn
  rw [normalizedPowerCoefficient_add_one s hs n hnpos]
  dsimp only [invNat]
  ring

/-- Uniform in the coefficient index (but with the half-integer exponent
fixed): every positive half-integer singularity has relative error
`O(1/n)`. -/
theorem normalizedPowerCoefficient_natSuccHalf_error_isBigO (m : ℕ) :
    (fun n : ℕ =>
        normalizedPowerCoefficient (((m + 1 : ℕ) : ℝ) / 2) n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  induction m using Nat.twoStepInduction with
  | zero =>
      simpa only [zero_add, Nat.cast_one, one_div] using
        normalizedPowerCoefficient_half_error_isBigO
  | one =>
      norm_num
      exact normalizedPowerCoefficient_one_error_isBigO
  | more m ih _ =>
      have hs : 0 < (((m + 1 : ℕ) : ℝ) / 2) := by positivity
      have h := normalizedPowerCoefficient_add_one_error_isBigO
        (((m + 1 : ℕ) : ℝ) / 2) hs ih
      convert h using 1
      · funext n
        congr 2
        push_cast
        ring

/-- The form used by a fixed positive surplus: the singular exponent is
`3*ell/2`. -/
theorem normalizedPowerCoefficient_three_halves_mul_error_isBigO
    (ell : ℕ) (hell : 0 < ell) :
    (fun n : ℕ =>
        normalizedPowerCoefficient ((3 * ell : ℕ) / (2 : ℝ)) n - 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  have h := normalizedPowerCoefficient_natSuccHalf_error_isBigO (3 * ell - 1)
  have hsucc : 3 * ell - 1 + 1 = 3 * ell := Nat.sub_add_cancel (by omega)
  simpa only [hsucc, Nat.cast_mul, Nat.cast_ofNat] using h

end PerronWright.Transfer
