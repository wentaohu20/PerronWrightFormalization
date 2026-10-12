import PerronWright.Transfer.PrefactorShiftRate

/-!
# Quantitative polynomial-prefactor coefficient normalization

Combining fixed-shift `O(1/n)` estimates with the pure-power coefficient
rates gives a general finite-polynomial transfer statement. The three
half-integer cases used by tree and unicyclic expansions are corollaries.
No analytic dented-domain remainder transfer is asserted here.
-/

open Filter Asymptotics
open scoped Topology
noncomputable section

namespace PerronWright.Transfer

theorem prefactorCoefficient_normalized_error_isBigO
    (P : Polynomial ℝ) (s : ℝ) (hs : ∀ j : ℕ, s + j ≠ 0)
    (N : ℕ → ℝ)
    (hRerr : (fun n : ℕ => coefficient s n * N n - 1) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹)) :
    (fun n : ℕ => prefactorCoefficient P s n * N n - P.eval 1) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  let R : ℕ → ℝ := fun n => coefficient s n * N n
  let Q : ℕ → ℝ := fun n => prefactorCoefficient P s n / coefficient s n
  have hQ : (fun n => Q n - P.eval 1) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) :=
    prefactorCoefficient_relative_shift_error_isBigO P s hs
  have hInv : (fun n : ℕ => (n : ℝ)⁻¹) =O[atTop] (fun _ => (1 : ℝ)) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).isBigO_one ℝ
  have hR : R =O[atTop] (fun _ => (1 : ℝ)) := by
    have h := (hRerr.trans hInv).add
      (isBigO_refl (fun _ : ℕ => (1 : ℝ)) atTop)
    simpa only [R, sub_add_cancel] using h
  have hQR := hQ.mul hR
  simp only [mul_one] at hQR
  have hPR := hRerr.const_mul_left (P.eval 1)
  have hsum := hQR.add hPR
  apply hsum.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards with n
  have hc : coefficient s n ≠ 0 := coefficient_nonzero_of_no_nat_root s hs n
  dsimp [Q, R]
  field_simp [hc]
  ring

theorem prefactorCoefficient_half_normalized_error_isBigO (P : Polynomial ℝ) :
    (fun n : ℕ => prefactorCoefficient P (1 / 2) n *
      (Real.sqrt Real.pi * Real.sqrt (n : ℝ)) - P.eval 1) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  apply prefactorCoefficient_normalized_error_isBigO P (1 / 2)
    (fun j => (add_pos_of_pos_of_nonneg
      (by norm_num : (0 : ℝ) < 1 / 2) (Nat.cast_nonneg j)).ne')
    (fun n => Real.sqrt Real.pi * Real.sqrt (n : ℝ))
  simpa only [mul_assoc] using coefficient_half_relative_error_isBigO

theorem prefactorCoefficient_neg_half_normalized_error_isBigO (P : Polynomial ℝ) :
    (fun n : ℕ => prefactorCoefficient P (-(1 / 2)) n *
      (-(2 * Real.sqrt Real.pi * (n : ℝ) * Real.sqrt (n : ℝ))) - P.eval 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) :=
  prefactorCoefficient_normalized_error_isBigO P (-(1 / 2))
    coefficient_neg_half_no_nat_root
    (fun n => -(2 * Real.sqrt Real.pi * (n : ℝ) * Real.sqrt (n : ℝ)))
    coefficient_neg_half_relative_error_isBigO

theorem prefactorCoefficient_neg_three_halves_normalized_error_isBigO
    (P : Polynomial ℝ) :
    (fun n : ℕ => prefactorCoefficient P (-(3 / 2)) n *
      (4 * Real.sqrt Real.pi * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 3) - P.eval 1)
      =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) :=
  prefactorCoefficient_normalized_error_isBigO P (-(3 / 2))
    coefficient_neg_three_halves_no_nat_root
    (fun n => 4 * Real.sqrt Real.pi * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 3)
    coefficient_neg_three_halves_relative_error_isBigO

end PerronWright.Transfer
