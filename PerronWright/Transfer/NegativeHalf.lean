import PerronWright.Transfer.ShiftError

/-!
# Exact coefficients and leading asymptotics for positive half-integer powers

The singularity analysis of tree and unicyclic terms also needs the
coefficients of `(1-z)^(1/2)` and `(1-z)^(3/2)`.  The general binomial
series in `Base` gives their exact expansion.  Here we relate those
coefficients algebraically to the proved positive half-power coefficients
and derive their leading asymptotics without a Gamma formula at negative
arguments.  This is not a general dented-domain transfer theorem.
-/

open Filter Asymptotics
open scoped Topology
noncomputable section

namespace PerronWright.Transfer

theorem coefficient_neg_half_relation (n : ℕ) :
    coefficient (-(1 / 2)) n =
      -coefficient (1 / 2) n / (2 * (n : ℝ) - 1) := by
  induction n with
  | zero => norm_num [coefficient]
  | succ n ih =>
      rw [coefficient_succ, coefficient_succ, ih]
      push_cast
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      have hd : 2 * (n : ℝ) - 1 ≠ 0 := by
        intro h
        have hnat : 2 * n = 1 := by exact_mod_cast (sub_eq_zero.mp h)
        omega
      have hd' : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
      have hden : 1 + (n : ℝ) * 2 ≠ 0 := by positivity
      field_simp [hn, hd, hd', hden]
      ring_nf
      field_simp [hden]
      ring

theorem coefficient_neg_three_halves_relation (n : ℕ) :
    coefficient (-(3 / 2)) n =
      3 * coefficient (1 / 2) n /
        ((2 * (n : ℝ) - 3) * (2 * (n : ℝ) - 1)) := by
  induction n with
  | zero => norm_num [coefficient]
  | succ n ih =>
      rw [coefficient_succ, coefficient_succ, ih]
      push_cast
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      have hd1 : 2 * (n : ℝ) - 3 ≠ 0 := by
        intro h
        have hnat : 2 * n = 3 := by exact_mod_cast (sub_eq_zero.mp h)
        omega
      have hd2 : 2 * (n : ℝ) - 1 ≠ 0 := by
        intro h
        have hnat : 2 * n = 1 := by exact_mod_cast (sub_eq_zero.mp h)
        omega
      have hd3 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
      have hden : -1 + (n : ℝ) ^ 2 * 4 ≠ 0 := by
        intro h
        have hprod := mul_ne_zero hd2 hd3
        apply hprod
        nlinarith
      field_simp [hn, hd1, hd2, hd3, hden]
      ring_nf
      field_simp [hden]
      ring

theorem tendsto_natCast_div_two_sub_one :
    Tendsto (fun n : ℕ => (n : ℝ) / (2 * n - 1)) atTop (𝓝 (1 / 2 : ℝ)) := by
  convert tendsto_add_mul_div_add_mul_atTop_nhds
    (0 : ℝ) (-1) 1 (by norm_num : (2 : ℝ) ≠ 0) using 1
  · ext n
    simp only [zero_add, one_mul]
    ring_nf

theorem coefficient_neg_half_normalized_tendsto :
    Tendsto (fun n : ℕ =>
      coefficient (-(1 / 2)) n / (n : ℝ) ^ (-(3 / 2) : ℝ))
      atTop (𝓝 (-(1 / (2 * Real.Gamma (1 / 2))))) := by
  have h := (coefficient_tendsto (1 / 2) (by norm_num)).mul
    tendsto_natCast_div_two_sub_one
  have h' : Tendsto (fun n : ℕ =>
      -((coefficient (1 / 2) n / (n : ℝ) ^ (-(1 / 2) : ℝ)) *
        ((n : ℝ) / (2 * n - 1)))) atTop
      (𝓝 (-(1 / (2 * Real.Gamma (1 / 2))))) := by
    convert h.neg using 1
    · ext n
      congr 1
      congr 2
      norm_num
    · ring_nf
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hd : 2 * (n : ℝ) - 1 ≠ 0 := by
    intro h
    have hnat : 2 * n = 1 := by exact_mod_cast (sub_eq_zero.mp h)
    omega
  have hp : (n : ℝ) ^ (-(3 / 2) : ℝ) =
      (n : ℝ) ^ (-(1 / 2) : ℝ) / n := by
    calc
      _ = (n : ℝ) ^ (-(1 / 2) : ℝ) / (n : ℝ) ^ (1 : ℝ) := by
        rw [← Real.rpow_sub hnpos]
        congr 1
        norm_num
      _ = _ := by rw [Real.rpow_one]
  rw [coefficient_neg_half_relation, hp]
  have hp0 : (n : ℝ) ^ (-(1 / 2) : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  field_simp [hn0, hd, hp0]

theorem tendsto_natCast_div_two_sub_three :
    Tendsto (fun n : ℕ => (n : ℝ) / (2 * n - 3)) atTop (𝓝 (1 / 2 : ℝ)) := by
  convert tendsto_add_mul_div_add_mul_atTop_nhds
    (0 : ℝ) (-3) 1 (by norm_num : (2 : ℝ) ≠ 0) using 1
  ext n
  simp only [zero_add, one_mul]
  ring_nf

theorem coefficient_neg_three_halves_normalized_tendsto :
    Tendsto (fun n : ℕ =>
      coefficient (-(3 / 2)) n / (n : ℝ) ^ (-(5 / 2) : ℝ))
      atTop (𝓝 (3 / (4 * Real.Gamma (1 / 2)))) := by
  have hrat : Tendsto (fun n : ℕ =>
      3 * ((n : ℝ) / (2 * n - 3) * ((n : ℝ) / (2 * n - 1))))
      atTop (𝓝 (3 / 4 : ℝ)) := by
    convert tendsto_const_nhds.mul
      (tendsto_natCast_div_two_sub_three.mul tendsto_natCast_div_two_sub_one) using 1
    norm_num
  have h := (coefficient_tendsto (1 / 2) (by norm_num)).mul hrat
  have h' : Tendsto (fun n : ℕ =>
      (coefficient (1 / 2) n / (n : ℝ) ^ (-(1 / 2) : ℝ)) *
        (3 * ((n : ℝ) / (2 * n - 3) * ((n : ℝ) / (2 * n - 1))))) atTop
      (𝓝 (3 / (4 * Real.Gamma (1 / 2)))) := by
    convert h using 1
    · ext n
      congr 1
      congr 2
      norm_num
    · ring_nf
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hd1 : 2 * (n : ℝ) - 3 ≠ 0 := by
    intro h
    have hnat : 2 * n = 3 := by exact_mod_cast (sub_eq_zero.mp h)
    omega
  have hd2 : 2 * (n : ℝ) - 1 ≠ 0 := by
    intro h
    have hnat : 2 * n = 1 := by exact_mod_cast (sub_eq_zero.mp h)
    omega
  have hp : (n : ℝ) ^ (-(5 / 2) : ℝ) =
      (n : ℝ) ^ (-(1 / 2) : ℝ) / (n : ℝ) ^ 2 := by
    calc
      _ = (n : ℝ) ^ (-(1 / 2) : ℝ) / (n : ℝ) ^ (2 : ℝ) := by
        rw [← Real.rpow_sub hnpos]
        congr 1
        norm_num
      _ = _ := by norm_num
  rw [coefficient_neg_three_halves_relation, hp]
  have hp0 : (n : ℝ) ^ (-(1 / 2) : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  field_simp [hn0, hd1, hd2, hp0]

theorem coefficient_neg_half_isEquivalent :
    coefficient (-(1 / 2)) ~[atTop]
      (fun n : ℕ => -(n : ℝ) ^ (-(3 / 2) : ℝ) /
        (2 * Real.sqrt Real.pi)) := by
  have hg : Real.Gamma (1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  have h := coefficient_neg_half_normalized_tendsto.mul_const
    (-(2 * Real.Gamma (1 / 2)))
  have hlim : Tendsto (fun n : ℕ => coefficient (-(1 / 2)) n /
      (-(n : ℝ) ^ (-(3 / 2) : ℝ) /
        (2 * Real.Gamma (1 / 2)))) atTop (𝓝 1) := by
    convert h using 1
    · ext n
      simp only [div_eq_mul_inv, mul_inv_rev, inv_neg, inv_inv]
      ring
    · field_simp [hg]
  apply Asymptotics.isEquivalent_of_tendsto_one
  convert hlim using 1
  ext n
  rw [Real.Gamma_one_half_eq]
  rfl

theorem coefficient_neg_three_halves_isEquivalent :
    coefficient (-(3 / 2)) ~[atTop]
      (fun n : ℕ => 3 * (n : ℝ) ^ (-(5 / 2) : ℝ) /
        (4 * Real.sqrt Real.pi)) := by
  have hg : Real.Gamma (1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  have h := coefficient_neg_three_halves_normalized_tendsto.mul_const
    (4 * Real.Gamma (1 / 2) / 3)
  have hlim : Tendsto (fun n : ℕ => coefficient (-(3 / 2)) n /
      (3 * (n : ℝ) ^ (-(5 / 2) : ℝ) /
        (4 * Real.Gamma (1 / 2)))) atTop (𝓝 1) := by
    convert h using 1
    · ext n
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    · field_simp [hg]
  apply Asymptotics.isEquivalent_of_tendsto_one
  convert hlim using 1
  ext n
  rw [Real.Gamma_one_half_eq]
  rfl

end PerronWright.Transfer
