import PerronWright.Transfer.PositiveHalfIntegerRate

/-!
# Relative size of lower half-step singular coefficients

After a vertical Taylor expansion of a positive-surplus fold numerator,
the term of vertical degree `j` contributes the elementary singularity
`(1 - w)^(-(3 * ell - j) / 2)`.  This file compares its exact coefficient
with the leading exponent `3 * ell / 2` in one statement, without splitting
according to the parity of `j`.
-/

open Filter Asymptotics
open scoped Topology

noncomputable section

namespace PerronWright.Transfer

/-- Every lower singular term in the positive-surplus vertical Taylor
polynomial loses exactly one half power of the coefficient index per unit
of vertical degree.  The comparison is with the exact leading elementary
coefficient, so no asymptotic main term is inserted as an interface. -/
theorem coefficient_halfStep_ratio_isBigO
    (ell j : ℕ) (hell : 0 < ell) (hj : j < 3 * ell) :
    (fun k : ℕ =>
        coefficient (((3 * ell - j : ℕ) : ℝ) / 2) k /
          coefficient (((3 * ell : ℕ) : ℝ) / 2) k) =O[atTop]
      (fun k : ℕ => (k : ℝ) ^ (-((j : ℝ) / 2))) := by
  let s₀ : ℝ := ((3 * ell : ℕ) : ℝ) / 2
  let sⱼ : ℝ := ((3 * ell - j : ℕ) : ℝ) / 2
  have hs₀ : 0 < s₀ := by
    dsimp only [s₀]
    positivity
  have hsⱼ : 0 < sⱼ := by
    dsimp only [sⱼ]
    have hsub : 0 < 3 * ell - j := Nat.sub_pos_of_lt hj
    positivity
  have hratio :=
    (coefficient_isEquivalent sⱼ hsⱼ).div
      (coefficient_isEquivalent s₀ hs₀)
  have hexponent : sⱼ - 1 - (s₀ - 1) = -((j : ℝ) / 2) := by
    dsimp only [sⱼ, s₀]
    rw [Nat.cast_sub (Nat.le_of_lt hj)]
    push_cast
    ring
  have hmain :
      (fun k : ℕ =>
          ((k : ℝ) ^ (sⱼ - 1) / Real.Gamma sⱼ) /
            ((k : ℝ) ^ (s₀ - 1) / Real.Gamma s₀)) =ᶠ[atTop]
        (fun k : ℕ =>
          (Real.Gamma s₀ / Real.Gamma sⱼ) *
            (k : ℝ) ^ (-((j : ℝ) / 2))) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hpow₀ : (k : ℝ) ^ (s₀ - 1) ≠ 0 :=
      (Real.rpow_pos_of_pos hkpos _).ne'
    have hgamma₀ : Real.Gamma s₀ ≠ 0 :=
      (Real.Gamma_pos_of_pos hs₀).ne'
    have hgammaⱼ : Real.Gamma sⱼ ≠ 0 :=
      (Real.Gamma_pos_of_pos hsⱼ).ne'
    calc
      ((k : ℝ) ^ (sⱼ - 1) / Real.Gamma sⱼ) /
          ((k : ℝ) ^ (s₀ - 1) / Real.Gamma s₀) =
          (Real.Gamma s₀ / Real.Gamma sⱼ) *
            ((k : ℝ) ^ (sⱼ - 1) / (k : ℝ) ^ (s₀ - 1)) := by
              field_simp [hpow₀, hgamma₀, hgammaⱼ]
      _ = (Real.Gamma s₀ / Real.Gamma sⱼ) *
            (k : ℝ) ^ (sⱼ - 1 - (s₀ - 1)) := by
              rw [← Real.rpow_sub hkpos]
      _ = (Real.Gamma s₀ / Real.Gamma sⱼ) *
            (k : ℝ) ^ (-((j : ℝ) / 2)) := by rw [hexponent]
  have hequiv := hratio.trans_eventuallyEq hmain
  have hconstant :
      (fun k : ℕ =>
          (Real.Gamma s₀ / Real.Gamma sⱼ) *
            (k : ℝ) ^ (-((j : ℝ) / 2))) =O[atTop]
        (fun k : ℕ => (k : ℝ) ^ (-((j : ℝ) / 2))) :=
    (isBigO_refl
      (fun k : ℕ => (k : ℝ) ^ (-((j : ℝ) / 2))) atTop).const_mul_left
        (Real.Gamma s₀ / Real.Gamma sⱼ)
  exact hequiv.trans_isBigO hconstant

end PerronWright.Transfer
