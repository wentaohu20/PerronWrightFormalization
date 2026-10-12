import PerronWright.Probability.FiniteIrreducibleCriticalTuplePrefactor
import PerronWright.Probability.FiniteIrreduciblePerronCountExpansion
import PerronWright.Probability.CriticalResidualScaling

/-! # Literal finite factorial-density normalization and exact main exponent

The mark probabilities are p_a = μ_a u_a, with Σ μ_a u_a = 1;
the paper's β is Σ μ_a u_a³, not a rescaled Brownian parameter.
At raw critical time the Gaussian enumeration product times the genuine
Perron population main exponential is *exactly* the literal density at
the normalized integer sizes. This is a numeric identity, not a theorem
about the remaining random residual or a realized limiting process.
-/

open Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleFactorialMainIdentity

open FiniteIrreducibleCriticalPrefactorScaling
open FiniteIrreducibleCriticalTuplePrefactor
open FiniteIrreduciblePerronCountExpansion (mainExponent)
open FiniteIrreduciblePearsonProfile (perronMass)

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem perronMass_sum (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    (∑ a, perronMass M hM a) = 1 := M.perronFunction_average hM

theorem alpha_eq_perronMass_square (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    M.alpha hM = ∑ a, (perronMass M hM a)^2 / M.weight a := by
  unfold FiniteIrreducibleModel.alpha FiniteIrreducibleModel.average perronMass
  apply Finset.sum_congr rfl
  intro a _
  field_simp [(M.weight_pos a).ne']

theorem beta_eq_perronMass_cube (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    M.beta hM = ∑ a, (perronMass M hM a)^3 / (M.weight a)^2 := by
  unfold FiniteIrreducibleModel.beta FiniteIrreducibleModel.average perronMass
  apply Finset.sum_congr rfl
  intro a _
  field_simp [(M.weight_pos a).ne']

theorem rawTime_thermal_exact (lambda K : ℝ) {n : ℕ} (hn : 0 < n) :
    (rawTime lambda n - 1) * K^2 / (n : ℝ) =
      lambda * (K / (n : ℝ)^(2/3 : ℝ))^2 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs := (Real.rpow_pos_of_pos hnR (2/3 : ℝ)).ne'
  have hp := CriticalResidualScaling.negativeThird_mul_twoThird_sq hnR
  unfold rawTime
  rw [div_pow]
  field_simp
  linear_combination lambda * K^2 * hp

theorem mainExponent_rawTime_exact (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda K : ℝ) {n : ℕ} (hn : 0 < n) :
    mainExponent M hM (n : ℝ) K (rawTime lambda n) =
      M.alpha hM * lambda * (K / (n : ℝ)^(2/3 : ℝ))^2 / 2 -
        M.beta hM * (K / (n : ℝ)^(2/3 : ℝ))^3 / 6 := by
  have ht := rawTime_thermal_exact lambda K hn
  have hc : K^3 / (n : ℝ)^2 = (K / (n : ℝ)^(2/3 : ℝ))^3 := by
    rw [div_pow, CriticalResidualScaling.twoThird_cube (Nat.cast_nonneg n)]
  unfold mainExponent
  linear_combination M.alpha hM / 2 * ht - M.beta hM / 6 * hc

theorem normalizedSize_sum {q n : ℕ} (k : Fin q → ℕ) :
    (∑ i, normalizedSize n (k i)) = ((∑ i, k i : ℕ) : ℝ) / (n : ℝ)^(2/3 : ℝ) := by
  simp [normalizedSize, Finset.sum_div]

theorem gaussian_product_mul_main_eq_density (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) {q : ℕ} (x : Fin q → ℝ) (r : Fin q → ℕ) :
    limitingTupleGaussianMainTerm M hM lambda x r *
      Real.exp (M.alpha hM * lambda * (∑ i, x i)^2 / 2 -
        M.beta hM * (∑ i, x i)^3 / 6) =
      FactorialDensity.density (M.alpha hM) (M.beta hM) lambda x r := by
  unfold limitingTupleGaussianMainTerm FactorialDensity.density
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  have he : (∑ i, -FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
      (lambda^2 * x i)) +
      (M.alpha hM * lambda * (∑ i, x i)^2 / 2 - M.beta hM * (∑ i, x i)^3 / 6) =
      -FactorialDensity.criticalExponent (M.alpha hM) (M.beta hM) lambda (∑ i, x i) := by
    simp only [FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate,
      FactorialDensity.criticalExponent, ← Finset.mul_sum, mul_assoc]
    ring
  calc
    _ = (∏ i, FactorialDensity.sizeFactor (M.beta hM) (x i) (r i)) *
        Real.exp ((∑ i, -FiniteIrreducibleCriticalWindowRadiusConversion.criticalQuadraticRate M hM *
          (lambda^2 * x i)) +
          (M.alpha hM * lambda * (∑ i, x i)^2 / 2 - M.beta hM * (∑ i, x i)^3 / 6)) := by
      rw [Real.exp_add]
      ring
    _ = _ := by rw [he]; ring

theorem tupleGaussian_mul_main_eq_density (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) {n q : ℕ} (hn : 0 < n)
    (k r : Fin q → ℕ) :
    tupleGaussianMainTerm M hM lambda n k r *
      Real.exp (mainExponent M hM (n : ℝ) ((∑ i, k i : ℕ) : ℝ) (rawTime lambda n)) =
      FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
        (fun i ↦ normalizedSize n (k i)) r := by
  rw [mainExponent_rawTime_exact M hM lambda _ hn, ← normalizedSize_sum k]
  exact gaussian_product_mul_main_eq_density M hM lambda _ r

theorem eventually_tupleGaussian_mul_actual_main_eq_density (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ k r : Fin q → ℕ,
      tupleGaussianMainTerm M hM lambda n k r *
        Real.exp (mainExponent M hM (n : ℝ) ((∑ i, k i : ℕ) : ℝ)
          (CriticalScaling.time lambda n)) =
        FactorialDensity.density (M.alpha hM) (M.beta hM) lambda
          (fun i ↦ normalizedSize n (k i)) r := by
  filter_upwards [CriticalScaling.time_eq_raw_eventually lambda,
    eventually_ge_atTop (1 : ℕ)] with n ht hn k r
  change CriticalScaling.time lambda n = rawTime lambda n at ht
  rw [ht]
  exact tupleGaussian_mul_main_eq_density M hM lambda (by omega) k r

end PerronWright.FiniteIrreducibleFactorialMainIdentity
