import PerronWright.Transfer.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomial prefactors for power singularities

The finite convolution below is the actual complex analytic coefficient sequence of
`P(z) * (1 - z)^(-s)`. For real `s > 0`, its normalized limit is `P(1) / Gamma(s)`;
when `P(1) ≠ 0`, this gives the corresponding asymptotic equivalence.
-/

open Filter Asymptotics
open scoped Topology

noncomputable section

namespace PerronWright.Transfer

theorem nat_sub_div_tendsto_one (j : ℕ) :
    Tendsto (fun n : ℕ => ((n - j : ℕ) : ℝ) / n) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => 1 - (j : ℝ) * (n : ℝ)⁻¹)
      atTop (𝓝 (1 - (j : ℝ) * 0)) := tendsto_const_nhds.sub
    (tendsto_const_nhds.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have h' : Tendsto (fun n : ℕ => 1 - (j : ℝ) * (n : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop j, eventually_ne_atTop 0] with n hn hn0
  rw [Nat.cast_sub hn, sub_div, div_self (by exact_mod_cast hn0), div_eq_mul_inv]

theorem shifted_coefficient_tendsto (s : ℝ) (hs : 0 < s) (j : ℕ) :
    Tendsto (fun n : ℕ => coefficient s (n - j) / (n : ℝ) ^ (s - 1))
      atTop (𝓝 (1 / Real.Gamma s)) := by
  have hc := (coefficient_tendsto s hs).comp (tendsto_sub_atTop_nat j)
  have hr := (nat_sub_div_tendsto_one j).rpow_const (p := s - 1) (Or.inl one_ne_zero)
  have h := hc.mul hr
  simp only [Real.one_rpow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop j] with n hn
  have hmpos : (0 : ℝ) < (n - j : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hn
  have hm : ((n - j : ℕ) : ℝ) ^ (s - 1) ≠ 0 := (Real.rpow_pos_of_pos hmpos _).ne'
  change coefficient s (n - j) / ((n - j : ℕ) : ℝ) ^ (s - 1) *
      (((n - j : ℕ) : ℝ) / n) ^ (s - 1) = _
  rw [Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  field_simp

/-- A fixed shift does not change the leading coefficient asymptotic. -/
theorem shifted_coefficient_ratio_tendsto (s : ℝ) (hs : 0 < s) (j : ℕ) :
    Tendsto (fun n : ℕ => coefficient s (n - j) / coefficient s n) atTop (𝓝 1) := by
  have hg : 1 / Real.Gamma s ≠ 0 := one_div_ne_zero (Real.Gamma_pos_of_pos hs).ne'
  have h := (shifted_coefficient_tendsto s hs j).div (coefficient_tendsto s hs) hg
  rw [div_self hg] at h
  apply h.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  exact div_div_div_cancel_right₀ (Real.rpow_pos_of_pos hnpos (s - 1)).ne' _ _

/-- The exact finite convolution, with the low-degree terms correctly truncated. -/
def prefactorCoefficient (P : Polynomial ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ P.support, if j ≤ n then P.coeff j * coefficient s (n - j) else 0

theorem prefactorCoefficient_eventually_eq (P : Polynomial ℝ) (s : ℝ) :
    (fun n => prefactorCoefficient P s n) =ᶠ[atTop]
      (fun n => ∑ j ∈ P.support, P.coeff j * coefficient s (n - j)) := by
  filter_upwards [eventually_ge_atTop P.natDegree] with n hn
  unfold prefactorCoefficient
  apply Finset.sum_congr rfl
  intro j hj
  exact if_pos ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)).trans hn)

/-- The normalized limit also holds when the prefactor vanishes at the singularity. -/
theorem prefactorCoefficient_tendsto (P : Polynomial ℝ) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => prefactorCoefficient P s n / (n : ℝ) ^ (s - 1))
      atTop (𝓝 (P.eval 1 / Real.Gamma s)) := by
  have h := tendsto_finsetSum P.support
    (fun j _ => (shifted_coefficient_tendsto s hs j).const_mul (P.coeff j))
  have heval : (∑ j ∈ P.support, P.coeff j * (1 / Real.Gamma s)) =
      P.eval 1 / Real.Gamma s := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum]
    simp only [one_pow, mul_one, Finset.sum_div, mul_one_div]
  rw [heval] at h
  apply h.congr'
  filter_upwards [prefactorCoefficient_eventually_eq P s] with n hn
  rw [hn, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hasSum_monomial_mul {a : ℕ → ℂ} {z F : ℂ}
    (h : HasSum (fun n => z ^ n * a n) F) (j : ℕ) :
    HasSum (fun n => z ^ n * (if j ≤ n then a (n - j) else 0)) (z ^ j * F) := by
  let f := fun n => z ^ n * (if j ≤ n then a (n - j) else 0)
  have htail : HasSum (fun n => f (n + j)) (z ^ j * F) := by
    convert! h.mul_left (z ^ j) using 1
    ext n
    simp only [f, Nat.le_add_left, if_true, Nat.add_sub_cancel, pow_add]
    ring
  have hprefix : ∑ n ∈ Finset.range j, f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [f, if_neg (Nat.not_le.mpr (Finset.mem_range.mp hn)), mul_zero]
  have hsum := (hasSum_nat_add_iff j).mp htail
  simpa only [hprefix, add_zero] using hsum

theorem prefactorCoefficient_hasSum (P : Polynomial ℝ) (s : ℝ) {z F : ℂ}
    (h : HasSum (fun n => z ^ n * (coefficient s n : ℂ)) F) :
    HasSum (fun n => z ^ n * (prefactorCoefficient P s n : ℂ))
      (P.eval₂ (algebraMap ℝ ℂ) z * F) := by
  have hsum := hasSum_sum (s := P.support)
    (fun j _ => (hasSum_monomial_mul h j).mul_left (P.coeff j : ℂ))
  convert! hsum using 1
  · ext n
    unfold prefactorCoefficient
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ≤ n
    · simp only [if_pos hj, Complex.ofReal_mul]
      ring
    · simp only [if_neg hj, Complex.ofReal_zero, mul_zero]
  · rw [Polynomial.eval₂_eq_sum, Polynomial.sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    change ((P.coeff j : ℂ) * z ^ j) * F = (P.coeff j : ℂ) * (z ^ j * F)
    ring

/-- The complex analytic series for a real polynomial times a power singularity. -/
def prefactorPowerSeries (P : Polynomial ℝ) (s : ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (fun n => (prefactorCoefficient P s n : ℂ))

theorem prefactorPowerSeries_coeff (P : Polynomial ℝ) (s : ℝ) (n : ℕ) :
    (prefactorPowerSeries P s).coeff n = (prefactorCoefficient P s n : ℂ) :=
  FormalMultilinearSeries.coeff_ofScalars

theorem prefactorPowerSeries_hasFPowerSeriesAt (P : Polynomial ℝ) (s : ℝ) :
    HasFPowerSeriesAt (fun z : ℂ => P.eval₂ (algebraMap ℝ ℂ) z * (1 - z) ^ (-(s : ℂ)))
      (prefactorPowerSeries P s) 0 := by
  rw [hasFPowerSeriesAt_iff]
  have h := hasFPowerSeriesAt_iff.mp (powerSeries_neg_cpow s).hasFPowerSeriesAt
  filter_upwards [h] with z hz
  simp only [zero_add, powerSeries_coeff, smul_eq_mul] at hz
  simpa only [prefactorPowerSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
    zero_add] using prefactorCoefficient_hasSum P s hz

/-- The leading term for a polynomial prefactor nonzero at the singularity. -/
theorem prefactorCoefficient_isEquivalent (P : Polynomial ℝ) (hP : P.eval 1 ≠ 0)
    (s : ℝ) (hs : 0 < s) :
    prefactorCoefficient P s ~[atTop]
      (fun n : ℕ => P.eval 1 * (n : ℝ) ^ (s - 1) / Real.Gamma s) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hg : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos hs).ne'
  have h := (prefactorCoefficient_tendsto P s hs).div_const (P.eval 1 / Real.Gamma s)
  have hq : P.eval 1 / Real.Gamma s ≠ 0 := div_ne_zero hP hg
  rw [div_self hq] at h
  convert h using 1
  ext n
  simp only [Pi.div_apply, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end PerronWright.Transfer
