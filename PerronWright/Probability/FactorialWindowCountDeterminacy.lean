import PerronWright.Probability.FactorialGeneratingSeries
import PerronWright.Probability.FactorialWindowMass

/-!
# The density-window bound supplies joint count determinacy

The actual integrated density bound implies exponential integrability of
any finite count-vector law whose total falling-factorial moments satisfy
that bound.  Equal mixed factorial moments then give equality of the
literal count laws.  This proves the analytic determinacy step; identification
of the Brownian process with these densities is separate work.
-/

open MeasureTheory Filter
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FactorialWindowCountDeterminacy

open BinomialInversion FactorialCountDeterminacy FactorialGeneratingSeries

variable {ι : Type*} [Fintype ι]

/-- Literal total falling-factorial statistic on a finite count partition. -/
def totalFactorial (q : ℕ) (n : ι → ℕ) : ℝ := (totalCount n).descFactorial q

theorem totalChoose_eq (q : ℕ) (n : ι → ℕ) :
    ((totalCount n).choose q : ℝ) = totalFactorial q n / (q.factorial : ℝ) := by
  have hp : (q.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  unfold totalFactorial
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  field_simp

/-- The literal window density bound proves exponential integrability of
the total count in every finite partition of that window. -/
theorem total_exp_integrable_of_window_bound_argument
    (μ : Measure (ι → ℕ)) (alpha lambda : ℝ) {beta a b : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (z : ℝ) (hz : 0 ≤ z)
    (hint : ∀ q, Integrable (totalFactorial q) μ)
    (hbound : ∀ q, (∫ n, totalFactorial q n ∂μ) ≤
      FactorialDensity.windowMass q alpha beta lambda a b R) :
    Integrable (fun n ↦ (1 + z) ^ totalCount n) μ := by
  apply total_exp_integrable_of_moment_series_argument μ z hz
  · intro q
    simp_rw [totalChoose_eq]
    exact (hint q).div_const _
  · have hm := FactorialDensity.summable_windowMass_factorial
      alpha lambda hbeta ha hab R z
    apply hm.of_nonneg_of_le
    · intro q
      exact mul_nonneg (by positivity) (integral_nonneg (fun n ↦ Nat.cast_nonneg _))
    · intro q
      simp_rw [totalChoose_eq]
      rw [integral_div, ← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (hbound q) (by positivity)

theorem total_exp_integrable_of_window_bound
    (μ : Measure (ι → ℕ)) (alpha lambda : ℝ) {beta a b : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (hint : ∀ q, Integrable (totalFactorial q) μ)
    (hbound : ∀ q, (∫ n, totalFactorial q n ∂μ) ≤
      FactorialDensity.windowMass q alpha beta lambda a b R) :
    Integrable (fun n ↦ (3 : ℝ) ^ totalCount n) μ := by
  simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using
    total_exp_integrable_of_window_bound_argument μ alpha lambda
      hbeta ha hab R 2 (by norm_num) hint hbound

/-- Determinacy of every finite joint count partition under the paper's
actual density-window majorant.  No probability-generating-functional
relation or moment-determination premise is assumed. -/
theorem count_laws_eq_of_window_factorial_moments
    (μ ν : Measure (ι → ℕ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (alpha lambda : ℝ) {beta a b : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (hμint : ∀ q, Integrable (totalFactorial q) μ)
    (hνint : ∀ q, Integrable (totalFactorial q) ν)
    (hμbound : ∀ q, (∫ n, totalFactorial q n ∂μ) ≤
      FactorialDensity.windowMass q alpha beta lambda a b R)
    (hνbound : ∀ q, (∫ n, totalFactorial q n ∂ν) ≤
      FactorialDensity.windowMass q alpha beta lambda a b R)
    (hmom : ∀ q, factorialMoment μ q = factorialMoment ν q) : μ = ν := by
  exact measure_eq_of_factorialMoments_of_total_exp μ ν
    (total_exp_integrable_of_window_bound μ alpha lambda hbeta ha hab R hμint hμbound)
    (total_exp_integrable_of_window_bound ν alpha lambda hbeta ha hab R hνint hνbound)
    hmom

end PerronWright.FactorialWindowCountDeterminacy
