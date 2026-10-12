import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Literal binomial inversion for finite count vectors

The pointwise identities below are finite combinatorics, including for
unbounded count-valued random variables: at each outcome only finitely many
terms are nonzero.  They are the inversion step used to recover joint count
laws from mixed factorial moments.  No generating-functional identity is
assumed.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BinomialInversion

/-- Coefficient of the `q`-th binomial moment in the atom at `m`. -/
def coefficient (m q : ℕ) : ℝ := (-1 : ℝ) ^ (q + m) * (q.choose m : ℝ)

/-- The pointwise scalar inversion term. -/
def scalarTerm (m q n : ℕ) : ℝ := coefficient m q * (n.choose q : ℝ)

theorem scalarTerm_eq_zero_of_lt_left {m q n : ℕ} (h : q < m) :
    scalarTerm m q n = 0 := by
  simp [scalarTerm, coefficient, Nat.choose_eq_zero_of_lt h]

theorem scalarTerm_eq_zero_of_lt_right {m q n : ℕ} (h : n < q) :
    scalarTerm m q n = 0 := by
  simp [scalarTerm, Nat.choose_eq_zero_of_lt h]

theorem scalarTerm_add (m q n : ℕ) :
    scalarTerm m (m + q) n =
      (n.choose m : ℝ) * ((-1 : ℝ) ^ q * ((n - m).choose q : ℝ)) := by
  have h := Nat.choose_mul (n := n) (k := m + q) (Nat.le_add_right m q)
  have hc : (n.choose (m + q) : ℝ) * ((m + q).choose m : ℝ) =
      (n.choose m : ℝ) * ((n - m).choose q : ℝ) := by
    exact_mod_cast (by simpa only [Nat.add_sub_cancel_left] using h)
  unfold scalarTerm coefficient
  rw [show m + q + m = q + 2 * m by omega, pow_add, pow_mul]
  norm_num
  calc
    _ = (-1 : ℝ) ^ q * ((n.choose (m + q) : ℝ) * ((m + q).choose m : ℝ)) := by ring
    _ = _ := by rw [hc]; ring

theorem alternating_choose_sum (n : ℕ) :
    (∑ q ∈ Finset.range (n + 1), (-1 : ℝ) ^ q * (n.choose q : ℝ)) =
      if n = 0 then 1 else 0 := by
  exact_mod_cast (Int.alternating_sum_range_choose (n := n))

/-- Exact scalar indicator inversion, with no infinite-series argument. -/
theorem scalar_sum (m n : ℕ) :
    (∑ q ∈ Finset.range (n + 1), scalarTerm m q n) =
      if n = m then 1 else 0 := by
  by_cases hmn : m ≤ n
  · rw [show n + 1 = m + (n - m + 1) by omega, Finset.sum_range_add]
    have hzero : (∑ q ∈ Finset.range m, scalarTerm m q n) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      exact scalarTerm_eq_zero_of_lt_left (Finset.mem_range.mp hq)
    rw [hzero, zero_add]
    simp_rw [scalarTerm_add]
    rw [← Finset.mul_sum, alternating_choose_sum]
    by_cases hnm : n = m
    · simp [hnm]
    · have hnsub : n - m ≠ 0 := by omega
      simp [hnsub, hnm]
  · have hnm : n ≠ m := by omega
    rw [if_neg hnm]
    apply Finset.sum_eq_zero
    intro q hq
    have hqn : q ≤ n := by simpa using Finset.mem_range.mp hq
    exact scalarTerm_eq_zero_of_lt_left (by omega)

theorem scalar_tsum (m n : ℕ) :
    (∑' q : ℕ, scalarTerm m q n) = if n = m then 1 else 0 := by
  rw [tsum_eq_sum (s := Finset.range (n + 1))]
  · exact scalar_sum m n
  · intro q hq
    exact scalarTerm_eq_zero_of_lt_right (by simpa using hq)

variable {ι : Type*} [Fintype ι]

/-- Mixed binomial-moment coefficient, coordinate by coordinate. -/
def jointCoefficient (m q : ι → ℕ) : ℝ := ∏ i, coefficient (m i) (q i)

/-- The literal mixed binomial polynomial on a count vector. -/
def binomialPolynomial (q n : ι → ℕ) : ℝ := ∏ i, (n i).choose (q i)

def jointTerm (m q n : ι → ℕ) : ℝ :=
  jointCoefficient m q * binomialPolynomial q n

theorem jointTerm_eq_prod (m q n : ι → ℕ) :
    jointTerm m q n = ∏ i, scalarTerm (m i) (q i) (n i) := by
  simp only [jointTerm, jointCoefficient, binomialPolynomial, scalarTerm,
    Finset.prod_mul_distrib]

theorem jointTerm_zero_outside (m n : ι → ℕ) (q : ι → ℕ)
    (hq : q ∉ Fintype.piFinset (fun i ↦ Finset.range (n i + 1))) :
    jointTerm m q n = 0 := by
  rw [Fintype.mem_piFinset] at hq
  push Not at hq
  obtain ⟨i, hi⟩ := hq
  rw [jointTerm_eq_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact scalarTerm_eq_zero_of_lt_right (by simpa using hi)

/-- Pointwise joint atom inversion.  The infinite sum is actually finitely
supported at each count vector. -/
theorem joint_tsum (m n : ι → ℕ) :
    (∑' q : ι → ℕ, jointTerm m q n) = if n = m then 1 else 0 := by
  rw [tsum_eq_sum (s := Fintype.piFinset (fun i ↦ Finset.range (n i + 1)))
    (jointTerm_zero_outside m n)]
  simp_rw [jointTerm_eq_prod]
  rw [← Finset.prod_univ_sum (fun i ↦ Finset.range (n i + 1))
    (fun i j ↦ scalarTerm (m i) j (n i))]
  simp_rw [scalar_sum]
  by_cases hnm : n = m
  · simp [hnm]
  · rw [if_neg hnm]
    have hi : ∃ i, n i ≠ m i := by
      by_contra h
      push Not at h
      exact hnm (funext h)
    obtain ⟨i, hi⟩ := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem jointCoefficient_abs_le (m q : ι → ℕ) :
    |jointCoefficient m q| ≤ (2 : ℝ) ^ (∑ i, q i) := by
  rw [jointCoefficient, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro i _
    exact abs_nonneg _
  · intro i _
    simp only [coefficient, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ ((q i).choose (m i) : ℝ) by positivity)]
    exact_mod_cast Nat.choose_le_two_pow (q i) (m i)

end PerronWright.BinomialInversion
