import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Literal positive integer type counts

Floors of the target finite type law are corrected at one distinguished
type so the vertex counts sum exactly to `n`.  Rounding bounds, convergence,
and eventual positivity are proved, rather than required of an external
finite-support realization.
-/

open Filter Topology
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.FiniteTypeCounts

variable {I : Type*} [Fintype I]

def floorCounts (nu : I → ℝ) (n : ℕ) (a : I) : ℕ := ⌊(n : ℝ) * nu a⌋₊

def deficit (nu : I → ℝ) (n : ℕ) : ℕ := n - ∑ a, floorCounts nu n a

/-- The literal number of type-`a` vertices; all rounding residue is put at
the distinguished type without changing the other type counts. -/
def counts (a0 : I) (nu : I → ℝ) (n : ℕ) (a : I) : ℕ :=
  floorCounts nu n a + if a = a0 then deficit nu n else 0

theorem sum_floorCounts_le (nu : I → ℝ) (hnu : ∀ a, 0 ≤ nu a)
    (hsum : ∑ a, nu a = 1) (n : ℕ) : ∑ a, floorCounts nu n a ≤ n := by
  have he : (∑ a, (floorCounts nu n a : ℝ)) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ a, (n : ℝ) * nu a := Finset.sum_le_sum (fun a _ ↦
        Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (hnu a)))
      _ = _ := by rw [← Finset.mul_sum, hsum, mul_one]
  exact_mod_cast he

theorem sum_counts (a0 : I) (nu : I → ℝ) (hnu : ∀ a, 0 ≤ nu a)
    (hsum : ∑ a, nu a = 1) (n : ℕ) : ∑ a, counts a0 nu n a = n := by
  have hl := sum_floorCounts_le nu hnu hsum n
  simp only [counts, Finset.sum_add_distrib]
  have hi : (∑ a : I, if a = a0 then deficit nu n else 0) = deficit nu n := by simp
  rw [hi, deficit]
  omega

theorem floorCounts_le_counts (a0 : I) (nu : I → ℝ) (n : ℕ) (a : I) :
    floorCounts nu n a ≤ counts a0 nu n a := Nat.le_add_right _ _

def roundingRemainder (nu : I → ℝ) (n : ℕ) (a : I) : ℝ :=
  (n : ℝ) * nu a - floorCounts nu n a

omit [Fintype I] in
theorem roundingRemainder_nonneg (nu : I → ℝ) (hnu : ∀ a, 0 ≤ nu a)
    (n : ℕ) (a : I) : 0 ≤ roundingRemainder nu n a :=
  sub_nonneg.mpr (Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (hnu a)))

omit [Fintype I] in
theorem roundingRemainder_lt_one (nu : I → ℝ) (n : ℕ) (a : I) :
    roundingRemainder nu n a < 1 := by
  have h := Nat.lt_floor_add_one ((n : ℝ) * nu a)
  unfold roundingRemainder floorCounts
  linarith

theorem deficit_eq_sum_remainders (nu : I → ℝ) (hnu : ∀ a, 0 ≤ nu a)
    (hsum : ∑ a, nu a = 1) (n : ℕ) :
    (deficit nu n : ℝ) = ∑ a, roundingRemainder nu n a := by
  rw [deficit, Nat.cast_sub (sum_floorCounts_le nu hnu hsum n), Nat.cast_sum]
  simp only [roundingRemainder, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, hsum, mul_one]

theorem deficit_le_card (nu : I → ℝ) (hnu : ∀ a, 0 ≤ nu a)
    (hsum : ∑ a, nu a = 1) (n : ℕ) :
    (deficit nu n : ℝ) ≤ Fintype.card I := by
  rw [deficit_eq_sum_remainders nu hnu hsum]
  calc
    _ ≤ ∑ _a : I, (1 : ℝ) :=
      Finset.sum_le_sum (fun a _ ↦ (roundingRemainder_lt_one nu n a).le)
    _ = _ := by simp

/-- Quantitative total absolute rounding error before division by `n`. -/
theorem sum_counts_error_le (a0 : I) (nu : I → ℝ) (hnu : ∀ a, 0 ≤ nu a)
    (hsum : ∑ a, nu a = 1) (n : ℕ) :
    (∑ a, |(counts a0 nu n a : ℝ) - (n : ℝ) * nu a|) ≤
      2 * (Fintype.card I : ℝ) := by
  have he (a : I) : (counts a0 nu n a : ℝ) - (n : ℝ) * nu a =
      (if a = a0 then (deficit nu n : ℝ) else 0) - roundingRemainder nu n a := by
    unfold counts roundingRemainder
    split_ifs <;> simp only [Nat.cast_add, Nat.cast_zero] <;> ring
  have hp (a : I) : |(counts a0 nu n a : ℝ) - (n : ℝ) * nu a| ≤
      (if a = a0 then (deficit nu n : ℝ) else 0) + roundingRemainder nu n a := by
    rw [he]
    have hc : 0 ≤ (if a = a0 then (deficit nu n : ℝ) else 0) := by split_ifs <;> positivity
    simpa only [abs_of_nonneg hc, abs_of_nonneg (roundingRemainder_nonneg nu hnu n a)]
      using abs_sub (if a = a0 then (deficit nu n : ℝ) else 0) (roundingRemainder nu n a)
  calc
    _ ≤ ∑ a : I, ((if a = a0 then (deficit nu n : ℝ) else 0) +
          roundingRemainder nu n a) := Finset.sum_le_sum (fun a _ ↦ hp a)
    _ = 2 * (deficit nu n : ℝ) := by
      rw [Finset.sum_add_distrib, ← deficit_eq_sum_remainders nu hnu hsum]
      simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (deficit_le_card nu hnu hsum n) (by norm_num)

/-- The empirical law attached to the integer counts. -/
def empiricalLaw (a0 : I) (nu : I → ℝ) (n : ℕ) (a : I) : ℝ :=
  counts a0 nu n a / (n : ℝ)

theorem sum_empiricalLaw (a0 : I) (nu : I → ℝ) (hnu : ∀ a, 0 ≤ nu a)
    (hsum : ∑ a, nu a = 1) {n : ℕ} (hn : 0 < n) :
    ∑ a, empiricalLaw a0 nu n a = 1 := by
  simp only [empiricalLaw, ← Finset.sum_div, ← Nat.cast_sum, sum_counts a0 nu hnu hsum n]
  exact div_self (by exact_mod_cast hn.ne')

/-- Total-variation rounding control for a fixed finite type law. -/
theorem sum_empirical_error_le (a0 : I) (nu : I → ℝ) (hnu : ∀ a, 0 ≤ nu a)
    (hsum : ∑ a, nu a = 1) {n : ℕ} (hn : 0 < n) :
    (∑ a, |empiricalLaw a0 nu n a - nu a|) ≤
      2 * (Fintype.card I : ℝ) / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he (a : I) : |empiricalLaw a0 nu n a - nu a| =
      |(counts a0 nu n a : ℝ) - (n : ℝ) * nu a| / (n : ℝ) := by
    unfold empiricalLaw
    have hd : (counts a0 nu n a : ℝ) / (n : ℝ) - nu a =
        ((counts a0 nu n a : ℝ) - (n : ℝ) * nu a) / (n : ℝ) := by
      field_simp
    rw [hd, abs_div, abs_of_pos hnR]
  simp_rw [he]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (sum_counts_error_le a0 nu hnu hsum n) hnR.le

theorem empirical_error_tendsto_zero (a0 : I) (nu : I → ℝ)
    (hnu : ∀ a, 0 ≤ nu a) (hsum : ∑ a, nu a = 1) :
    Tendsto (fun n ↦ ∑ a, |empiricalLaw a0 nu n a - nu a|) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ ↦ 2 * (Fintype.card I : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)))
    _ ht
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact sum_empirical_error_le a0 nu hnu hsum (by omega : 0 < n)

/-- Positive target masses give strictly positive deterministic type
counts simultaneously, once `n` is sufficiently large. -/
theorem counts_pos_eventually (a0 : I) (nu : I → ℝ) (hnu : ∀ a, 0 < nu a) :
    ∀ᶠ n : ℕ in atTop, ∀ a, 0 < counts a0 nu n a := by
  apply eventually_all.mpr
  intro a
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) * nu a) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (hnu a)
  filter_upwards [ht.eventually_ge_atTop 1] with n hn
  exact lt_of_lt_of_le (Nat.floor_pos.mpr hn) (floorCounts_le_counts a0 nu n a)

end PerronWright.FiniteTypeCounts
