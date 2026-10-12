import PerronWright.Probability.AnnealedTupleResidualConnectedLawFormula
import PerronWright.Probability.CriticalLocalSizeFactor

/-! # Exact critical rescaling of the actual ordered-tuple prefactor -/

open scoped BigOperators Real

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.CriticalTuplePrefactor

theorem total_edge_exponent_cast {q : ℕ} (k r : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) :
    ((∑ i, (k i+r i-1) : ℕ) : ℝ) =
      ((∑ i, k i : ℕ) : ℝ) + ∑ i, (r i : ℝ) - (q : ℝ) := by
  rw [Nat.cast_sum, Nat.cast_sum]
  have he (i : Fin q) : ((k i+r i-1 : ℕ) : ℝ) = (k i : ℝ)+(r i : ℝ)-1 := by
    rw [Nat.cast_sub (by have := hk i; omega), Nat.cast_add, Nat.cast_one]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp

/-- Exact powers, including the `-1` in each connected edge count. -/
theorem critical_power_identity {q n : ℕ} (hn : 0 < n)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) :
    (n : ℝ)^(2*(q : ℝ)/3) * (n : ℝ)⁻¹^(∑ i, (k i+r i-1)) *
        (n : ℝ)^(∑ i, k i) = ∏ i, (n : ℝ)^(5/3-(r i : ℝ)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hnR.le,
    ← Real.rpow_natCast, ← Real.rpow_add hnR, ← Real.rpow_add hnR,
    ← Real.rpow_sum_of_pos hnR]
  congr 1
  rw [total_edge_exponent_cast k r hk, Finset.sum_sub_distrib]
  simp
  ring

/-- The local graph scaling splits into the actual falling selection
ratio and the product of literal factorial-divided enumerators. -/
theorem tuple_prefactor_scaled {q n : ℕ} (hn : 0 < n)
    (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i) (C : Fin q → ℝ) :
    (n : ℝ)^(2*(q : ℝ)/3) *
      (((n.descFactorial (∑ i, k i) : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
        ((n : ℝ)⁻¹^(∑ i, (k i+r i-1))) * ∏ i, C i) =
      ((n.descFactorial (∑ i, k i) : ℝ) / (n : ℝ)^(∑ i, k i)) *
        ∏ i, ((n : ℝ)^(5/3-(r i : ℝ)) * (C i / ((k i).factorial : ℝ))) := by
  have hnz : (n : ℝ)^(∑ i, k i) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr hn.ne')
  have hfac : (∏ i, ((k i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ ↦ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib,
    ← critical_power_identity hn k r hk]
  field_simp

end PerronWright.CriticalTuplePrefactor
