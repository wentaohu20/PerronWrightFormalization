import PerronWright.Probability.GrowingTypeCounts

/-!
# Total absolute variation of the constructed growing type laws

The finite empirical probabilities are extended by zero to all of `ℕ`.
The full infinite sum of absolute errors is controlled by the actual
rounding error plus twice the discarded probability mass.
-/

open Filter Topology
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.GrowingTypeCounts

def extendedLaw (w : ℕ → ℝ) (m n : ℕ) (a : ℕ) : ℝ :=
  if h : a < m + 1 then empiricalLaw w m n ⟨a, h⟩ else 0

theorem extendedLaw_fin (w : ℕ → ℝ) (m n : ℕ) (a : Fin (m + 1)) :
    extendedLaw w m n a = empiricalLaw w m n a := by
  simp [extendedLaw, a.isLt]

theorem extendedLaw_tail (w : ℕ → ℝ) (m n a : ℕ) :
    extendedLaw w m n (a + (m + 1)) = 0 := by
  simp only [extendedLaw, dif_neg (by omega : ¬ a + (m + 1) < m + 1)]

theorem truncatedLaw_ge_weight (w : ℕ → ℝ) (hw : ∀ a, 0 < w a)
    (hs : HasSum w 1) (m : ℕ) (a : Fin (m + 1)) :
    w a ≤ truncatedLaw w m a := by
  apply (le_div_iff₀ (mass_pos w hw m)).2
  exact (mul_le_mul_of_nonneg_left (mass_le_one w hw hs m) (hw a).le).trans_eq (mul_one _)

theorem truncation_error_eq (w : ℕ → ℝ) (hw : ∀ a, 0 < w a)
    (hs : HasSum w 1) (m : ℕ) :
    (∑ a : Fin (m + 1), |truncatedLaw w m a - w a|) = 1 - mass w m := by
  simp_rw [abs_of_nonneg (sub_nonneg.mpr (truncatedLaw_ge_weight w hw hs m _))]
  rw [Finset.sum_sub_distrib, sum_truncatedLaw w hw m]
  rfl

theorem inside_error_le (w : ℕ → ℝ) (hw : ∀ a, 0 < w a)
    (hs : HasSum w 1) (m n : ℕ) :
    (∑ a : Fin (m + 1), |empiricalLaw w m n a - w a|) ≤
      (∑ a, |empiricalLaw w m n a - truncatedLaw w m a|) + (1 - mass w m) := by
  calc
    _ ≤ ∑ a : Fin (m + 1),
        (|empiricalLaw w m n a - truncatedLaw w m a| + |truncatedLaw w m a - w a|) :=
      Finset.sum_le_sum (fun a _ ↦ abs_sub_le _ _ _)
    _ = _ := by rw [Finset.sum_add_distrib, truncation_error_eq w hw hs]

theorem full_error_summable (w : ℕ → ℝ) (hw : ∀ a, 0 < w a)
    (hs : HasSum w 1) (m n : ℕ) :
    Summable (fun a : ℕ ↦ |extendedLaw w m n a - w a|) := by
  apply (summable_nat_add_iff (m + 1)).1
  simpa only [extendedLaw_tail, zero_sub, abs_neg, abs_of_pos (hw _)] using
    (summable_nat_add_iff (m + 1)).2 hs.summable

theorem full_error_eq (w : ℕ → ℝ) (hw : ∀ a, 0 < w a)
    (hs : HasSum w 1) (m n : ℕ) :
    (∑' a : ℕ, |extendedLaw w m n a - w a|) =
      (∑ a : Fin (m + 1), |empiricalLaw w m n a - w a|) + (1 - mass w m) := by
  have he := (full_error_summable w hw hs m n).sum_add_tsum_nat_add (m + 1)
  have ht := hs.summable.sum_add_tsum_nat_add (m + 1)
  rw [hs.tsum_eq, ← mass_eq_sum_range] at ht
  have htail : (∑' a : ℕ, |extendedLaw w m n (a + (m + 1)) - w (a + (m + 1))|) =
      1 - mass w m := by
    simp_rw [extendedLaw_tail, zero_sub, abs_neg, abs_of_pos (hw _)]
    linarith
  rw [htail] at he
  rw [← Fin.sum_univ_eq_sum_range] at he
  simp only [extendedLaw_fin] at he
  exact he.symm

theorem full_error_le (w : ℕ → ℝ) (hw : ∀ a, 0 < w a)
    (hs : HasSum w 1) (m n : ℕ) :
    (∑' a : ℕ, |extendedLaw w m n a - w a|) ≤
      (∑ a, |empiricalLaw w m n a - truncatedLaw w m a|) + 2 * (1 - mass w m) := by
  rw [full_error_eq w hw hs]
  linarith [inside_error_le w hw hs m n]

/-- Actual infinite-dimensional total absolute variation tends to zero
along the constructed slow-growing supports. -/
theorem growing_full_error_tendsto (w : ℕ → ℝ) (hw : ∀ a, 0 < w a)
    (hs : HasSum w 1) (level : ℕ → ℕ) (ht : Tendsto level atTop atTop)
    (hp : ∀ᶠ n in atTop, requirements w (level n) n) :
    Tendsto (fun n : ℕ ↦ ∑' a : ℕ, |extendedLaw w (level n) n a - w a|)
      atTop (nhds 0) := by
  have hcard : Tendsto (fun n : ℕ ↦ ((level n : ℝ) + 1)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop.comp ht)
  have hinv := hcard.inv_tendsto_atTop
  have hmass := (mass_tendsto_one w hs).comp ht
  have hmajor : Tendsto (fun n : ℕ ↦ 1 / (level n + 1 : ℝ) +
      2 * (1 - mass w (level n))) atTop (nhds 0) := by
    have h := hinv.add (((tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub hmass).const_mul 2)
    simpa only [one_div, sub_self, mul_zero, add_zero, Nat.cast_add, Nat.cast_one,
      Pi.inv_apply, Function.comp_apply] using h
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n ↦ tsum_nonneg (fun _ ↦ abs_nonneg _)))
    _ hmajor
  filter_upwards [hp] with n hn
  exact (full_error_le w hw hs (level n) n).trans (by linarith [hn.2.1])

end PerronWright.GrowingTypeCounts
