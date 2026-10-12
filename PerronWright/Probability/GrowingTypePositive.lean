import PerronWright.Probability.GrowingTypeApproximation

/-!
# Strictly positive type counts for every nonempty vertex set

Before a positive truncation level reaches its threshold, the zero level
uses only type zero.  This makes every retained type count positive for
every `n > 0`, without altering the proved limiting properties.
-/

open Filter Topology
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.GrowingTypeCounts

theorem truncatedCounts_zero (w : ℕ → ℝ) (hw : ∀ a, 0 < w a)
    (n : ℕ) (a : Fin 1) : truncatedCounts w 0 n a = n := by
  have ha : a = 0 := Subsingleton.elim _ _
  rw [ha]
  have h := sum_truncatedCounts w hw 0 n
  change (∑ a : Fin 1, truncatedCounts w 0 n a) = n at h
  simpa only [Fin.sum_univ_one] using h

/-- A constructive simultaneous realization with no exceptional positive
vertex sizes: all support counts are positive, exact totals hold, and the
full absolute-variation error and critical-scale minimum have their
claimed limits. -/
theorem exists_positive_growing_realization (w : ℕ → ℝ)
    (hw : ∀ a, 0 < w a) (hs : HasSum w 1) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      (∀ n, ∑ a, truncatedCounts w (level n) n a = n) ∧
      (∀ n > 0, ∀ a, 0 < truncatedCounts w (level n) n a) ∧
      (∀ᶠ n in atTop, requirements w (level n) n) ∧
      Tendsto (fun n : ℕ ↦ ∑' a : ℕ, |extendedLaw w (level n) n a - w a|)
        atTop (nhds 0) ∧
      (∀ B : ℝ, ∀ᶠ n : ℕ in atTop, ∀ a,
        B ≤ (n : ℝ) ^ (1 / 3 : ℝ) * empiricalLaw w (level n) n a) := by
  have hN : ∀ m, ∃ N : ℕ, ∀ n ≥ N, requirements w m n := by
    intro m
    exact eventually_atTop.1 (requirements_eventually w hw m)
  choose threshold hthreshold using hN
  let level := SlowGrowingIndex.index threshold
  have hm : Monotone level := SlowGrowingIndex.index_monotone threshold
  have ht : Tendsto level atTop atTop := SlowGrowingIndex.index_tendsto_atTop threshold
  have hp : ∀ᶠ n in atTop, requirements w (level n) n := by
    filter_upwards [SlowGrowingIndex.threshold_index_le_eventually threshold] with n hn
    exact hthreshold (level n) n hn
  refine ⟨level, hm, ht, fun n ↦ sum_truncatedCounts w hw (level n) n, ?_, hp,
    growing_full_error_tendsto w hw hs level ht hp, growing_scaled_minimum w level ht hp⟩
  intro n hn
  by_cases hl : level n = 0
  · intro a
    have he {m : ℕ} (h : m = 0) (a : Fin (m + 1)) : truncatedCounts w m n a = n := by
      subst m
      exact truncatedCounts_zero w hw n a
    rw [he hl a]
    exact hn
  · have hle : threshold (level n) ≤ n :=
      Nat.findGreatest_of_ne_zero (P := fun m ↦ threshold m ≤ n) rfl hl
    exact (hthreshold (level n) n hle).1

end PerronWright.GrowingTypeCounts
