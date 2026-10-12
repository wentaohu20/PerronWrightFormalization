import Mathlib.Data.Nat.Find
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# A proved slow-growing diagonal index

For each fixed truncation level, an eventual finite-size requirement can
be met along one monotone sequence of levels tending to infinity.  This
elementary selection is used for the actual countable-type realization;
it does not postulate any graph or asymptotic interface.
-/

open Filter
open scoped Classical

noncomputable section

namespace PerronWright.SlowGrowingIndex

/-- The largest level whose finite-size threshold has been reached. -/
def index (threshold : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m ↦ threshold m ≤ n) n

theorem index_le (threshold : ℕ → ℕ) (n : ℕ) : index threshold n ≤ n :=
  Nat.findGreatest_le n

theorem index_monotone (threshold : ℕ → ℕ) : Monotone (index threshold) := by
  intro n n' hn
  exact Nat.findGreatest_mono (fun _ hm ↦ hm.trans hn) hn

theorem index_tendsto_atTop (threshold : ℕ → ℕ) :
    Tendsto (index threshold) atTop atTop := by
  apply tendsto_atTop.2
  intro m
  filter_upwards [eventually_ge_atTop (max m (threshold m))] with n hn
  exact Nat.le_findGreatest (le_trans (le_max_left _ _) hn)
    (le_trans (le_max_right _ _) hn)

theorem threshold_index_le_eventually (threshold : ℕ → ℕ) :
    ∀ᶠ n in atTop, threshold (index threshold n) ≤ n := by
  filter_upwards [eventually_ge_atTop (threshold 0)] with n hn
  exact Nat.findGreatest_spec (P := fun m ↦ threshold m ≤ n) (Nat.zero_le n) hn

/-- No uniformity in the truncation parameter is assumed.  The thresholds
are constructed from the separately proved eventual requirements. -/
theorem exists_monotone_diagonal (P : ℕ → ℕ → Prop)
    (hP : ∀ m, ∀ᶠ n in atTop, P m n) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      (∀ n, level n ≤ n) ∧ (∀ᶠ n in atTop, P (level n) n) := by
  have hN : ∀ m, ∃ N : ℕ, ∀ n ≥ N, P m n := by
    intro m
    exact eventually_atTop.1 (hP m)
  choose threshold hthreshold using hN
  refine ⟨index threshold, index_monotone threshold, index_tendsto_atTop threshold,
    index_le threshold, ?_⟩
  filter_upwards [threshold_index_le_eventually threshold] with n hn
  exact hthreshold (index threshold n) n hn

end PerronWright.SlowGrowingIndex
