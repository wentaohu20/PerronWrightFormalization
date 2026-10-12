import PerronWright.Probability.CountableTypeRealization

/-! # A single actual positive realization with countably many refinements

This is a selection theorem, not a graph-limit assertion. Separately
proved eventual requirements at each fixed support can be imposed on
the same positive integer-count realization. No uniform threshold in
the support parameter is required. Every fixed refinement eventually
holds along the constructed growing support.
-/

open Filter Topology MeasureTheory
open scoped BigOperators Classical
noncomputable section

namespace PerronWright.GrowingTypeCounts

theorem exists_positive_growing_realization_refined (w : ℕ → ℝ)
    (hw : ∀ a, 0 < w a) (hs : HasSum w 1)
    (Q : ℕ → ℕ → ℕ → Prop) (hQ : ∀ m j, ∀ᶠ n in atTop, Q m j n) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      (∀ n, level n ≤ n) ∧
      (∀ n, ∑ a, truncatedCounts w (level n) n a = n) ∧
      (∀ n > 0, ∀ a, 0 < truncatedCounts w (level n) n a) ∧
      (∀ᶠ n in atTop, requirements w (level n) n) ∧
      Tendsto (fun n : ℕ ↦ ∑' a : ℕ, |extendedLaw w (level n) n a - w a|)
        atTop (𝓝 0) ∧
      (∀ B : ℝ, ∀ᶠ n : ℕ in atTop, ∀ a,
        B ≤ (n : ℝ) ^ (1 / 3 : ℝ) * empiricalLaw w (level n) n a) ∧
      (∀ᶠ n in atTop, ∀ j ≤ level n, Q (level n) j n) ∧
      (∀ j, ∀ᶠ n in atTop, Q (level n) j n) := by
  have htail : ∀ m, ∀ᶠ n in atTop, requirements w m n ∧ ∀ j ≤ m, Q m j n := by
    intro m
    have ht := (eventually_all_finset (Finset.range (m + 1))).mpr (fun j _ ↦ hQ m j)
    filter_upwards [requirements_eventually w hw m, ht] with n hn hqn
    exact ⟨hn, fun j hj ↦ hqn j (Finset.mem_range.mpr (by omega))⟩
  have hN : ∀ m, ∃ N : ℕ, ∀ n ≥ N, requirements w m n ∧ ∀ j ≤ m, Q m j n :=
    fun m ↦ eventually_atTop.mp (htail m)
  choose threshold hthreshold using hN
  let level := SlowGrowingIndex.index threshold
  have hm : Monotone level := SlowGrowingIndex.index_monotone threshold
  have ht : Tendsto level atTop atTop := SlowGrowingIndex.index_tendsto_atTop threshold
  have hpq : ∀ᶠ n in atTop, requirements w (level n) n ∧ ∀ j ≤ level n, Q (level n) j n := by
    filter_upwards [SlowGrowingIndex.threshold_index_le_eventually threshold] with n hn
    exact hthreshold (level n) n hn
  have hp : ∀ᶠ n in atTop, requirements w (level n) n := hpq.mono (fun _ h ↦ h.1)
  refine ⟨level, hm, ht, SlowGrowingIndex.index_le threshold,
    fun n ↦ sum_truncatedCounts w hw (level n) n, ?_, hp,
    growing_full_error_tendsto w hw hs level ht hp,
    growing_scaled_minimum w level ht hp, hpq.mono (fun _ h ↦ h.2), ?_⟩
  · intro n hn
    by_cases hl : level n = 0
    · have he {m : ℕ} (h : m = 0) (a : Fin (m + 1)) : truncatedCounts w m n a = n := by
        subst m
        exact truncatedCounts_zero w hw n a
      intro a
      rw [he hl a]
      exact hn
    · have hle : threshold (level n) ≤ n :=
        Nat.findGreatest_of_ne_zero (P := fun m ↦ threshold m ≤ n) rfl hl
      exact (hthreshold (level n) n hle).1.1
  · intro j
    filter_upwards [hpq, ht.eventually (eventually_ge_atTop j)] with n hn hj
    exact hn.2 j hj

end PerronWright.GrowingTypeCounts

namespace PerronWright.CountableTypeRealization

theorem exists_positive_empirical_realization_refined (M : CountableKernel)
    (Q : ℕ → ℕ → ℕ → Prop) (hQ : ∀ m j, ∀ᶠ n in atTop, Q m j n) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      (∀ n, level n ≤ n) ∧
      (∀ n, ∑ a, GrowingTypeCounts.truncatedCounts (weights M) (level n) n a = n) ∧
      (∀ n > 0, ∀ a, 0 < GrowingTypeCounts.truncatedCounts (weights M) (level n) n a) ∧
      (∀ n > 0, IsProbabilityMeasure (empiricalMeasure M (level n) n)) ∧
      Tendsto (fun n : ℕ ↦ ∑' a : ℕ,
        |(empiricalMeasure M (level n) n).real {a} - M.mu.real {a}|) atTop (𝓝 0) ∧
      (∀ B : ℝ, ∀ᶠ n : ℕ in atTop, ∀ a : Fin (level n + 1),
        B ≤ (n : ℝ) ^ (1 / 3 : ℝ) * (empiricalMeasure M (level n) n).real {a.val}) ∧
      (∀ᶠ n in atTop, ∀ j ≤ level n, Q (level n) j n) ∧
      (∀ j, ∀ᶠ n in atTop, Q (level n) j n) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hp, _, hmin, hdiag, hfixed⟩ :=
    GrowingTypeCounts.exists_positive_growing_realization_refined
      (weights M) M.atomMass_pos M.atomMass_hasSum Q hQ
  refine ⟨level, hm, ht, hle, hc, hpos,
    fun n hn ↦ empiricalMeasure_isProbability M (level n) hn,
    empiricalMeasure_error_tendsto M level ht hp, ?_, hdiag, hfixed⟩
  intro B
  filter_upwards [hmin B] with n hn
  intro a
  rw [empiricalMeasure_atom, GrowingTypeCounts.extendedLaw_fin]
  exact hn a

end PerronWright.CountableTypeRealization
