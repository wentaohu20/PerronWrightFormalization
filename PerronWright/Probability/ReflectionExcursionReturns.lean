import PerronWright.Probability.ContinuousPathReflection

/-!
# Cofinal zeros of the actual running-minimum reflection

For a continuous function tending to minus infinity, the reflection formed
from its literal past minimum returns to zero after every time.  The zeros
are obtained at attained minima, not from an assumed excursion interface.
-/

open Filter Topology
open scoped NNReal

noncomputable section

namespace PerronWright.ReflectionExcursionReturns

open ContinuousPathReflection

theorem reflected_zero_of_minimum_attained {f : ℝ≥0 → ℝ}
    (hf : Continuous f) {s t : ℝ≥0} (hst : s ≤ t)
    (he : runningMinimum f t = f s) : reflected f s = 0 := by
  have h₁ := runningMinimum_antitone hf hst
  have h₂ := runningMinimum_le hf (le_rfl : s ≤ s)
  have hm : runningMinimum f s = f s := le_antisymm h₂ (he ▸ h₁)
  simp [reflected, hm]

theorem runningMinimum_eq_on_positive_interval {f : ℝ≥0 → ℝ}
    (hf : Continuous f) {q t : ℝ≥0} (hqt : q ≤ t)
    (hp : ∀ u ∈ Set.Icc q t, 0 < reflected f u) :
    runningMinimum f t = runningMinimum f q := by
  obtain ⟨u, hu, he⟩ := runningMinimum_attained hf t
  have huq : u ≤ q := by
    by_contra h
    have hz := reflected_zero_of_minimum_attained hf hu.2 he
    have hpos := hp u ⟨le_of_lt (lt_of_not_ge h), hu.2⟩
    simp only [hz, lt_self_iff_false] at hpos
  apply le_antisymm (runningMinimum_antitone hf hqt)
  rw [he]
  exact runningMinimum_le hf huq

theorem exists_zero_after_of_lt_minimum {f : ℝ≥0 → ℝ}
    (hf : Continuous f) {q T : ℝ≥0}
    (hT : f T < runningMinimum f q) :
    ∃ u ∈ Set.Ioc q T, reflected f u = 0 := by
  obtain ⟨u, hu, he⟩ := runningMinimum_attained hf T
  have hm := runningMinimum_le hf (le_rfl : T ≤ T)
  have hqu : q < u := by
    by_contra h
    have hle := runningMinimum_le hf (le_of_not_gt h : u ≤ q)
    rw [he] at hm
    linarith
  exact ⟨u, ⟨hqu, hu.2⟩, reflected_zero_of_minimum_attained hf hu.2 he⟩

/-- Genuine cofinal return times for the running-minimum reflection. -/
theorem exists_zero_after {f : ℝ≥0 → ℝ} (hf : Continuous f)
    (hlim : Tendsto f atTop atBot) (q : ℝ≥0) :
    ∃ t : ℝ≥0, q < t ∧ reflected f t = 0 := by
  obtain ⟨T, hT⟩ := (hlim.eventually_lt_atBot (runningMinimum f q)).exists
  obtain ⟨t, ht, hz⟩ := exists_zero_after_of_lt_minimum hf hT
  exact ⟨t, ht.1, hz⟩

theorem zero_set_unbounded {f : ℝ≥0 → ℝ} (hf : Continuous f)
    (hlim : Tendsto f atTop atBot) :
    ¬ BddAbove {t : ℝ≥0 | reflected f t = 0} := by
  rintro ⟨q, hq⟩
  obtain ⟨t, hqt, ht⟩ := exists_zero_after hf hlim q
  exact (not_le_of_gt hqt) (hq ht)

end PerronWright.ReflectionExcursionReturns
