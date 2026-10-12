import PerronWright.Analysis.SlowGrowingIndex
import PerronWright.Probability.IntegerTypeAssignment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Constructed slow-growing countable type supports and integer counts

Every truncation is the actual initial segment of a positive summable
type law, normalized by its own mass.  The support level is selected by
the proved diagonal lemma.  In particular the population-size minimum
condition is proved, not supplied as a realization interface.
-/

open Filter Topology
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.GrowingTypeCounts

def mass (w : ℕ → ℝ) (m : ℕ) : ℝ := ∑ a : Fin (m + 1), w a

theorem mass_pos (w : ℕ → ℝ) (hw : ∀ a, 0 < w a) (m : ℕ) : 0 < mass w m := by
  apply Finset.sum_pos
  · intro a _
    exact hw a
  · exact Finset.univ_nonempty

theorem mass_eq_sum_range (w : ℕ → ℝ) (m : ℕ) :
    mass w m = ∑ a ∈ Finset.range (m + 1), w a := by
  exact Fin.sum_univ_eq_sum_range w (m + 1)

theorem mass_le_one (w : ℕ → ℝ) (hw : ∀ a, 0 < w a)
    (hs : HasSum w 1) (m : ℕ) : mass w m ≤ 1 := by
  rw [mass_eq_sum_range, ← hs.tsum_eq]
  exact hs.summable.sum_le_tsum (Finset.range (m + 1)) (fun a _ ↦ (hw a).le)

theorem mass_tendsto_one (w : ℕ → ℝ) (hs : HasSum w 1) :
    Tendsto (mass w) atTop (nhds 1) := by
  simpa only [Function.comp_def, ← mass_eq_sum_range] using
    hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- The genuine normalized truncated law on the finite support. -/
def truncatedLaw (w : ℕ → ℝ) (m : ℕ) (a : Fin (m + 1)) : ℝ := w a / mass w m

theorem truncatedLaw_pos (w : ℕ → ℝ) (hw : ∀ a, 0 < w a)
    (m : ℕ) (a : Fin (m + 1)) : 0 < truncatedLaw w m a :=
  div_pos (hw a) (mass_pos w hw m)

theorem sum_truncatedLaw (w : ℕ → ℝ) (hw : ∀ a, 0 < w a) (m : ℕ) :
    ∑ a, truncatedLaw w m a = 1 := by
  simp only [truncatedLaw, ← Finset.sum_div]
  exact div_self (mass_pos w hw m).ne'

def truncatedCounts (w : ℕ → ℝ) (m n : ℕ) : Fin (m + 1) → ℕ :=
  FiniteTypeCounts.counts 0 (truncatedLaw w m) n

def empiricalLaw (w : ℕ → ℝ) (m n : ℕ) : Fin (m + 1) → ℝ :=
  FiniteTypeCounts.empiricalLaw 0 (truncatedLaw w m) n

theorem sum_truncatedCounts (w : ℕ → ℝ) (hw : ∀ a, 0 < w a) (m n : ℕ) :
    ∑ a, truncatedCounts w m n a = n :=
  FiniteTypeCounts.sum_counts 0 (truncatedLaw w m)
    (fun a ↦ (truncatedLaw_pos w hw m a).le) (sum_truncatedLaw w hw m) n

theorem empiricalLaw_ge_half_eventually (w : ℕ → ℝ) (hw : ∀ a, 0 < w a)
    (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ a, truncatedLaw w m a / 2 ≤ empiricalLaw w m n a := by
  apply eventually_all.mpr
  intro a
  have hp := truncatedLaw_pos w hw m a
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) * truncatedLaw w m a) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hp
  filter_upwards [ht.eventually_ge_atTop 2, eventually_ge_atTop 1] with n hn hn1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hf := Nat.lt_floor_add_one ((n : ℝ) * truncatedLaw w m a)
  have hc : (⌊(n : ℝ) * truncatedLaw w m a⌋₊ : ℝ) ≤
      (truncatedCounts w m n a : ℝ) := by
    exact_mod_cast FiniteTypeCounts.floorCounts_le_counts 0 (truncatedLaw w m) n a
  change truncatedLaw w m a / 2 ≤ (truncatedCounts w m n a : ℝ) / (n : ℝ)
  apply (le_div_iff₀ hnR).2
  nlinarith

/-- Every fixed finite truncation eventually satisfies the actual
population minimum requirement at the critical scale. -/
theorem scaled_empirical_minimum_eventually (w : ℕ → ℝ) (hw : ∀ a, 0 < w a)
    (m : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ a,
      B ≤ (n : ℝ) ^ (1 / 3 : ℝ) * empiricalLaw w m n a := by
  have hg : ∀ᶠ n : ℕ in atTop, ∀ a,
      B ≤ (n : ℝ) ^ (1 / 3 : ℝ) * (truncatedLaw w m a / 2) := by
    apply eventually_all.mpr
    intro a
    have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) *
        (truncatedLaw w m a / 2)) atTop atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
        tendsto_natCast_atTop_atTop).atTop_mul_const
          (div_pos (truncatedLaw_pos w hw m a) (by norm_num))
    exact ht.eventually_ge_atTop B
  filter_upwards [hg, empiricalLaw_ge_half_eventually w hw m] with n hn he
  intro a
  exact (hn a).trans (mul_le_mul_of_nonneg_left (he a)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _))

def requirements (w : ℕ → ℝ) (m n : ℕ) : Prop :=
  (∀ a, 0 < truncatedCounts w m n a) ∧
  (∑ a, |empiricalLaw w m n a - truncatedLaw w m a|) ≤ 1 / (m + 1 : ℝ) ∧
  (∀ a, (m : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) * empiricalLaw w m n a)

theorem requirements_eventually (w : ℕ → ℝ) (hw : ∀ a, 0 < w a) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, requirements w m n := by
  have he := FiniteTypeCounts.empirical_error_tendsto_zero 0 (truncatedLaw w m)
    (fun a ↦ (truncatedLaw_pos w hw m a).le) (sum_truncatedLaw w hw m)
  have hbound : ∀ᶠ n in atTop,
      (∑ a, |empiricalLaw w m n a - truncatedLaw w m a|) ≤ 1 / (m + 1 : ℝ) := by
    have hsmall := he.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (m + 1 : ℝ) by positivity))
    filter_upwards [hsmall] with n hn
    exact hn.le
  filter_upwards [FiniteTypeCounts.counts_pos_eventually 0 (truncatedLaw w m)
    (truncatedLaw_pos w hw m), hbound, scaled_empirical_minimum_eventually w hw m m]
    with n hp he hm
  exact ⟨hp, he, hm⟩

/-- The level is monotone and exhaustive.  Each count vector is literal,
has exactly `n` vertices, and eventually satisfies all three quantitative
conditions simultaneously. -/
theorem exists_growing_counts (w : ℕ → ℝ) (hw : ∀ a, 0 < w a) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      (∀ n, ∑ a, truncatedCounts w (level n) n a = n) ∧
      (∀ᶠ n in atTop, requirements w (level n) n) := by
  obtain ⟨level, hmono, ht, _, hp⟩ :=
    SlowGrowingIndex.exists_monotone_diagonal (requirements w) (requirements_eventually w hw)
  exact ⟨level, hmono, ht, fun n ↦ sum_truncatedCounts w hw (level n) n, hp⟩

def support (level : ℕ → ℕ) (n : ℕ) : Finset ℕ := Finset.range (level n + 1)

theorem support_monotone (level : ℕ → ℕ) (hlevel : Monotone level) :
    Monotone (support level) := by
  intro n n' hn
  exact Finset.range_mono (Nat.add_le_add_right (hlevel hn) 1)

theorem support_exhaustive (level : ℕ → ℕ) (ht : Tendsto level atTop atTop) (a : ℕ) :
    ∀ᶠ n in atTop, a ∈ support level n := by
  filter_upwards [ht.eventually_ge_atTop a] with n hn
  exact Finset.mem_range.mpr (by omega)

/-- This is the uniform-over-the-growing-support meaning of the paper's
scaled minimum tending to infinity. -/
theorem growing_scaled_minimum (w : ℕ → ℝ) (level : ℕ → ℕ)
    (ht : Tendsto level atTop atTop)
    (hp : ∀ᶠ n in atTop, requirements w (level n) n) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ a,
      B ≤ (n : ℝ) ^ (1 / 3 : ℝ) * empiricalLaw w (level n) n a := by
  have hc : Tendsto (fun n : ℕ ↦ (level n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ht
  filter_upwards [hc.eventually_ge_atTop B, hp] with n hn hr
  intro a
  exact hn.trans (hr.2.2 a)

end PerronWright.GrowingTypeCounts
