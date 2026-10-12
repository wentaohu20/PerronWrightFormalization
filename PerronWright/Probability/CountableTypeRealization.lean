import PerronWright.Model.CountableKernel
import PerronWright.Probability.GrowingTypeApproximation
import PerronWright.Probability.GrowingTypePositive
import PerronWright.Probability.EmpiricalTypeMarks

/-!
# Actual deterministic countable-type vertex assignments

The growing-support count construction is linked to the given atomic
probability measure and to actual vertices.  Its empirical law is the
literal finite sum of Dirac measures.  This proves the realization
foundations only, not the countable graph limit theorem.
-/

open Filter Topology MeasureTheory
open scoped BigOperators Classical ENNReal

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableTypeRealization

open GrowingTypeCounts

def weights (M : CountableKernel) (a : ℕ) : ℝ := M.mu.real {a}

def vertexTypes (M : CountableKernel) (m n : ℕ) (v : Fin n) : ℕ :=
  (IntegerTypeAssignment.roundedTypeVector 0 (truncatedLaw (weights M) m)
    (fun a ↦ (truncatedLaw_pos (weights M) M.atomMass_pos m a).le)
    (sum_truncatedLaw (weights M) M.atomMass_pos m) n v).val

theorem vertexTypes_lt (M : CountableKernel) (m n : ℕ) (v : Fin n) :
    vertexTypes M m n v < m + 1 :=
  (IntegerTypeAssignment.roundedTypeVector 0 (truncatedLaw (weights M) m)
    (fun a ↦ (truncatedLaw_pos (weights M) M.atomMass_pos m a).le)
    (sum_truncatedLaw (weights M) M.atomMass_pos m) n v).isLt

theorem fiber_card (M : CountableKernel) (m n a : ℕ) :
    Fintype.card {v : Fin n // vertexTypes M m n v = a} =
      if h : a < m + 1 then truncatedCounts (weights M) m n ⟨a, h⟩ else 0 := by
  let x := IntegerTypeAssignment.roundedTypeVector 0 (truncatedLaw (weights M) m)
    (fun a ↦ (truncatedLaw_pos (weights M) M.atomMass_pos m a).le)
    (sum_truncatedLaw (weights M) M.atomMass_pos m) n
  by_cases ha : a < m + 1
  · rw [dif_pos ha]
    have he : ∀ v : Fin n, vertexTypes M m n v = a ↔ x v = ⟨a, ha⟩ := by
      intro v
      change (x v).val = a ↔ x v = (⟨a, ha⟩ : Fin (m + 1))
      exact ⟨fun h ↦ Fin.ext h, fun h ↦ congrArg Fin.val h⟩
    have hc := Fintype.card_congr (Equiv.subtypeEquivRight he)
    rw [hc]
    simpa only [← Nat.card_eq_fintype_card, x, truncatedCounts] using
      IntegerTypeAssignment.roundedTypeVector_fiber_card
      (0 : Fin (m + 1)) (truncatedLaw (weights M) m)
      (fun a ↦ (truncatedLaw_pos (weights M) M.atomMass_pos m a).le)
      (sum_truncatedLaw (weights M) M.atomMass_pos m) n ⟨a, ha⟩
  · rw [dif_neg ha]
    have hi : IsEmpty {v : Fin n // vertexTypes M m n v = a} :=
      ⟨fun v ↦ ha (v.property ▸ vertexTypes_lt M m n v.val)⟩
    exact Fintype.card_eq_zero

def empiricalMeasure (M : CountableKernel) (m n : ℕ) : Measure ℕ :=
  EmpiricalTypeMarks.empiricalMeasure (vertexTypes M m n) Finset.univ

theorem empiricalMeasure_isProbability (M : CountableKernel) (m : ℕ)
    {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (empiricalMeasure M m n) := by
  apply EmpiricalTypeMarks.empiricalMeasure_isProbability
  exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem empiricalMeasure_atom (M : CountableKernel) (m n a : ℕ) :
    (empiricalMeasure M m n).real {a} = extendedLaw (weights M) m n a := by
  have hc : (∑ v : Fin n, (Measure.dirac (vertexTypes M m n v)) {a}) =
      (Fintype.card {v : Fin n // vertexTypes M m n v = a} : ℝ≥0∞) := by
    simp only [Measure.dirac_apply' _ (measurableSet_singleton a), Set.mem_singleton_iff,
      Set.indicator_apply, Pi.one_apply, Fintype.card_subtype, Finset.sum_boole]
  unfold empiricalMeasure EmpiricalTypeMarks.empiricalMeasure
  simp only [Measure.real, Measure.smul_apply, Measure.finsetSum_apply, Finset.card_univ,
    Fintype.card_fin, hc, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  rw [fiber_card]
  unfold extendedLaw empiricalLaw FiniteTypeCounts.empiricalLaw
  split_ifs
  · simp only [truncatedCounts, div_eq_mul_inv]
    ring
  · simp

/-- The empirical probability measures of actual vertex assignments
converge in full atomic total absolute variation. -/
theorem empiricalMeasure_error_tendsto (M : CountableKernel) (level : ℕ → ℕ)
    (ht : Tendsto level atTop atTop)
    (hp : ∀ᶠ n in atTop, requirements (weights M) (level n) n) :
    Tendsto (fun n : ℕ ↦ ∑' a : ℕ,
      |(empiricalMeasure M (level n) n).real {a} - M.mu.real {a}|)
      atTop (nhds 0) := by
  simp_rw [empiricalMeasure_atom]
  exact growing_full_error_tendsto (weights M) M.atomMass_pos M.atomMass_hasSum level ht hp

theorem exists_empirical_realization (M : CountableKernel) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      (∀ n, ∑ a, truncatedCounts (weights M) (level n) n a = n) ∧
      (∀ᶠ n in atTop, requirements (weights M) (level n) n) ∧
      Tendsto (fun n : ℕ ↦ ∑' a : ℕ,
        |(empiricalMeasure M (level n) n).real {a} - M.mu.real {a}|) atTop (nhds 0) := by
  obtain ⟨level, hm, ht, hc, hp⟩ := exists_growing_counts (weights M) M.atomMass_pos
  exact ⟨level, hm, ht, hc, hp, empiricalMeasure_error_tendsto M level ht hp⟩

/-- The complete integer-support construction before any spectral or
graph-limit assertion.  The empirical measures are genuine probability
measures for every positive vertex count, and all retained type counts
are then strictly positive. -/
theorem exists_positive_empirical_realization (M : CountableKernel) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      (∀ n, ∑ a, truncatedCounts (weights M) (level n) n a = n) ∧
      (∀ n > 0, ∀ a, 0 < truncatedCounts (weights M) (level n) n a) ∧
      (∀ n > 0, IsProbabilityMeasure (empiricalMeasure M (level n) n)) ∧
      Tendsto (fun n : ℕ ↦ ∑' a : ℕ,
        |(empiricalMeasure M (level n) n).real {a} - M.mu.real {a}|) atTop (nhds 0) ∧
      (∀ B : ℝ, ∀ᶠ n : ℕ in atTop, ∀ a : Fin (level n + 1),
        B ≤ (n : ℝ) ^ (1 / 3 : ℝ) * (empiricalMeasure M (level n) n).real {a.val}) := by
  obtain ⟨level, hm, ht, hc, hpos, hp, _, hmin⟩ :=
    exists_positive_growing_realization (weights M) M.atomMass_pos M.atomMass_hasSum
  refine ⟨level, hm, ht, hc, hpos,
    fun n hn ↦ empiricalMeasure_isProbability M (level n) hn,
    empiricalMeasure_error_tendsto M level ht hp, ?_⟩
  intro B
  filter_upwards [hmin B] with n hn
  intro a
  rw [empiricalMeasure_atom, extendedLaw_fin]
  exact hn a

end PerronWright.CountableTypeRealization
