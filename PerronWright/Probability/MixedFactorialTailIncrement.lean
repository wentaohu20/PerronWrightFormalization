import PerronWright.Probability.MixedFactorialTail
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Mixed next-order tails and integrability of actual atomic limits

Incrementing one mixed order at a time provides tail control directly
from the mixed moments. No uniform generating-series bound is needed.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.MixedFactorialTailIncrement

open FactorialCountDeterminacy FactorialGeneratingSeries MixedFactorialTail

variable {ι : Type*} [Fintype ι]

def increment (q : ι → ℕ) (i : ι) : ι → ℕ := by
  classical
  exact Function.update q i (q i + 1)

theorem descFactorial_real_succ (n q : ℕ) :
    (n.descFactorial (q + 1) : ℝ) = ((n : ℝ) - q) * (n.descFactorial q : ℝ) := by
  by_cases hq : q ≤ n
  · rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hq]
  · have hz := Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hq)
    simp [Nat.descFactorial_succ, hz]

theorem factorialPolynomial_increment (q n : ι → ℕ) (i : ι) :
    factorialPolynomial (increment q i) n = ((n i : ℝ) - q i) * factorialPolynomial q n := by
  classical
  unfold factorialPolynomial
  rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ ((n j).descFactorial (increment q i j) : ℝ))
    (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ ((n j).descFactorial (q j) : ℝ))
    (Finset.mem_univ i)]
  have hi : increment q i i = q i + 1 := by simp [increment]
  have ho : (∏ j ∈ Finset.univ.erase i, ((n j).descFactorial (increment q i j) : ℝ)) =
      ∏ j ∈ Finset.univ.erase i, ((n j).descFactorial (q j) : ℝ) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [increment, (Finset.mem_erase.mp hj).1]
  rw [hi, ho, descFactorial_real_succ]
  ring

theorem sum_increment_polynomials (q n : ι → ℕ) :
    (∑ i, factorialPolynomial (increment q i) n) =
      ((totalCount n : ℝ) - (∑ i, q i : ℕ)) * factorialPolynomial q n := by
  simp_rw [factorialPolynomial_increment]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum]
  rfl

theorem mixed_count_tail_le_next_mixed (μ : Measure (ι → ℕ)) (q : ι → ℕ)
    (H : ℕ) (hH : (∑ i, q i) < H)
    (hint : Integrable (factorialPolynomial q) μ)
    (hintnext : ∀ i, Integrable (factorialPolynomial (increment q i)) μ) :
    (∫ n, {n | H < totalCount n}.indicator (factorialPolynomial q) n ∂μ) ≤
      (∑ i, factorialMoment μ (increment q i)) / ((H : ℝ) - (∑ i, q i : ℕ)) := by
  have hs : MeasurableSet {n : ι → ℕ | H < totalCount n} := (Set.to_countable _).measurableSet
  have hd : 0 < (H : ℝ) - (∑ i, q i : ℕ) := sub_pos.mpr (by exact_mod_cast hH)
  have hi : Integrable (fun n ↦ ∑ i, factorialPolynomial (increment q i) n) μ :=
    integrable_finsetSum _ (fun i _ ↦ hintnext i)
  have he : (∫ n, {n | H < totalCount n}.indicator (factorialPolynomial q) n ∂μ) ≤
      ∫ n, (∑ i, factorialPolynomial (increment q i) n) /
        ((H : ℝ) - (∑ i, q i : ℕ)) ∂μ := by
    apply integral_mono (hint.indicator hs) (hi.div_const _)
    intro n
    by_cases hn : H < totalCount n
    · rw [Set.indicator_of_mem (show n ∈ {n | H < totalCount n} from hn)]
      apply (le_div_iff₀ hd).mpr
      rw [sum_increment_polynomials]
      have hc : (H : ℝ) ≤ (totalCount n : ℝ) := by exact_mod_cast hn.le
      have hp := mul_le_mul_of_nonneg_right (sub_le_sub_right hc (∑ i, q i : ℕ))
        (factorialPolynomial_nonneg q n)
      simpa only [mul_comm] using hp
    · rw [Set.indicator_of_notMem (show n ∉ {n | H < totalCount n} from hn)]
      exact div_nonneg (Finset.sum_nonneg (fun i _ ↦ factorialPolynomial_nonneg _ _)) hd.le
  rw [integral_div, integral_finsetSum Finset.univ (fun i _ ↦ hintnext i)] at he
  exact he

theorem mixed_finite_truncation_error_le_next_mixed (μ : Measure (ι → ℕ)) (q : ι → ℕ)
    (H : ℕ) (hH : (∑ i, q i) < H)
    (hint : Integrable (factorialPolynomial q) μ)
    (hintnext : ∀ i, Integrable (factorialPolynomial (increment q i)) μ) :
    0 ≤ factorialMoment μ q - ∑ n ∈ countTruncation H, μ.real {n} * factorialPolynomial q n ∧
    factorialMoment μ q - ∑ n ∈ countTruncation H, μ.real {n} * factorialPolynomial q n ≤
      (∑ i, factorialMoment μ (increment q i)) / ((H : ℝ) - (∑ i, q i : ℕ)) := by
  have hs : MeasurableSet (countTruncation (ι := ι) H : Set (ι → ℕ)) :=
    (countTruncation H).measurableSet
  have hf := setIntegral_finset (μ := μ) (countTruncation H) hint.integrableOn
  simp only [smul_eq_mul] at hf
  have he : factorialMoment μ q - ∑ n ∈ countTruncation H, μ.real {n} * factorialPolynomial q n =
      ∫ n, {n | H < totalCount n}.indicator (factorialPolynomial q) n ∂μ := by
    rw [factorialMoment, ← hf, ← setIntegral_compl hs hint, countTruncation_compl,
      ← integral_indicator ((Set.to_countable _).measurableSet)]
  rw [he]
  exact ⟨integral_nonneg (fun n ↦ Set.indicator_nonneg (fun _ _ ↦ factorialPolynomial_nonneg q _) n),
    mixed_count_tail_le_next_mixed μ q H hH hint hintnext⟩

/-- Atomic limit probabilities and a genuine uniform observable moment
bound imply integrability of that observable under the actual limit
measure, with the same bound. This is the discrete Fatou step. -/
theorem integrable_limit_of_atom_tendsto_nonneg
    (μ : ℕ → ProbabilityMeasure (ι → ℕ)) (ν : ProbabilityMeasure (ι → ℕ))
    (f : (ι → ℕ) → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hint : ∀ j, Integrable f (μ j : Measure (ι → ℕ))) (M : ℝ)
    (hb : ∀ j, (∫ n, f n ∂(μ j : Measure (ι → ℕ))) ≤ M)
    (hatom : ∀ n, Tendsto (fun j ↦ (μ j : Measure (ι → ℕ)).real {n}) atTop
      (𝓝 ((ν : Measure (ι → ℕ)).real {n}))) :
    Integrable f (ν : Measure (ι → ℕ)) ∧ (∫ n, f n ∂(ν : Measure (ι → ℕ))) ≤ M := by
  have hfinite (F : Finset (ι → ℕ)) : ∑ n ∈ F, (ν : Measure (ι → ℕ)).real {n} * f n ≤ M := by
    have ht := tendsto_finsetSum F (fun n _ ↦ (hatom n).mul_const (f n))
    apply le_of_tendsto ht
    exact Eventually.of_forall (fun j ↦ by
      have hs := setIntegral_finset (μ := (μ j : Measure (ι → ℕ))) F (hint j).integrableOn
      simp only [smul_eq_mul] at hs
      rw [← hs]
      exact (setIntegral_le_integral (hint j) (Eventually.of_forall hf)).trans (hb j))
  have hsum : Summable (fun n ↦ (ν : Measure (ι → ℕ)).real {n} * f n) :=
    summable_of_sum_le (fun n ↦ mul_nonneg measureReal_nonneg (hf n)) hfinite
  have hνint : Integrable f (ν : Measure (ι → ℕ)) := by
    rw [← Measure.sum_smul_dirac (ν : Measure (ι → ℕ))]
    apply integrable_sum_dirac (fun n ↦ measure_ne_top (ν : Measure (ι → ℕ)) {n})
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _), measureReal_def] using hsum
  refine ⟨hνint, ?_⟩
  rw [integral_countable hνint]
  simp only [smul_eq_mul]
  exact hsum.tsum_le_of_sum_le hfinite

end PerronWright.MixedFactorialTailIncrement
