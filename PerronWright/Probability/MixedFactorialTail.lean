import PerronWright.Probability.FactorialGeneratingSeries
import PerronWright.Probability.FactorialTailBounds
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Actual mixed factorial tails and finite count truncations

The domination of mixed factorial products by the falling factorial of
the total count is proved combinatorially. Actual next total factorial
moments then control tails under changing count-vector laws.
-/

open MeasureTheory Filter
open scoped Classical BigOperators

noncomputable section

set_option maxHeartbeats 800000

namespace PerronWright.MixedFactorialTail

open FactorialCountDeterminacy FactorialGeneratingSeries FactorialTailBounds

/-- Choosing ordered distinct objects in separate classes is bounded
by choosing them in the union, including the zero-factor cases. -/
theorem descFactorial_mul_le (n m q r : ℕ) :
    n.descFactorial q * m.descFactorial r ≤ (n + m).descFactorial (q + r) := by
  by_cases hq : q ≤ n
  · have hfirst := Nat.descFactorial_le q (Nat.le_add_right n m)
    have hsecond := Nat.descFactorial_le r (show m ≤ n + m - q by omega)
    calc
      _ ≤ (n + m).descFactorial q * (n + m - q).descFactorial r := Nat.mul_le_mul hfirst hsecond
      _ = _ := by
        simpa only [Nat.add_sub_cancel_left, Nat.mul_comm] using
          (Nat.descFactorial_mul_descFactorial (n := n + m) (k := q) (m := q + r)
            (Nat.le_add_right q r))
  · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hq), zero_mul,
      Nat.zero_le]

theorem prod_descFactorial_le {ι : Type*} (F : Finset ι) (n q : ι → ℕ) :
    (∏ i ∈ F, (n i).descFactorial (q i)) ≤
      (∑ i ∈ F, n i).descFactorial (∑ i ∈ F, q i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (Nat.mul_le_mul_left ((n i).descFactorial (q i)) ih).trans
      (descFactorial_mul_le (n i) (∑ j ∈ F, n j) (q i) (∑ j ∈ F, q j))

variable {ι : Type*} [Fintype ι]

theorem factorialPolynomial_nonneg (q n : ι → ℕ) : 0 ≤ factorialPolynomial q n :=
  Finset.prod_nonneg (fun _ _ ↦ Nat.cast_nonneg _)

/-- Literal mixed factorial products are dominated by the total
falling factorial of exactly the same total order. -/
theorem factorialPolynomial_le_total (q n : ι → ℕ) :
    factorialPolynomial q n ≤ ((totalCount n).descFactorial (∑ i, q i) : ℝ) := by
  unfold factorialPolynomial totalCount
  rw [← Nat.cast_prod]
  exact_mod_cast prod_descFactorial_le Finset.univ n q

theorem factorialPolynomial_integrable_of_total (μ : Measure (ι → ℕ)) (q : ι → ℕ)
    (hint : Integrable (fun n ↦ ((totalCount n).descFactorial (∑ i, q i) : ℝ)) μ) :
    Integrable (factorialPolynomial q) μ :=
  hint.mono_nonneg (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall (factorialPolynomial_nonneg q))
    (Eventually.of_forall (factorialPolynomial_le_total q))

/-- Tail error of the actual mixed moment when the total count is
truncated at `H`, controlled by the next actual total factorial moment. -/
theorem integral_mixed_count_tail_le (μ : Measure (ι → ℕ)) (q : ι → ℕ)
    (H : ℕ) (hH : (∑ i, q i) < H)
    (hint : Integrable (fun n ↦ ((totalCount n).descFactorial (∑ i, q i) : ℝ)) μ)
    (hintnext : Integrable (fun n ↦ ((totalCount n).descFactorial ((∑ i, q i) + 1) : ℝ)) μ) :
    (∫ n, {n | H < totalCount n}.indicator (factorialPolynomial q) n ∂μ) ≤
      (∫ n, ((totalCount n).descFactorial ((∑ i, q i) + 1) : ℝ) ∂μ) /
        ((H : ℝ) - (∑ i, q i : ℕ)) := by
  have hset : MeasurableSet {n : ι → ℕ | H < totalCount n} := (Set.to_countable _).measurableSet
  have hpi := factorialPolynomial_integrable_of_total μ q hint
  have hd : 0 < (H : ℝ) - (∑ i, q i : ℕ) := sub_pos.mpr (by exact_mod_cast hH)
  rw [← integral_div]
  apply integral_mono (hpi.indicator hset) (hintnext.div_const _)
  intro n
  by_cases hn : H < totalCount n
  · rw [Set.indicator_of_mem (show n ∈ {n | H < totalCount n} from hn)]
    exact (factorialPolynomial_le_total q n).trans (factorial_le_next_div hH hn)
  · rw [Set.indicator_of_notMem (show n ∉ {n | H < totalCount n} from hn)]
    positivity

/-- Genuine uniform tail control across changing count-vector laws;
only actual total factorial-moment integrability and its next-order
uniform bound are required. -/
theorem exists_uniform_mixed_count_tail_cutoff {J : Type*}
    (μ : J → Measure (ι → ℕ)) (q : ι → ℕ)
    (hint : ∀ j, Integrable (fun n ↦ ((totalCount n).descFactorial (∑ i, q i) : ℝ)) (μ j))
    (hintnext : ∀ j, Integrable (fun n ↦ ((totalCount n).descFactorial ((∑ i, q i) + 1) : ℝ)) (μ j))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, (∫ n, ((totalCount n).descFactorial ((∑ i, q i) + 1) : ℝ) ∂μ j) ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, (∑ i, q i) < H ∧ ∀ j,
      (∫ n, {n | H < totalCount n}.indicator (factorialPolynomial q) n ∂μ j) < ε := by
  obtain ⟨H, hH⟩ := exists_nat_gt ((∑ i, q i : ℕ) + M / ε : ℝ)
  have hd0 : (∑ i, q i : ℕ) < (H : ℝ) := by
    have hmε : 0 ≤ M / ε := div_nonneg hM hε.le
    linarith
  have hqH : (∑ i, q i) < H := by exact_mod_cast hd0
  have hd : 0 < (H : ℝ) - (∑ i, q i : ℕ) := sub_pos.mpr hd0
  have hcut : M / ((H : ℝ) - (∑ i, q i : ℕ)) < ε := by
    apply (div_lt_iff₀ hd).mpr
    have hmul := (div_lt_iff₀ hε).mp (show M / ε < (H : ℝ) - (∑ i, q i : ℕ) by linarith)
    nlinarith
  refine ⟨H, hqH, fun j ↦ ?_⟩
  exact (integral_mixed_count_tail_le (μ j) q H hqH (hint j) (hintnext j)).trans_lt
    ((div_le_div_of_nonneg_right (hbound j) hd.le).trans_lt hcut)

/-- Uniform integrability in its literal tail-integral form, valid
even though the probability laws themselves vary with the index. -/
theorem exists_uniform_mixed_observable_tail_cutoff {J : Type*}
    (μ : J → Measure (ι → ℕ)) (q : ι → ℕ)
    (hint : ∀ j, Integrable (fun n ↦ ((totalCount n).descFactorial (∑ i, q i) : ℝ)) (μ j))
    (hintnext : ∀ j, Integrable (fun n ↦ ((totalCount n).descFactorial ((∑ i, q i) + 1) : ℝ)) (μ j))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, (∫ n, ((totalCount n).descFactorial ((∑ i, q i) + 1) : ℝ) ∂μ j) ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j,
      (∫ n, {n | A < |factorialPolynomial q n|}.indicator
        (fun n ↦ |factorialPolynomial q n|) n ∂μ j) < ε := by
  obtain ⟨H, _hH, hb⟩ := exists_uniform_observable_tail_cutoff
    μ (fun _ ↦ totalCount) (fun _ ↦ factorialPolynomial q) (∑ i, q i)
    (fun _ ↦ measurable_of_countable _) (fun _ ↦ factorialPolynomial_nonneg q)
    (fun _ ↦ factorialPolynomial_le_total q) hint hintnext M hM hbound ε hε
  refine ⟨(H.descFactorial (∑ i, q i) : ℝ), Nat.cast_nonneg _, ?_⟩
  simpa only [abs_of_nonneg (factorialPolynomial_nonneg q _)] using hb

/-- A genuine finite state cutoff, containing exactly the count vectors
whose total count is at most `H`. -/
def countTruncation (H : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset (fun _ : ι ↦ Finset.range (H + 1))).filter (fun n ↦ totalCount n ≤ H)

theorem mem_countTruncation (H : ℕ) (n : ι → ℕ) :
    n ∈ countTruncation H ↔ totalCount n ≤ H := by
  classical
  simp only [countTruncation, Finset.mem_filter]
  refine ⟨And.right, fun hn ↦ ⟨?_, hn⟩⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_range.mpr
  have hi : n i ≤ totalCount n :=
    Finset.single_le_sum (fun j _ ↦ Nat.zero_le (n j)) (Finset.mem_univ i)
  omega

theorem countTruncation_compl (H : ℕ) :
    (countTruncation (ι := ι) H : Set (ι → ℕ))ᶜ = {n | H < totalCount n} := by
  ext n
  simp only [Set.mem_compl_iff, Finset.mem_coe, mem_countTruncation, Set.mem_ofPred_eq, not_le]

/-- Finite truncation of a mixed moment is the literal finite sum of
its polynomial values times the actual atom probabilities. -/
theorem mixed_moment_finite_truncation_error (μ : Measure (ι → ℕ)) (q : ι → ℕ)
    (H : ℕ) (hH : (∑ i, q i) < H)
    (hint : Integrable (fun n ↦ ((totalCount n).descFactorial (∑ i, q i) : ℝ)) μ)
    (hintnext : Integrable (fun n ↦ ((totalCount n).descFactorial ((∑ i, q i) + 1) : ℝ)) μ) :
    0 ≤ factorialMoment μ q - ∑ n ∈ countTruncation H, μ.real {n} * factorialPolynomial q n ∧
    factorialMoment μ q - ∑ n ∈ countTruncation H, μ.real {n} * factorialPolynomial q n ≤
      (∫ n, ((totalCount n).descFactorial ((∑ i, q i) + 1) : ℝ) ∂μ) /
        ((H : ℝ) - (∑ i, q i : ℕ)) := by
  have hpi := factorialPolynomial_integrable_of_total μ q hint
  have hset : MeasurableSet (countTruncation (ι := ι) H : Set (ι → ℕ)) :=
    (countTruncation H).measurableSet
  have hfinite := setIntegral_finset (μ := μ) (countTruncation H) hpi.integrableOn
  simp only [smul_eq_mul] at hfinite
  have htail : factorialMoment μ q -
      ∑ n ∈ countTruncation H, μ.real {n} * factorialPolynomial q n =
      ∫ n, {n | H < totalCount n}.indicator (factorialPolynomial q) n ∂μ := by
    rw [factorialMoment, ← hfinite, ← setIntegral_compl hset hpi, countTruncation_compl,
      ← integral_indicator ((Set.to_countable _).measurableSet)]
  rw [htail]
  refine ⟨integral_nonneg (fun n ↦ Set.indicator_nonneg (fun _ _ ↦ factorialPolynomial_nonneg q _) n),
    integral_mixed_count_tail_le μ q H hH hint hintnext⟩

/-- The actual mass outside the finite count cutoff is controlled by
the first total moment, so tightness is not supplied as an interface. -/
theorem probability_countTruncation_compl_le (μ : Measure (ι → ℕ)) [IsFiniteMeasure μ]
    (H : ℕ) (hH : 0 < H) (hint : Integrable (fun n ↦ (totalCount n : ℝ)) μ) :
    μ.real (countTruncation (ι := ι) H : Set (ι → ℕ))ᶜ ≤
      (∫ n, (totalCount n : ℝ) ∂μ) / (H : ℝ) := by
  have he := integral_mixed_count_tail_le μ (fun _ ↦ 0) H (by simpa using hH)
    (by simpa only [Finset.sum_const_zero, Nat.descFactorial_zero, Nat.cast_one] using
      integrable_const (1 : ℝ))
    (by simpa only [Finset.sum_const_zero, zero_add, Nat.descFactorial_one] using hint)
  have hzero : (factorialPolynomial (fun _ : ι ↦ 0) : (ι → ℕ) → ℝ) = 1 := by
    funext n
    simp [factorialPolynomial]
  rw [hzero] at he
  simp only [Finset.sum_const_zero, Nat.descFactorial_one, zero_add, Nat.cast_zero, sub_zero] at he
  rw [integral_indicator_one ((Set.to_countable _).measurableSet)] at he
  rwa [countTruncation_compl]

/-- Actual event probabilities are approximated by a finite atom sum,
uniformly over all events. This is a finite-state law truncation error,
not an assumed point-probability determination statement. -/
theorem event_probability_finite_truncation_error (μ : Measure (ι → ℕ)) [IsFiniteMeasure μ]
    (A : Set (ι → ℕ)) (H : ℕ) (hH : 0 < H)
    (hint : Integrable (fun n ↦ (totalCount n : ℝ)) μ) :
    0 ≤ μ.real A - ∑ n ∈ (countTruncation H).filter (fun n ↦ n ∈ A), μ.real {n} ∧
    μ.real A - ∑ n ∈ (countTruncation (ι := ι) H).filter (fun n ↦ n ∈ A), μ.real {n} ≤
      (∫ n, (totalCount n : ℝ) ∂μ) / (H : ℝ) := by
  classical
  let F := (countTruncation (ι := ι) H).filter (fun n ↦ n ∈ A)
  have hF : (F : Set (ι → ℕ)) = A ∩ (countTruncation (ι := ι) H : Set (ι → ℕ)) := by
    ext n
    simp only [F, Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff]
    exact and_comm
  have hsum : μ.real (F : Set (ι → ℕ)) = ∑ n ∈ F, μ.real {n} := by
    exact (sum_measureReal_singleton F).symm
  have heq : μ.real A - ∑ n ∈ F, μ.real {n} =
      μ.real (A \ (countTruncation (ι := ι) H : Set (ι → ℕ))) := by
    rw [← hsum, hF]
    have hd := measureReal_sdiff_add_inter (μ := μ) (s := A)
      (t := (countTruncation (ι := ι) H : Set (ι → ℕ))) (countTruncation H).measurableSet
    linarith
  have hsub : A \ (countTruncation (ι := ι) H : Set (ι → ℕ)) ⊆
      (countTruncation (ι := ι) H : Set (ι → ℕ))ᶜ := fun _ hn ↦ hn.2
  change 0 ≤ μ.real A - ∑ n ∈ F, μ.real {n} ∧
    μ.real A - ∑ n ∈ F, μ.real {n} ≤ _
  rw [heq]
  exact ⟨measureReal_nonneg, (measureReal_mono hsub).trans
    (probability_countTruncation_compl_le μ H hH hint)⟩

/-- Every bounded actual test integral has a uniformly quantified
finite atom-sum truncation error from the first total moment. -/
theorem bounded_test_finite_truncation_error (μ : Measure (ι → ℕ)) [IsFiniteMeasure μ]
    (f : (ι → ℕ) → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ n, |f n| ≤ B)
    (H : ℕ) (hH : 0 < H) (hint : Integrable (fun n ↦ (totalCount n : ℝ)) μ) :
    |(∫ n, f n ∂μ) - ∑ n ∈ countTruncation H, μ.real {n} * f n| ≤
      B * ((∫ n, (totalCount n : ℝ) ∂μ) / (H : ℝ)) := by
  have hfi : Integrable f μ := (integrable_const B).mono'
    (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall (fun n ↦ by simpa only [Real.norm_eq_abs] using hf n))
  have hs : MeasurableSet (countTruncation (ι := ι) H : Set (ι → ℕ)) :=
    (countTruncation H).measurableSet
  have hfinite := setIntegral_finset (μ := μ) (countTruncation H) hfi.integrableOn
  simp only [smul_eq_mul] at hfinite
  rw [← hfinite, ← setIntegral_compl hs hfi]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := f)
    (s := (countTruncation (ι := ι) H : Set (ι → ℕ))ᶜ) (measure_lt_top _ _)
    (fun n _ ↦ by simpa only [Real.norm_eq_abs] using hf n)
  have hb' : |∫ n in (countTruncation (ι := ι) H : Set (ι → ℕ))ᶜ, f n ∂μ| ≤
      B * μ.real (countTruncation (ι := ι) H : Set (ι → ℕ))ᶜ := by
    simpa only [Real.norm_eq_abs, measureReal_def] using hb
  exact hb'.trans
    (mul_le_mul_of_nonneg_left (probability_countTruncation_compl_le μ H hH hint) hB)

end PerronWright.MixedFactorialTail
