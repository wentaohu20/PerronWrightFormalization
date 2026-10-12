import PerronWright.Probability.FactorialCountDeterminacy

/-!
# Actual factorial generating series and count-law determinacy

Finite binomial expansions prove the pointwise series.  Tonelli and
dominated convergence then prove the generating-series identities for
unbounded count vectors.  In particular, summable total factorial moments
give the exponential integrability needed by the joint inversion theorem.
-/

open MeasureTheory Filter
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FactorialGeneratingSeries

open BinomialInversion FactorialCountDeterminacy

theorem scalar_weighted_hasSum_argument (n : ℕ) (z : ℝ) :
    HasSum (fun q : ℕ ↦ z ^ q * (n.choose q : ℝ)) ((1 + z) ^ n) := by
  have hz : ∀ q ∉ Finset.range (n + 1), z ^ q * (n.choose q : ℝ) = 0 := by
    intro q hq
    have h : n < q := by simpa using hq
    simp only [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]
  have hs : (∑ q ∈ Finset.range (n + 1), z ^ q * (n.choose q : ℝ)) = (1 + z) ^ n := by
    simpa only [one_pow, mul_one, add_comm z 1] using (_root_.add_pow z 1 n).symm
  rw [← hs]
  exact hasSum_sum_of_ne_finset_zero hz

theorem scalar_weighted_hasSum (n : ℕ) :
    HasSum (fun q : ℕ ↦ (2 : ℝ) ^ q * (n.choose q : ℝ)) ((3 : ℝ) ^ n) := by
  simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using
    scalar_weighted_hasSum_argument n 2

variable {ι : Type*} [Fintype ι]

/-- The total count in a finite partition. -/
def totalCount (n : ι → ℕ) : ℕ := ∑ i, n i

def weightedPolynomial (q n : ι → ℕ) : ℝ :=
  (2 : ℝ) ^ (∑ i, q i) * binomialPolynomial q n

theorem weightedPolynomial_nonneg (q n : ι → ℕ) : 0 ≤ weightedPolynomial q n :=
  mul_nonneg (by positivity) (binomialPolynomial_nonneg q n)

theorem weightedPolynomial_eq_prod (q n : ι → ℕ) :
    weightedPolynomial q n = ∏ i, (2 : ℝ) ^ (q i) * ((n i).choose (q i) : ℝ) := by
  simp only [weightedPolynomial, binomialPolynomial, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]

theorem weightedPolynomial_zero_outside (n q : ι → ℕ)
    (hq : q ∉ Fintype.piFinset (fun i ↦ Finset.range (n i + 1))) :
    weightedPolynomial q n = 0 := by
  rw [Fintype.mem_piFinset] at hq
  push Not at hq
  obtain ⟨i, hi⟩ := hq
  have h : n i < q i := by simpa using hi
  rw [weightedPolynomial_eq_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (by simp only [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero])

/-- The exact multivariate generating series at argument `2`. -/
theorem joint_weighted_hasSum (n : ι → ℕ) :
    HasSum (fun q : ι → ℕ ↦ weightedPolynomial q n) ((3 : ℝ) ^ totalCount n) := by
  have hs : (∑ q ∈ Fintype.piFinset (fun i ↦ Finset.range (n i + 1)),
      weightedPolynomial q n) = (3 : ℝ) ^ totalCount n := by
    simp_rw [weightedPolynomial_eq_prod]
    rw [← Finset.prod_univ_sum (fun i ↦ Finset.range (n i + 1))
      (fun i j ↦ (2 : ℝ) ^ j * ((n i).choose j : ℝ))]
    have hi (i : ι) : (∑ j ∈ Finset.range (n i + 1),
        (2 : ℝ) ^ j * ((n i).choose j : ℝ)) = (3 : ℝ) ^ n i := by
      rw [← (scalar_weighted_hasSum (n i)).tsum_eq,
        tsum_eq_sum (s := Finset.range (n i + 1))]
      intro q hq
      have h : n i < q := by simpa using hq
      simp only [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]
    simp_rw [hi]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [← hs]
  exact hasSum_sum_of_ne_finset_zero (weightedPolynomial_zero_outside n)

theorem binomialPolynomial_le_total_exp (q n : ι → ℕ) :
    binomialPolynomial q n ≤ (3 : ℝ) ^ totalCount n := by
  calc
    _ ≤ ∏ i, (2 : ℝ) ^ n i := by
      apply Finset.prod_le_prod
      · intro i _
        exact Nat.cast_nonneg _
      · intro i _
        exact_mod_cast Nat.choose_le_two_pow (n i) (q i)
    _ = (2 : ℝ) ^ totalCount n := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- Exponential integrability of the actual total count yields the full
mixed generating series, not only a formal series of coefficients. -/
theorem mixed_series_hasSum (μ : Measure (ι → ℕ))
    (hexp : Integrable (fun n ↦ (3 : ℝ) ^ totalCount n) μ) :
    HasSum (fun q : ι → ℕ ↦ (2 : ℝ) ^ (∑ i, q i) * binomialMoment μ q)
      (∫ n, (3 : ℝ) ^ totalCount n ∂μ) := by
  have hs : HasSum (fun q : ι → ℕ ↦ ∫ n, weightedPolynomial q n ∂μ)
      (∫ n, (3 : ℝ) ^ totalCount n ∂μ) := by
    apply hasSum_integral_of_dominated_convergence
      (fun q n ↦ weightedPolynomial q n)
    · intro q
      exact (measurable_of_countable _).aestronglyMeasurable
    · intro q
      exact Eventually.of_forall (fun n ↦ by
        rw [Real.norm_of_nonneg (weightedPolynomial_nonneg q n)])
    · exact Eventually.of_forall (fun n ↦ (joint_weighted_hasSum n).summable)
    · have hfun : (fun n : ι → ℕ ↦ ∑' q : ι → ℕ, weightedPolynomial q n) =
          (fun n ↦ (3 : ℝ) ^ totalCount n) := by
        funext n
        exact (joint_weighted_hasSum n).tsum_eq
      rw [hfun]
      exact hexp
    · exact Eventually.of_forall joint_weighted_hasSum
  simpa only [weightedPolynomial, integral_const_mul, binomialMoment] using hs

theorem binomialPolynomial_integrable (μ : Measure (ι → ℕ))
    (hexp : Integrable (fun n ↦ (3 : ℝ) ^ totalCount n) μ) (q : ι → ℕ) :
    Integrable (binomialPolynomial q) μ := by
  apply hexp.mono_nonneg (measurable_of_countable _).aestronglyMeasurable
  · exact Eventually.of_forall (binomialPolynomial_nonneg q)
  · exact Eventually.of_forall (binomialPolynomial_le_total_exp q)

/-- A total factorial-moment generating series gives genuine exponential
integrability.  This is the step justified by the cubic density-window
bound in the paper. -/
theorem total_exp_integrable_of_moment_series_argument (μ : Measure (ι → ℕ))
    (z : ℝ) (hz : 0 ≤ z)
    (hint : ∀ q : ℕ, Integrable (fun n ↦ ((totalCount n).choose q : ℝ)) μ)
    (hseries : Summable (fun q : ℕ ↦
      z ^ q * ∫ n, ((totalCount n).choose q : ℝ) ∂μ)) :
    Integrable (fun n ↦ (1 + z) ^ totalCount n) μ := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun n ↦ by positivity))]
  have hpoint (n : ι → ℕ) : ENNReal.ofReal ((1 + z) ^ totalCount n) =
      ∑' q : ℕ, ENNReal.ofReal (z ^ q * ((totalCount n).choose q : ℝ)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun q ↦ by positivity)
      (scalar_weighted_hasSum_argument (totalCount n) z).summable,
      (scalar_weighted_hasSum_argument (totalCount n) z).tsum_eq]
  simp_rw [hpoint]
  rw [lintegral_tsum (fun _ ↦ (measurable_of_countable _).aemeasurable)]
  have hint' (q : ℕ) :
      (∫⁻ n, ENNReal.ofReal (z ^ q * ((totalCount n).choose q : ℝ)) ∂μ) =
        ENNReal.ofReal (z ^ q * ∫ n, ((totalCount n).choose q : ℝ) ∂μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal ((hint q).const_mul _)
      (Eventually.of_forall (fun n ↦ by positivity)), integral_const_mul]
  simp_rw [hint']
  exact hseries.tsum_ofReal_lt_top

theorem total_exp_integrable_of_moment_series (μ : Measure (ι → ℕ))
    (hint : ∀ q : ℕ, Integrable (fun n ↦ ((totalCount n).choose q : ℝ)) μ)
    (hseries : Summable (fun q : ℕ ↦
      (2 : ℝ) ^ q * ∫ n, ((totalCount n).choose q : ℝ) ∂μ)) :
    Integrable (fun n ↦ (3 : ℝ) ^ totalCount n) μ := by
  simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using
    total_exp_integrable_of_moment_series_argument μ 2 (by norm_num) hint hseries

/-- Joint count-law determinacy under literal exponential integrability of
the total counts and equality of all mixed factorial moments. -/
theorem measure_eq_of_factorialMoments_of_total_exp
    (μ ν : Measure (ι → ℕ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμexp : Integrable (fun n ↦ (3 : ℝ) ^ totalCount n) μ)
    (hνexp : Integrable (fun n ↦ (3 : ℝ) ^ totalCount n) ν)
    (hmom : ∀ q, factorialMoment μ q = factorialMoment ν q) : μ = ν := by
  apply measure_eq_of_binomialMoments μ ν
    (binomialPolynomial_integrable μ hμexp)
    (binomialPolynomial_integrable ν hνexp)
    (mixed_series_hasSum μ hμexp).summable
  intro q
  rw [binomialMoment_eq_div, binomialMoment_eq_div, hmom]

end PerronWright.FactorialGeneratingSeries
