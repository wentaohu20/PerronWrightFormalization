import PerronWright.Probability.BinomialInversion

/-!
# Mixed factorial moments determine the actual joint count law

The inversion formula is proved by integration of the pointwise binomial
identity.  Its absolute-summability hypothesis concerns the literal mixed
moments of the given measure; it is not an assumed determination interface.
The subsequent window-density bound supplies this hypothesis in the Aldous
application.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FactorialCountDeterminacy

open BinomialInversion

variable {ι : Type*} [Fintype ι]

/-- The literal mixed binomial moment of a count-vector law. -/
def binomialMoment (μ : Measure (ι → ℕ)) (q : ι → ℕ) : ℝ :=
  ∫ n, binomialPolynomial q n ∂μ

theorem binomialPolynomial_nonneg (q n : ι → ℕ) :
    0 ≤ binomialPolynomial q n := by
  exact Finset.prod_nonneg (fun i _ ↦ Nat.cast_nonneg _)

theorem binomialMoment_nonneg (μ : Measure (ι → ℕ)) (q : ι → ℕ) :
    0 ≤ binomialMoment μ q := integral_nonneg (binomialPolynomial_nonneg q)

theorem jointTerm_norm (m q n : ι → ℕ) :
    ‖jointTerm m q n‖ = |jointCoefficient m q| * binomialPolynomial q n := by
  simp only [jointTerm, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (binomialPolynomial_nonneg q n)]

theorem integral_jointTerm_norm (μ : Measure (ι → ℕ)) (m q : ι → ℕ) :
    (∫ n, ‖jointTerm m q n‖ ∂μ) = |jointCoefficient m q| * binomialMoment μ q := by
  simp_rw [jointTerm_norm]
  rw [integral_const_mul]
  rfl

/-- Exact recovery of each actual atom from the absolutely convergent mixed
binomial-moment series. -/
theorem atom_eq_moment_series (μ : Measure (ι → ℕ)) [IsFiniteMeasure μ]
    (hint : ∀ q, Integrable (binomialPolynomial q) μ)
    (hseries : Summable (fun q : ι → ℕ ↦
      (2 : ℝ) ^ (∑ i, q i) * binomialMoment μ q)) (m : ι → ℕ) :
    μ.real {m} = ∑' q : ι → ℕ, jointCoefficient m q * binomialMoment μ q := by
  have hterm (q : ι → ℕ) : Integrable (jointTerm m q) μ :=
    (hint q).const_mul (jointCoefficient m q)
  have hnorm : Summable (fun q : ι → ℕ ↦ ∫ n, ‖jointTerm m q n‖ ∂μ) := by
    apply hseries.of_norm_bounded
    intro q
    rw [integral_jointTerm_norm, Real.norm_of_nonneg
      (mul_nonneg (abs_nonneg _) (binomialMoment_nonneg μ q))]
    exact mul_le_mul_of_nonneg_right (jointCoefficient_abs_le m q)
      (binomialMoment_nonneg μ q)
  have hs := integral_tsum_of_summable_integral_norm hterm hnorm
  have hpoint : (fun n : ι → ℕ ↦ ∑' q : ι → ℕ, jointTerm m q n) =
      Set.indicator {m} (fun _ ↦ (1 : ℝ)) := by
    funext n
    rw [joint_tsum]
    simp only [Set.indicator_apply, Set.mem_singleton_iff]
  rw [hpoint] at hs
  change (∑' q : ι → ℕ, ∫ n, jointTerm m q n ∂μ) =
    (∫ n, ({m} : Set (ι → ℕ)).indicator (1 : (ι → ℕ) → ℝ) n ∂μ) at hs
  rw [integral_indicator_one (measurableSet_singleton m)] at hs
  rw [← hs]
  apply tsum_congr
  intro q
  change (∫ n, jointCoefficient m q * binomialPolynomial q n ∂μ) = _
  rw [integral_const_mul]
  rfl

/-- Equality of literal mixed binomial moments implies equality of the full
joint count laws when their moment series is absolutely convergent. -/
theorem measure_eq_of_binomialMoments
    (μ ν : Measure (ι → ℕ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμint : ∀ q, Integrable (binomialPolynomial q) μ)
    (hνint : ∀ q, Integrable (binomialPolynomial q) ν)
    (hμseries : Summable (fun q : ι → ℕ ↦
      (2 : ℝ) ^ (∑ i, q i) * binomialMoment μ q))
    (hmom : ∀ q, binomialMoment μ q = binomialMoment ν q) : μ = ν := by
  have hνseries : Summable (fun q : ι → ℕ ↦
      (2 : ℝ) ^ (∑ i, q i) * binomialMoment ν q) := by
    simpa only [← hmom] using hμseries
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro m
  rw [atom_eq_moment_series μ hμint hμseries,
    atom_eq_moment_series ν hνint hνseries]
  simp_rw [hmom]

/-- The literal mixed falling-factorial polynomial. -/
def factorialPolynomial (q n : ι → ℕ) : ℝ := ∏ i, (n i).descFactorial (q i)

/-- The actual mixed falling-factorial moment. -/
def factorialMoment (μ : Measure (ι → ℕ)) (q : ι → ℕ) : ℝ :=
  ∫ n, factorialPolynomial q n ∂μ

theorem factorialPolynomial_eq (q n : ι → ℕ) :
    factorialPolynomial q n = (∏ i, ((q i).factorial : ℝ)) * binomialPolynomial q n := by
  simp only [factorialPolynomial, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, Finset.prod_mul_distrib, binomialPolynomial]

theorem factorialMoment_eq (μ : Measure (ι → ℕ)) (q : ι → ℕ) :
    factorialMoment μ q = (∏ i, ((q i).factorial : ℝ)) * binomialMoment μ q := by
  unfold factorialMoment
  simp_rw [factorialPolynomial_eq]
  rw [integral_const_mul]
  rfl

theorem binomialMoment_eq_div (μ : Measure (ι → ℕ)) (q : ι → ℕ) :
    binomialMoment μ q = factorialMoment μ q / ∏ i, ((q i).factorial : ℝ) := by
  have hpos : 0 < ∏ i, ((q i).factorial : ℝ) :=
    Finset.prod_pos (fun i _ ↦ by exact_mod_cast Nat.factorial_pos (q i))
  rw [factorialMoment_eq]
  field_simp [hpos.ne']

/-- Determinacy phrased directly in mixed falling-factorial moments. -/
theorem measure_eq_of_factorialMoments
    (μ ν : Measure (ι → ℕ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμint : ∀ q, Integrable (factorialPolynomial q) μ)
    (hνint : ∀ q, Integrable (factorialPolynomial q) ν)
    (hμseries : Summable (fun q : ι → ℕ ↦
      (2 : ℝ) ^ (∑ i, q i) * factorialMoment μ q /
        ∏ i, ((q i).factorial : ℝ)))
    (hmom : ∀ q, factorialMoment μ q = factorialMoment ν q) : μ = ν := by
  have hint (ζ : Measure (ι → ℕ))
      (hζ : ∀ q, Integrable (factorialPolynomial q) ζ) (q : ι → ℕ) :
      Integrable (binomialPolynomial q) ζ := by
    have hpos : 0 < ∏ i, ((q i).factorial : ℝ) :=
      Finset.prod_pos (fun i _ ↦ by exact_mod_cast Nat.factorial_pos (q i))
    have hfun : binomialPolynomial q =
        (fun n ↦ factorialPolynomial q n / ∏ i, ((q i).factorial : ℝ)) := by
      funext n
      rw [factorialPolynomial_eq]
      field_simp [hpos.ne']
    rw [hfun]
    exact (hζ q).div_const _
  apply measure_eq_of_binomialMoments μ ν (hint μ hμint) (hint ν hνint)
  · simpa only [binomialMoment_eq_div, mul_div_assoc] using hμseries
  · intro q
    rw [binomialMoment_eq_div, binomialMoment_eq_div, hmom]

end PerronWright.FactorialCountDeterminacy
