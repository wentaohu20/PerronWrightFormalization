import PerronWright.Probability.FinitePoissonIidCellFactorials

/-!
# Exact disjoint-cell factorial moments of constructed spatial Poisson laws

The arbitrary finite intensity law is the actual normalized iid-atom
construction. Its moments follow from the labelled tuple formula and
the proved factorial moments of the actual Poisson count distribution.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FinitePoissonCellFactorialMoments

open FinitePointMeasureCompact FinitePoissonIidCellFactorials
  FactorialCountDeterminacy

theorem poisson_lintegral_descFactorial (r : ℝ≥0) (q : ℕ) :
    (∫⁻ n : ℕ, (n.descFactorial q : ℝ≥0∞) ∂poissonMeasure r) =
      (r : ℝ≥0∞) ^ q := by
  have ho := ofReal_integral_eq_lintegral_ofReal
    (PoissonFactorialMoments.integrable_descFactorial r q)
    (Filter.Eventually.of_forall (fun n : ℕ ↦ Nat.cast_nonneg (n.descFactorial q)))
  simpa only [PoissonFactorialMoments.integral_descFactorial,
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (NNReal.coe_nonneg r),
    ENNReal.ofReal_coe_nnreal] using ho.symm

variable {E D : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [BorelSpace E] [SecondCountableTopology E] [HasOuterApproxClosed E] [Fintype D]

/-- All mixed factorial moments of disjoint cells of the actual spatial law. -/
theorem law_lintegral_mixedFactorial (r : ℝ≥0) (μ : Measure E)
    [IsProbabilityMeasure μ] (A : D → Set E) (q : D → ℕ)
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) :
    (∫⁻ η, mixedFactorial A q η ∂FinitePoissonPointLaw.law r μ) =
      ∏ i, ((r : ℝ≥0∞) * μ (A i)) ^ q i := by
  simp only [FinitePoissonPointLaw.law, lintegral_sum_measure,
    lintegral_smul_measure, smul_eq_mul,
    iidAtomsLaw_lintegral_mixedFactorial μ _ A q hAd hA]
  simp_rw [← mul_assoc]
  rw [ENNReal.tsum_mul_right]
  have he : (∑' n : ℕ, poissonMeasure r {n} *
      (n.descFactorial (∑ i, q i) : ℝ≥0∞)) = (r : ℝ≥0∞) ^ (∑ i, q i) := by
    rw [← poisson_lintegral_descFactorial r (∑ i, q i), lintegral_countable']
    congr 1
    funext n
    exact mul_comm _ _
  rw [he]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

variable [Nonempty E]

/-- No disjoint-cell moment formula is assumed for the actual finite intensity. -/
theorem intensityLaw_lintegral_mixedFactorial (ν : FiniteMeasure E)
    (A : D → Set E) (q : D → ℕ)
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) :
    (∫⁻ η, mixedFactorial A q η ∂FinitePoissonIntensityLaw.law ν) =
      ∏ i, ((ν : Measure E) (A i)) ^ q i := by
  rw [FinitePoissonIntensityLaw.law, law_lintegral_mixedFactorial _ _ A q hAd hA]
  congr 1
  funext i
  rw [FinitePoissonIntensityLaw.intensity_decomposition ν, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]

omit [TopologicalSpace E] [BorelSpace E] [SecondCountableTopology E]
  [HasOuterApproxClosed E] [Nonempty E] in
theorem mixedFactorial_toReal (A : D → Set E) (q : D → ℕ) (η : PointMeasure E) :
    (mixedFactorial A q η).toReal =
      factorialPolynomial q (fun i ↦ count η (A i)) := by
  simp only [mixedFactorial, factorialPolynomial, ENNReal.toReal_prod,
    ENNReal.toReal_natCast]

omit [TopologicalSpace E] [BorelSpace E] [SecondCountableTopology E]
  [HasOuterApproxClosed E] [Nonempty E] in
theorem mixedFactorial_ne_top (A : D → Set E) (q : D → ℕ) (η : PointMeasure E) :
    mixedFactorial A q η ≠ ∞ := by
  simp [mixedFactorial, ENNReal.prod_ne_top]

/-- The actual real mixed factorial polynomial is genuinely integrable. -/
theorem intensityLaw_integrable_mixedFactorial (ν : FiniteMeasure E)
    (A : D → Set E) (q : D → ℕ)
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) :
    Integrable (fun η ↦ factorialPolynomial q (fun i ↦ count η (A i)))
      (FinitePoissonIntensityLaw.law ν) := by
  have hi := integrable_toReal_of_lintegral_ne_top
    (measurable_mixedFactorial A q hA).aemeasurable
    (μ := FinitePoissonIntensityLaw.law ν) (by
      rw [intensityLaw_lintegral_mixedFactorial ν A q hAd hA]
      exact ENNReal.prod_ne_top (fun i _ ↦ by
        finiteness))
  simpa only [mixedFactorial_toReal] using hi

/-- Exact real mixed factorial moments, including the zero-intensity case. -/
theorem intensityLaw_integral_mixedFactorial (ν : FiniteMeasure E)
    (A : D → Set E) (q : D → ℕ)
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) :
    (∫ η, factorialPolynomial q (fun i ↦ count η (A i))
      ∂FinitePoissonIntensityLaw.law ν) = ∏ i, ((ν : Measure E).real (A i)) ^ q i := by
  have he := integral_toReal (measurable_mixedFactorial A q hA).aemeasurable
    (μ := FinitePoissonIntensityLaw.law ν)
    (Filter.Eventually.of_forall (fun η ↦ lt_top_iff_ne_top.mpr
      (mixedFactorial_ne_top A q η)))
  rw [intensityLaw_lintegral_mixedFactorial ν A q hAd hA] at he
  simpa only [mixedFactorial_toReal, ENNReal.toReal_prod, ENNReal.toReal_pow,
    Measure.real] using he

end PerronWright.FinitePoissonCellFactorialMoments
