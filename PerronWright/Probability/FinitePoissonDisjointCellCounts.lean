import PerronWright.Probability.FinitePoissonCellFactorialMoments
import PerronWright.Enumeration.CubicForbiddenCorrectionBridge

/-!
# Actual independent Poisson counts in disjoint spatial cells

The count law is identified from the proved mixed factorial moments.
The inversion theorem's summability condition is discharged by genuine
finite products of exponential series. Independence is a conclusion,
not an input to the spatial construction.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FinitePoissonDisjointCellCounts

open FinitePointMeasureCompact FinitePoissonCellFactorialMoments
  FactorialCountDeterminacy

variable {D : Type*} [Fintype D]

theorem finitePoisson_integrable_factorialPolynomial (r : D → ℝ≥0) (q : D → ℕ) :
    Integrable (factorialPolynomial q) (PoissonCountKernel.finiteCountLaw r) := by
  exact Integrable.fintype_prod (fun i ↦
    PoissonFactorialMoments.integrable_descFactorial (r i) (q i))

theorem finitePoisson_factorialMoment (r : D → ℝ≥0) (q : D → ℕ) :
    factorialMoment (PoissonCountKernel.finiteCountLaw r) q = ∏ i, (r i : ℝ) ^ q i :=
  PoissonFactorialMoments.integral_mixed_descFactorial r q

/-- The actual Poisson moment series meets the full mixed inversion criterion. -/
theorem summable_finitePoisson_factorialSeries (r : D → ℝ≥0) :
    Summable (fun q : D → ℕ ↦ (2 : ℝ) ^ (∑ i, q i) *
      factorialMoment (PoissonCountKernel.finiteCountLaw r) q /
        ∏ i, ((q i).factorial : ℝ)) := by
  let e := Fintype.equivFin D
  let a := Equiv.arrowCongr e (Equiv.refl ℕ)
  have hs := (GraphCore.summable_finFunction_prod_and_tsum
    (fun j : Fin (Fintype.card D) ↦ fun n : ℕ ↦
      (2 * (r (e.symm j) : ℝ)) ^ n / (n.factorial : ℝ))
    (fun j ↦ Real.summable_pow_div_factorial (2 * (r (e.symm j) : ℝ)))).1
  have ht := a.summable_iff.mpr hs
  have hp : Summable (fun q : D → ℕ ↦
      ∏ i, (2 * (r i : ℝ)) ^ q i / ((q i).factorial : ℝ)) := by
    apply ht.congr
    intro q
    exact e.symm.prod_comp (fun i : D ↦
      (2 * (r i : ℝ)) ^ q i / ((q i).factorial : ℝ))
  apply hp.congr
  intro q
  simp only [finitePoisson_factorialMoment, mul_pow, Finset.prod_div_distrib,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [BorelSpace E] [SecondCountableTopology E] [HasOuterApproxClosed E] [Nonempty E]

/-- The literal pushforward of the actual finite spatial point measure. -/
def countLaw (ν : FiniteMeasure E) (A : D → Set E) : Measure (D → ℕ) :=
  (FinitePoissonIntensityLaw.law ν).map (fun η i ↦ count η (A i))

omit [Fintype D] in
theorem countLaw_isProbabilityMeasure (ν : FiniteMeasure E)
    (A : D → Set E) (hA : ∀ i, MeasurableSet (A i)) :
    IsProbabilityMeasure (countLaw ν A) := by
  exact Measure.isProbabilityMeasure_map
    (FinitePointMeasureMeasurable.measurable_count_vector A hA).aemeasurable

theorem countLaw_integrable_factorialPolynomial (ν : FiniteMeasure E)
    (A : D → Set E) (q : D → ℕ)
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) :
    Integrable (factorialPolynomial q) (countLaw ν A) := by
  apply (integrable_map_measure
    (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable
    (FinitePointMeasureMeasurable.measurable_count_vector A hA).aemeasurable).mpr
  exact intensityLaw_integrable_mixedFactorial ν A q hAd hA

theorem countLaw_factorialMoment (ν : FiniteMeasure E)
    (A : D → Set E) (q : D → ℕ)
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) :
    factorialMoment (countLaw ν A) q = ∏ i, (ν (A i) : ℝ) ^ q i := by
  unfold factorialMoment countLaw
  rw [integral_map (FinitePointMeasureMeasurable.measurable_count_vector A hA).aemeasurable
    (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable]
  simpa only [FiniteMeasure.measureReal_eq_coe_coeFn] using
    intensityLaw_integral_mixedFactorial ν A q hAd hA

/-- The disjoint-cell count law is exactly the independent Poisson product. -/
theorem countLaw_eq_finitePoisson (ν : FiniteMeasure E) (A : D → Set E)
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) :
    countLaw ν A = PoissonCountKernel.finiteCountLaw (fun i ↦ ν (A i)) := by
  let := countLaw_isProbabilityMeasure ν A hA
  symm
  apply measure_eq_of_factorialMoments
    (PoissonCountKernel.finiteCountLaw (fun i ↦ ν (A i))) (countLaw ν A)
    (finitePoisson_integrable_factorialPolynomial _)
    (fun q ↦ countLaw_integrable_factorialPolynomial ν A q hAd hA)
    (summable_finitePoisson_factorialSeries _)
  intro q
  rw [finitePoisson_factorialMoment, countLaw_factorialMoment ν A q hAd hA]

/-- Every actual cell-count marginal has its literal intensity as Poisson rate. -/
theorem intensityLaw_count_hasLaw (ν : FiniteMeasure E) (A : D → Set E)
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) (i : D) :
    HasLaw (fun η : PointMeasure E ↦ count η (A i)) (poissonMeasure (ν (A i)))
      (FinitePoissonIntensityLaw.law ν) := by
  have hv : HasLaw (fun η : PointMeasure E ↦ fun j ↦ count η (A j))
      (PoissonCountKernel.finiteCountLaw (fun j ↦ ν (A j)))
      (FinitePoissonIntensityLaw.law ν) :=
    ⟨(FinitePointMeasureMeasurable.measurable_count_vector A hA).aemeasurable,
      countLaw_eq_finitePoisson ν A hAd hA⟩
  exact (PoissonCountKernel.finiteCountLaw_hasLaw_eval (fun j ↦ ν (A j)) i).comp hv

/-- Independence of actual spatial counts, derived from the spatial construction. -/
theorem intensityLaw_counts_independent (ν : FiniteMeasure E) (A : D → Set E)
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) :
    iIndepFun (fun i (η : PointMeasure E) ↦ count η (A i))
      (FinitePoissonIntensityLaw.law ν) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i ↦ (FinitePointMeasureMeasurable.measurable_count (hA i)).aemeasurable)).mpr
  change countLaw ν A = Measure.pi (fun i ↦
    (FinitePoissonIntensityLaw.law ν).map (fun η ↦ count η (A i)))
  rw [countLaw_eq_finitePoisson ν A hAd hA]
  unfold PoissonCountKernel.finiteCountLaw
  congr 1
  funext i
  exact (intensityLaw_count_hasLaw ν A hAd hA i).map_eq.symm

end PerronWright.FinitePoissonDisjointCellCounts
