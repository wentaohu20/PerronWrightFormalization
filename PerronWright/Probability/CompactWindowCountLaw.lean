import PerronWright.Probability.CompactWindowFactorialMoments
import PerronWright.Probability.FactorialCountLimitExistence
import PerronWright.Probability.FinitePointMeasurePolish
import PerronWright.Probability.FactorialWindowMass

/-! # The genuine compact-window component-number limit

The source laws count actual graph components. All their factorial moments
converge to the proved density integrals; tightness and moment determinacy
construct a unique probability law and prove actual weak convergence.
This does not identify the Brownian excursion law.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology

noncomputable section

namespace PerronWright.CompactWindowCountLaw

open FinitePointMeasureCompact FinitePointMeasurePolish
  ComponentWindowPointMeasures ComponentWindowFactorialCounts
  CompactWindowFactorialMoments FactorialCountDeterminacy
  FactorialCountLimitExistence FactorialDensity

/-- Singleton count vector, retaining the actual integer component mass. -/
def countVector {E : Type*} [MeasurableSpace E] (η : PointMeasure E) : Fin 1 → ℕ :=
  fun _ ↦ size η

theorem continuous_countVector {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] : Continuous (countVector : PointMeasure E → Fin 1 → ℕ) := by
  have hc : Continuous (fun η : PointMeasure E ↦ (mass η : ℝ)) :=
    NNReal.continuous_coe.comp continuous_mass
  have he : (Nat.cast : ℕ → ℝ) ∘ (size : PointMeasure E → ℕ) =
      fun η : PointMeasure E ↦ (mass η : ℝ) := by
    funext η
    change (size η : ℝ) = (mass η : ℝ)
    exact_mod_cast (mass_eq_size η).symm
  rw [← he] at hc
  exact continuous_pi (fun _ ↦ Nat.isClosedEmbedding_coe_real.isEmbedding.continuous_iff.mpr hc)

def countLaw {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (ν : ProbabilityMeasure (PointMeasure E)) : ProbabilityMeasure (Fin 1 → ℕ) :=
  ν.map continuous_countVector.measurable.aemeasurable

@[simp] theorem factorialPolynomial_countVector {E : Type*} [MeasurableSpace E]
    (q : Fin 1 → ℕ) (η : PointMeasure E) :
    factorialPolynomial q (countVector η) = ((size η).descFactorial (q 0) : ℝ) := by
  simp [factorialPolynomial,countVector]

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

def actualCountLaw (M : CompactBJRModel S) (lambda a b : ℝ) (R n : ℕ) :
    ProbabilityMeasure (Fin 1 → ℕ) := countLaw (unmarkedWindowLaw M lambda a b R n)

theorem actualCountLaw_factorial_integrable (M : CompactBJRModel S)
    (lambda a b : ℝ) (R n : ℕ) (q : Fin 1 → ℕ) :
    Integrable (factorialPolynomial q) (actualCountLaw M lambda a b R n : Measure (Fin 1 → ℕ)) := by
  unfold actualCountLaw countLaw
  rw [ProbabilityMeasure.toMeasure_map]
  apply (integrable_map_measure (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable
    continuous_countVector.measurable.aemeasurable).mpr
  change Integrable (fun η ↦ factorialPolynomial q (countVector η))
    (unmarkedWindowLaw M lambda a b R n : Measure (PointMeasure (SurplusWindow a b R)))
  simpa only [Function.comp_apply,factorialPolynomial_countVector] using
    windowLaw_descFactorial_integrable M lambda a b R n (q 0)

theorem actualCountLaw_factorialMoment (M : CompactBJRModel S)
    (lambda a b : ℝ) (R n : ℕ) (q : Fin 1 → ℕ) :
    factorialMoment (actualCountLaw M lambda a b R n : Measure (Fin 1 → ℕ)) q =
      ∫ η, ((size η).descFactorial (q 0) : ℝ) ∂(unmarkedWindowLaw M lambda a b R n :
        Measure (PointMeasure (SurplusWindow a b R))) := by
  unfold factorialMoment actualCountLaw countLaw
  rw [ProbabilityMeasure.toMeasure_map,integral_map continuous_countVector.measurable.aemeasurable
    (measurable_of_countable (factorialPolynomial q)).aestronglyMeasurable]
  simp only [factorialPolynomial_countVector]

theorem actualCountLaw_factorialMoment_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (q : Fin 1 → ℕ) :
    Tendsto (fun n ↦ factorialMoment (actualCountLaw M lambda a b R n) q) atTop
      (𝓝 (windowMass (q 0) (M.alpha hM) (M.beta hM) lambda a b R)) := by
  simp_rw [actualCountLaw_factorialMoment]
  exact windowLaw_all_factorial_moments_tendsto M hM hQP lambda a b ha hab R (q 0)

theorem singleton_windowMass_series (alpha lambda : ℝ) {beta a b : ℝ}
    (hbeta : 0 < beta) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    Summable (fun q : Fin 1 → ℕ ↦ (2 : ℝ)^(∑ i, q i) *
      windowMass (q 0) alpha beta lambda a b R / ∏ i, ((q i).factorial : ℝ)) := by
  have hs := summable_windowMass_factorial alpha lambda hbeta ha hab R 2
  have he := (Equiv.funUnique (Fin 1) ℕ).summable_iff.mpr hs
  simpa [Function.comp_def,Equiv.funUnique,Equiv.piUnique,Fin.sum_univ_one,Fin.prod_univ_one] using he

/-- Actual source laws construct their unique density-moment limit.
No target-law realization is assumed. -/
theorem exists_unique_actualCountLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃! ν : ProbabilityMeasure (Fin 1 → ℕ),
      (∀ q, Integrable (factorialPolynomial q) (ν : Measure (Fin 1 → ℕ))) ∧
      (∀ q, factorialMoment (ν : Measure (Fin 1 → ℕ)) q =
        windowMass (q 0) (M.alpha hM) (M.beta hM) lambda a b R) ∧
      Tendsto (actualCountLaw M lambda a b R) atTop (𝓝 ν) :=
  exists_unique_limit_of_factorialMoments (actualCountLaw M lambda a b R)
    (actualCountLaw_factorial_integrable M lambda a b R)
    (fun q ↦ windowMass (q 0) (M.alpha hM) (M.beta hM) lambda a b R)
    (actualCountLaw_factorialMoment_tendsto M hM hQP lambda a b ha hab R)
    (singleton_windowMass_series _ _ (M.beta_pos hM) ha hab R)

end PerronWright.CompactWindowCountLaw
