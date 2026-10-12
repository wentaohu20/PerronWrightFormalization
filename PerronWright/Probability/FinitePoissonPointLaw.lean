import PerronWright.Probability.FinitePointMeasureMeasurable
import PerronWright.Probability.PoissonCountKernel
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Constructed finite spatial Poisson laws

An actual Poisson number of independent locations is pushed to the genuine
weak-Borel space of finite integer atomic measures.  The normalization,
count distribution, and rate measurability are proved from this construction.
This is the finite-intensity spatial construction, not an assumption about
Brownian excursion marks or about their factorial densities.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

noncomputable section

namespace PerronWright.FinitePoissonPointLaw

open FinitePointMeasureCompact

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The law of exactly `n` independently sampled actual locations. -/
def iidAtomsLaw (μ : Measure E) (n : ℕ) : Measure (PointMeasure E) :=
  (Measure.pi (fun _ : Fin n ↦ μ)).map ofAtomsPoint

instance (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (iidAtomsLaw μ n) := by
  unfold iidAtomsLaw
  exact Measure.isProbabilityMeasure_map (measurable_ofAtomsPoint n).aemeasurable

theorem iidAtomsLaw_size (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    (iidAtomsLaw μ n).map size = Measure.dirac n := by
  rw [iidAtomsLaw, Measure.map_map measurable_size (measurable_ofAtomsPoint n)]
  simp only [Function.comp_def, size_ofAtomsPoint]
  simp

/-- The literal random atomic measure with a Poisson number of iid locations. -/
def law (r : ℝ≥0) (μ : Measure E) : Measure (PointMeasure E) :=
  Measure.sum (fun n ↦ poissonMeasure r {n} • iidAtomsLaw μ n)

theorem poisson_weights_sum (r : ℝ≥0) : ∑' n : ℕ, poissonMeasure r {n} = 1 := by
  simpa only [Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one, measure_univ]
    using congrArg (fun ν : Measure ℕ ↦ ν Set.univ)
    (Measure.sum_smul_dirac (poissonMeasure r))

instance (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (law r μ) := by
  constructor
  simp only [law, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one]
  exact poisson_weights_sum r

/-- The count extracted from the actual random measure has exactly the Poisson law. -/
theorem law_size (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ] :
    (law r μ).map size = poissonMeasure r := by
  rw [law, Measure.map_sum measurable_size.aemeasurable]
  simp only [Measure.map_smul, iidAtomsLaw_size]
  exact Measure.sum_smul_dirac (poissonMeasure r)

omit [SecondCountableTopology E] in
/-- Changing the rate gives a genuine measurable spatial law. -/
theorem measurable_law (μ : Measure E) : Measurable (fun r ↦ law r μ) := by
  apply Measure.measurable_measure.mpr
  intro s hs
  simp only [law, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
  apply Measurable.tsum
  intro n
  exact ((Measure.measurable_coe (measurableSet_singleton n)).comp
    PoissonCountKernel.measurable_poissonMeasure).mul_const _

/-- The actual finite spatial construction as a rate kernel. -/
def rateKernel (μ : Measure E) : Kernel ℝ≥0 (PointMeasure E) :=
  ⟨fun r ↦ law r μ, measurable_law μ⟩

instance (μ : Measure E) [IsProbabilityMeasure μ] : IsMarkovKernel (rateKernel μ) :=
  ⟨fun r ↦ inferInstanceAs (IsProbabilityMeasure (law r μ))⟩

theorem law_lintegral (r : ℝ≥0) (μ : Measure E)
    {F : PointMeasure E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ η, F η ∂law r μ) = ∑' n : ℕ, poissonMeasure r {n} *
      ∫⁻ x : Fin n → E, F (ofAtomsPoint x) ∂Measure.pi (fun _ ↦ μ) := by
  simp only [law, lintegral_sum_measure, lintegral_smul_measure, smul_eq_mul,
    iidAtomsLaw, lintegral_map hF (measurable_ofAtomsPoint _)]

end PerronWright.FinitePoissonPointLaw
