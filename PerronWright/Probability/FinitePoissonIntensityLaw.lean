import PerronWright.Probability.FinitePoissonPointLaw
import PerronWright.Probability.PoissonFactorialMoments
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Arbitrary genuine finite spatial intensities

Normalization of an actual finite intensity measure supplies iid
locations, including the zero-intensity case.  The resulting actual
random measure has exactly the specified first intensity, proved cell
by cell from the iid construction and the genuine Poisson first moment.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

noncomputable section

namespace PerronWright.FinitePoissonIntensityLaw

open FinitePointMeasureCompact FinitePoissonPointLaw

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [BorelSpace E] [SecondCountableTopology E] [HasOuterApproxClosed E] [Nonempty E]

/-- The actual spatial law at an arbitrary finite intensity measure. -/
def law (ν : FiniteMeasure E) : Measure (PointMeasure E) :=
  FinitePoissonPointLaw.law ν.mass (ν.normalize : Measure E)

instance (ν : FiniteMeasure E) : IsProbabilityMeasure (law ν) := by
  unfold law
  infer_instance

omit [HasOuterApproxClosed E] in
theorem law_size (ν : FiniteMeasure E) :
    (law ν).map size = poissonMeasure ν.mass :=
  FinitePoissonPointLaw.law_size ν.mass (ν.normalize : Measure E)

omit [TopologicalSpace E] [BorelSpace E] [SecondCountableTopology E]
  [HasOuterApproxClosed E] in
theorem intensity_decomposition (ν : FiniteMeasure E) :
    (ν : Measure E) = ν.mass • (ν.normalize : Measure E) := by
  have h := congrArg (fun η : FiniteMeasure E ↦ (η : Measure E))
    ν.self_eq_mass_smul_normalize
  simpa only [FiniteMeasure.toMeasure_smul,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure] using h

omit [Nonempty E] in
theorem iidAtomsLaw_lintegral_eval (μ : Measure E) [IsProbabilityMeasure μ]
    (n : ℕ) {A : Set E} (hA : MeasurableSet A) :
    (∫⁻ η, ((η : FiniteMeasure E) : Measure E) A ∂iidAtomsLaw μ n) = (n : ℝ≥0∞) * μ A := by
  rw [iidAtomsLaw, lintegral_map (FinitePointMeasureMeasurable.measurable_eval hA)
    (measurable_ofAtomsPoint n)]
  simp only [ofAtomsPoint_val, FiniteAtomicPointMeasure.ofAtoms_toMeasure,
    Measure.coe_finsetSum, Finset.sum_apply]
  rw [lintegral_finsetSum Finset.univ
    (f := fun (i : Fin n) (x : Fin n → E) ↦ Measure.dirac (x i) A) (fun i _ ↦
    ((Measure.measurable_coe hA).comp Measure.measurable_dirac).comp (measurable_pi_apply i))]
  have he (i : Fin n) :
      (∫⁻ x : Fin n → E, Measure.dirac (x i) A ∂Measure.pi (fun _ ↦ μ)) = μ A := by
    have hg : Measurable (fun z : E ↦ Measure.dirac z A) :=
      (Measure.measurable_coe hA).comp Measure.measurable_dirac
    rw [(measurePreserving_eval (fun _ : Fin n ↦ μ) i).lintegral_comp hg]
    simp_rw [Measure.dirac_apply' _ hA]
    exact lintegral_indicator_one hA
  simp_rw [he]
  simp

theorem poisson_lintegral_nat (r : ℝ≥0) :
    (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure r) = (r : ℝ≥0∞) := by
  have hi : Integrable (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure r) := by
    simpa only [Nat.descFactorial_one] using PoissonFactorialMoments.integrable_descFactorial r 1
  have he : (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = (r : ℝ) := by
    simpa only [Nat.descFactorial_one, pow_one] using
      PoissonFactorialMoments.integral_descFactorial r 1
  have ho := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun n : ℕ ↦ Nat.cast_nonneg n))
  simpa only [he, ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal] using ho.symm

/-- Every actual Borel cell has exactly the prescribed expected intensity. -/
theorem law_lintegral_eval (ν : FiniteMeasure E) {A : Set E} (hA : MeasurableSet A) :
    (∫⁻ η, ((η : FiniteMeasure E) : Measure E) A ∂law ν) = (ν : Measure E) A := by
  simp only [law, FinitePoissonPointLaw.law, lintegral_sum_measure,
    lintegral_smul_measure, smul_eq_mul, iidAtomsLaw_lintegral_eval _ _ hA]
  simp_rw [← mul_assoc]
  rw [ENNReal.tsum_mul_right]
  have he : (∑' n : ℕ, poissonMeasure ν.mass {n} * (n : ℝ≥0∞)) = (ν.mass : ℝ≥0∞) := by
    rw [← poisson_lintegral_nat ν.mass, lintegral_countable']
    congr 1
    funext n
    exact mul_comm _ _
  rw [he, intensity_decomposition ν, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]

end PerronWright.FinitePoissonIntensityLaw
