import PerronWright.Probability.FinitePoissonPointLaw
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Measurability of genuine Poisson iid-position laws

Finite product measurability is proved on the actual generating boxes,
and the iid-atom pushforward and Poisson sum are then measurable.
Both the rate and the actual position distribution may vary. No equality
of weak Borel and Giry sigma algebras is imposed: the output point-measure
space is the already constructed genuine weak-Borel space.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FinitePoissonPositionKernel

open FinitePointMeasureCompact FinitePoissonPointLaw

variable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
  [TopologicalSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [TopologicalSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Genuine finite product probability families are measurable by boxes. -/
theorem measurable_finitePi (μ : S → Measure E) (hμ : Measurable μ)
    [∀ s, IsProbabilityMeasure (μ s)] (n : ℕ) :
    Measurable (fun s ↦ Measure.pi (fun _ : Fin n ↦ μ s)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_pi.symm isPiSystem_pi
  rintro _ ⟨A,hA,rfl⟩
  have hAm : ∀ i : Fin n, MeasurableSet (A i) := fun i ↦ hA i (mem_univ i)
  simp only [Measure.pi_pi]
  exact Finset.measurable_prod Finset.univ (fun i _ ↦
    (Measure.measurable_coe (hAm i)).comp hμ)

/-- The actual iid-position atomic law varies measurably in its input law. -/
theorem measurable_iidAtomsLaw (μ : S → Measure E) (hμ : Measurable μ)
    [∀ s, IsProbabilityMeasure (μ s)] (n : ℕ) :
    Measurable (fun s ↦ iidAtomsLaw (μ s) n) :=
  (Measure.measurable_map ofAtomsPoint (measurable_ofAtomsPoint n)).comp
    (measurable_finitePi μ hμ n)

/-- The proved iid-atom construction is jointly measurable in the actual
rate and the actual spatial location law. -/
theorem measurable_law (r : S → ℝ≥0) (μ : S → Measure E)
    (hr : Measurable r) (hμ : Measurable μ) [∀ s, IsProbabilityMeasure (μ s)] :
    Measurable (fun s ↦ FinitePoissonPointLaw.law (r s) (μ s)) := by
  apply Measure.measurable_measure.mpr
  intro A hA
  simp only [FinitePoissonPointLaw.law,Measure.sum_apply _ hA,
    Measure.smul_apply,smul_eq_mul]
  apply Measurable.tsum
  intro n
  exact (((Measure.measurable_coe (measurableSet_singleton n)).comp
    PoissonCountKernel.measurable_poissonMeasure).comp hr).mul
      ((Measure.measurable_coe hA).comp (measurable_iidAtomsLaw μ hμ n))

def positionKernel (r : S → ℝ≥0) (μ : S → Measure E)
    (hr : Measurable r) (hμ : Measurable μ) [∀ s, IsProbabilityMeasure (μ s)] :
    Kernel S (PointMeasure E) :=
  ⟨fun s ↦ FinitePoissonPointLaw.law (r s) (μ s),measurable_law r μ hr hμ⟩

instance (r : S → ℝ≥0) (μ : S → Measure E)
    (hr : Measurable r) (hμ : Measurable μ) [∀ s, IsProbabilityMeasure (μ s)] :
    IsMarkovKernel (positionKernel r μ hr hμ) :=
  ⟨fun s ↦ inferInstanceAs (IsProbabilityMeasure (FinitePoissonPointLaw.law (r s) (μ s)))⟩

end PerronWright.FinitePoissonPositionKernel
