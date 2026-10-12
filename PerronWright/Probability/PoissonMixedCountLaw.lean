import PerronWright.Probability.PoissonCountKernel
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Actual random-rate independent Poisson counts

For a genuine source probability measure and a measurable finite vector of
rates, the composition-product constructs a genuine joint law of the
source and counts. Its source marginal and exact mixed count probability
are proved directly. This is infrastructure for excursion areas, not a
postulated spatial Poisson process or an excursion law.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ProbabilityTheory NNReal ENNReal

noncomputable section

namespace PerronWright.PoissonMixedCountLaw

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- Actual rate substitution in the proved finite independent Poisson kernel. -/
def rateKernel (A : Ω → ι → ℝ≥0) (hA : Measurable A) : Kernel Ω (ι → ℕ) :=
  ⟨fun x ↦ PoissonCountKernel.finiteCountLaw (A x),
    PoissonCountKernel.measurable_finiteCountLaw.comp hA⟩

instance (A : Ω → ι → ℝ≥0) (hA : Measurable A) : IsMarkovKernel (rateKernel A hA) :=
  ⟨fun x ↦ inferInstanceAs (IsProbabilityMeasure (PoissonCountKernel.finiteCountLaw (A x)))⟩

/-- A constructed joint source/count law, not an assumed conditional distribution. -/
def law (μ : Measure Ω) (A : Ω → ι → ℝ≥0) (hA : Measurable A) :
    Measure (Ω × (ι → ℕ)) := μ ⊗ₘ rateKernel A hA

instance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ι → ℝ≥0) (hA : Measurable A) : IsProbabilityMeasure (law μ A hA) := by
  unfold law
  infer_instance

/-- Adding actual random Poisson counts leaves the source law unchanged. -/
theorem law_source_marginal (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ι → ℝ≥0) (hA : Measurable A) :
    (law μ A hA).map Prod.fst = μ :=
  Measure.fst_compProd μ (rateKernel A hA)

/-- Exact simultaneous count probabilities conditional on any source event. -/
theorem law_source_count_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ι → ℝ≥0) (hA : Measurable A)
    (s : Set Ω) (hs : MeasurableSet s) (n : ι → ℕ) :
    law μ A hA (s ×ˢ {n}) = ∫⁻ x in s, ∏ i, ENNReal.ofReal
      (Real.exp (-(A x i : ℝ)) * (A x i : ℝ) ^ n i / ((n i).factorial : ℝ)) ∂μ := by
  rw [law, Measure.compProd_apply_prod hs (measurableSet_singleton n)]
  simp only [rateKernel, Kernel.coe_mk, PoissonCountKernel.finiteCountLaw_singleton]

theorem law_count_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ι → ℝ≥0) (hA : Measurable A) (n : ι → ℕ) :
    law μ A hA (Prod.snd ⁻¹' {n}) = ∫⁻ x, ∏ i, ENNReal.ofReal
      (Real.exp (-(A x i : ℝ)) * (A x i : ℝ) ^ n i / ((n i).factorial : ℝ)) ∂μ := by
  have he : (Prod.snd ⁻¹' {n} : Set (Ω × (ι → ℕ))) = Set.univ ×ˢ {n} := by
    ext p
    simp
  rw [he, law_source_count_event μ A hA Set.univ MeasurableSet.univ n, Measure.restrict_univ]

end PerronWright.PoissonMixedCountLaw
