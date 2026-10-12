import PerronWright.Probability.FinitePoissonIntensityLaw
import PerronWright.Probability.FinitePoissonPointLaplace

/-!
# Literal finite-intensity spatial Laplace formula

The exponent is written against the specified intensity measure, not
against an abstract location distribution.  Zero intensities are included.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

noncomputable section

namespace PerronWright.FinitePoissonIntensityLaplace

open FinitePointMeasureCompact FinitePoissonPointLaplace

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [BorelSpace E] [SecondCountableTopology E] [HasOuterApproxClosed E] [Nonempty E]

/-- The actual spatial law has the literal Poisson Laplace functional
of its given finite intensity, including intensity zero. -/
theorem law_laplace (ν : FiniteMeasure E) {f : E → ℝ≥0} (hf : Measurable f) :
    (∫⁻ η, laplace f η ∂FinitePoissonIntensityLaw.law ν) =
      ENNReal.ofReal (Real.exp ((∫⁻ z, expNeg (f z) ∂(ν : Measure E)).toReal - (ν.mass : ℝ))) := by
  rw [FinitePoissonIntensityLaw.law, FinitePoissonPointLaplace.law_laplace _ _ hf]
  congr 2
  rw [FinitePoissonIntensityLaw.intensity_decomposition ν, lintegral_smul_measure]
  simp only [ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  ring

end PerronWright.FinitePoissonIntensityLaplace
