import PerronWright.Probability.BrownianUnderGraphIntensity
import PerronWright.Probability.FinitePoissonIntensityLaplace

/-!
# Constructed spatial Poisson laws under actual bounded reflected paths

For each actual continuous path the intensity is literal planar Lebesgue
measure restricted below its reflected graph.  The random object is an
actual finite integer atomic planar measure, not just an abstract Poisson
count.  Joint random-path kernels and global excursion identification are
separate later steps.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal

noncomputable section

namespace PerronWright.BrownianUnderGraphPoissonLaw

open BrownianPathLaw BrownianReflectedAreaCounts BrownianUnderGraphIntensity
open FinitePointMeasureCompact FinitePoissonPointLaplace

/-- Literal unit planar intensity under the actual reflected graph. -/
def intensity (lambda : ℝ) (a b : ℝ≥0) (f : Path) : FiniteMeasure (ℝ × ℝ) :=
  ⟨volume.restrict (region lambda a b f),
    isFiniteMeasure_restrict.mpr (volume_region_ne_top lambda a b f)⟩

theorem intensity_mass (lambda : ℝ) (a b : ℝ≥0) (f : Path) :
    (intensity lambda a b f).mass = area lambda a b f := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  change volume.restrict (region lambda a b f) Set.univ = (area lambda a b f : ℝ≥0∞)
  rw [Measure.restrict_apply_univ, volume_region]
  rw [← coe_area lambda a b f, ENNReal.ofReal_coe_nnreal]

/-- A genuine finite random planar point measure for every actual path. -/
def law (lambda : ℝ) (a b : ℝ≥0) (f : Path) : Measure (PointMeasure (ℝ × ℝ)) :=
  FinitePoissonIntensityLaw.law (intensity lambda a b f)

instance (lambda : ℝ) (a b : ℝ≥0) (f : Path) : IsProbabilityMeasure (law lambda a b f) := by
  unfold law
  infer_instance

/-- Actual planar atoms have the Poisson count with the genuine path area. -/
theorem law_size (lambda : ℝ) (a b : ℝ≥0) (f : Path) :
    (law lambda a b f).map size = poissonMeasure (area lambda a b f) := by
  rw [law, FinitePoissonIntensityLaw.law_size, intensity_mass]

/-- The expected number in every Borel cell is its literal unit planar area. -/
theorem law_lintegral_eval (lambda : ℝ) (a b : ℝ≥0) (f : Path)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    (∫⁻ η, ((η : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) A ∂law lambda a b f) =
      volume (A ∩ region lambda a b f) := by
  rw [law, FinitePoissonIntensityLaw.law_lintegral_eval _ hA]
  exact Measure.restrict_apply hA

/-- Exact spatial Laplace functional against the real under-graph intensity. -/
theorem law_laplace (lambda : ℝ) (a b : ℝ≥0) (f : Path)
    {F : (ℝ × ℝ) → ℝ≥0} (hF : Measurable F) :
    (∫⁻ η, laplace F η ∂law lambda a b f) = ENNReal.ofReal
      (Real.exp ((∫⁻ z in region lambda a b f, expNeg (F z)).toReal -
        (area lambda a b f : ℝ))) := by
  rw [law, FinitePoissonIntensityLaplace.law_laplace _ hF, intensity_mass]
  rfl

end PerronWright.BrownianUnderGraphPoissonLaw
