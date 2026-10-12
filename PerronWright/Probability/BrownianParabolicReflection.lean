import PerronWright.Probability.BrownianContinuousModification
import PerronWright.Probability.ContinuousPathReflection

/-!
# Parabolic reflection of the genuinely constructed Gaussian process

The sampled process and its almost-sure continuous modification are
already constructed. This file applies the proved literal running-minimum
operation to those paths, simultaneously for every critical parameter.
It does not assert excursion enumeration, Poisson marking, or the Aldous
factorial-density identity.
-/

open MeasureTheory Filter Topology
open scoped NNReal

noncomputable section

namespace PerronWright.BrownianParabolicReflection

open BrownianGaussianSkeleton BrownianContinuousModification ContinuousPathReflection

def drift (lambda : ℝ) (t : ℝ≥0) (x : ℕ → ℝ) : ℝ :=
  parabolicDrift lambda (fun s ↦ process s x) t

def reflection (lambda : ℝ) (t : ℝ≥0) (x : ℕ → ℝ) : ℝ :=
  reflected (fun s ↦ drift lambda s x) t

theorem drift_formula (lambda : ℝ) (t : ℝ≥0) (x : ℕ → ℝ) :
    drift lambda t x = process t x + lambda * (t : ℝ) - (t : ℝ) ^ 2 / 2 := rfl

theorem reflection_formula (lambda : ℝ) (t : ℝ≥0) (x : ℕ → ℝ) :
    reflection lambda t x = drift lambda t x -
      sInf ((fun s ↦ drift lambda s x) '' Set.Icc 0 t) := rfl

/-- One actual full-measure set works for every drift parameter. The
running infimum is over the literal interval, not an assumed reflection. -/
theorem ae_all_parameter_reflection_properties :
    ∀ᵐ x ∂rationalLaw, ∀ lambda : ℝ,
      Continuous (fun t ↦ reflection lambda t x) ∧
      (∀ t : ℝ≥0, 0 ≤ reflection lambda t x) ∧
      IsOpen {t : ℝ≥0 | 0 < reflection lambda t x} := by
  filter_upwards [ae_continuous_process] with x hx
  intro lambda
  exact reflected_parabolic_properties hx lambda

theorem ae_continuous_drift (lambda : ℝ) :
    ∀ᵐ x ∂rationalLaw, Continuous (fun t ↦ drift lambda t x) := by
  filter_upwards [ae_continuous_process] with x hx
  exact continuous_parabolicDrift hx lambda

theorem aemeasurable_drift (lambda : ℝ) (t : ℝ≥0) :
    AEMeasurable (drift lambda t) rationalLaw := by
  exact ((aemeasurable_process t).add aemeasurable_const).sub aemeasurable_const

@[simp] theorem reflection_zero (lambda : ℝ) (x : ℕ → ℝ) :
    reflection lambda 0 x = 0 := reflected_zero _

theorem drift_zero_ae_eq_zero (lambda : ℝ) :
    ∀ᵐ x ∂rationalLaw, drift lambda 0 x = 0 := by
  filter_upwards [process_zero_ae_eq_zero] with x hx
  simp only [drift_formula, NNReal.coe_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_div, add_zero, sub_zero, hx]

end PerronWright.BrownianParabolicReflection
