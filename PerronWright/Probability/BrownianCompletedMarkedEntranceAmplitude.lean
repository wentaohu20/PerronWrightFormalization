import PerronWright.Probability.BrownianCompletedExcursionPoissonSizeFactor
import PerronWright.Probability.BrownianCompletedMinimumShapeSource

/-! # The completed marked entrance amplitude with arbitrary remaining mass

The actual unit entrance area law supplies the literal paper intensity.
The remaining nonnegative mass may be infinite; the inverse physical
length and entrance-shape prefactor are eliminated exactly.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianCompletedMarkedEntranceAmplitude

open BrownianPathLaw BrownianPathDilationLaw BrownianBridgeCyclicArea
open BrownianParabolicDriftTiltGeometry BrownianCompletedMinimumShapeSource
open BrownianCompletedExcursionPoissonSizeFactor BrownianExcursionTuplePoissonWeights
open FactorialDensity

private theorem shapeFactor_inv_length (T : ℝ≥0) (hT : 0 < T) :
    shapeFactor (T : ℝ)*(T : ℝ≥0∞)⁻¹ =
      ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*(T : ℝ)*(T : ℝ)*Real.sqrt (T : ℝ))) := by
  have ht : 0 < (T : ℝ) := hT
  rw [shapeFactor,← ENNReal.ofReal_coe_nnreal,← ENNReal.ofReal_inv_of_pos ht,
    ← ENNReal.ofReal_mul (by positivity :
      0 ≤ 1/(Real.sqrt (2*Real.pi)*(T : ℝ)*Real.sqrt (T : ℝ)))]
  congr 1
  field_simp

theorem actual_complete_marked_entrance_amplitude
    (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) (J : ℝ≥0∞) :
    shapeFactor (T : ℝ)*
      (∫⁻ e : Path,
        poissonWeight (Real.toNNReal (pathArea T (brownianDilation T e))) r *
          (ENNReal.ofReal (Real.exp (pathArea T (brownianDilation T e)-energy lambda T/2)) *
            ((T : ℝ≥0∞)⁻¹*J))
              ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) =
      ENNReal.ofReal (Real.exp (-criticalExponent 1 1 lambda (T : ℝ))*sizeFactor 1 (T : ℝ) r)*J := by
  let c := ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*(T : ℝ)*(T : ℝ)*Real.sqrt (T : ℝ)))
  let A : Path → ℝ := fun e ↦ pathArea T (brownianDilation T e)
  let F : Path → ℝ≥0∞ := fun e ↦ c*(ENNReal.ofReal (Real.exp (A e-energy lambda T/2))*
    poissonWeight (Real.toNNReal (A e)) r)
  have hA : Measurable A := (measurable_pathArea T).comp (measurable_brownianDilation T)
  have hF : Measurable F := measurable_const.mul
    (((hA.sub_const _).exp.ennreal_ofReal).mul ((measurable_poissonWeight r).comp hA.real_toNNReal))
  calc
    _ = ∫⁻ e : Path, F e*J ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one := by
      rw [← lintegral_const_mul' (shapeFactor (T : ℝ)) _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro e
      change shapeFactor (T : ℝ)*(poissonWeight (Real.toNNReal (A e)) r *
        (ENNReal.ofReal (Real.exp (A e-energy lambda T/2))*((T : ℝ≥0∞)⁻¹*J))) =
          (c*(ENNReal.ofReal (Real.exp (A e-energy lambda T/2))*
            poissonWeight (Real.toNNReal (A e)) r))*J
      have hc : shapeFactor (T : ℝ)*(T : ℝ≥0∞)⁻¹ = c := shapeFactor_inv_length T hT
      rw [← hc]
      ac_rfl
    _ = (∫⁻ e : Path, F e ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one)*J :=
      lintegral_mul_const J hF
    _ = _ := by
      have h := actual_unit_entrance_dilated_poisson_intensity lambda T hT r
      change (∫⁻ e : Path, F e ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) = _ at h
      rw [h]

end PerronWright.BrownianCompletedMarkedEntranceAmplitude
