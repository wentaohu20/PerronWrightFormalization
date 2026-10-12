import PerronWright.Probability.BrownianMinimumShiftWrightLaw
import PerronWright.Probability.BrownianEntranceDurationScaling
import PerronWright.Probability.BrownianFactorialDensityDeletion

/-! # The literal completed entrance Poisson weight gives the paper size factor

The actual full-area Wright moments and Poisson exponential cancellation
combine with the complete-duration prefactor. The resulting expression is
exactly the unchanged homogeneous size factor and parabolic exponent in
Chapter 3, at every surplus. No Campbell or Palm identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal Real
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianCompletedExcursionPoissonSizeFactor

open BrownianPathLaw BrownianPathDilationLaw BrownianBridgeCyclicArea
open BrownianParabolicDriftTiltGeometry BrownianMinimumShiftWrightLaw
open BrownianMinimumShiftEntranceIdentification BrownianExcursionTuplePoissonWeights
open BrownianEntranceDurationScaling BrownianFactorialDensityDeletion
open PerronWrightFormulaMainTerm FactorialDensity

theorem sizeFactor_eq_complete_area_prefactor (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    (1/(Real.sqrt (2*Real.pi)*(T : ℝ)*(T : ℝ)*Real.sqrt (T : ℝ)))*
      (((T : ℝ)^(3/2 : ℝ))^r*wrightConstant r) = sizeFactor 1 (T : ℝ) r := by
  have ht : 0 < (T : ℝ) := hT
  have hpow : (T : ℝ)^(5/2 : ℝ) = (T : ℝ)*(T : ℝ)*Real.sqrt (T : ℝ) := by
    rw [show (5/2 : ℝ) = 1+(1+1/2) by norm_num,
      Real.rpow_add ht,Real.rpow_add ht,Real.rpow_one,← Real.sqrt_eq_rpow]
    ring
  unfold sizeFactor
  rw [Real.one_rpow, mul_one,Real.rpow_sub ht,
    show 3*(r : ℝ)/2 = (3/2 : ℝ)*(r : ℝ) by ring,
    Real.rpow_mul_natCast ht.le,hpow]
  ring

theorem actual_duration_entrance_poisson_intensity
    (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    (∫⁻ e : Path,
      ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*(T : ℝ)*(T : ℝ)*Real.sqrt (T : ℝ)))*
        (ENNReal.ofReal (Real.exp (pathArea T e-energy lambda T/2))*
          poissonWeight (Real.toNNReal (pathArea T e)) r)
            ∂BrownianEntranceContinuousRealization.pathLaw T hT) =
      ENNReal.ofReal (Real.exp (-criticalExponent 1 1 lambda (T : ℝ))*sizeFactor 1 (T : ℝ) r) := by
  have hm : Measurable (fun e : Path ↦ ENNReal.ofReal (Real.exp (pathArea T e))*
      poissonWeight (Real.toNNReal (pathArea T e)) r) :=
    ((measurable_pathArea T).exp.ennreal_ofReal).mul
      ((measurable_poissonWeight r).comp (measurable_pathArea T).real_toNNReal)
  have hmoment := actual_minimumShift_tilted_poisson_weight_eq_wrightConstant T hT r
  rw [actual_minimumShiftLaw_eq_entrance] at hmoment
  let c := 1/(Real.sqrt (2*Real.pi)*(T : ℝ)*(T : ℝ)*Real.sqrt (T : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  calc
    _ = ∫⁻ e : Path, ENNReal.ofReal (c*Real.exp (-energy lambda T/2))*
        (ENNReal.ofReal (Real.exp (pathArea T e))*poissonWeight (Real.toNNReal (pathArea T e)) r)
          ∂BrownianEntranceContinuousRealization.pathLaw T hT := by
      apply lintegral_congr
      intro e
      have hexp : ENNReal.ofReal (Real.exp (pathArea T e-energy lambda T/2)) =
          ENNReal.ofReal (Real.exp (-energy lambda T/2))*
            ENNReal.ofReal (Real.exp (pathArea T e)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
        congr 2
        ring
      change ENNReal.ofReal c*(ENNReal.ofReal (Real.exp (pathArea T e-energy lambda T/2))*
        poissonWeight (Real.toNNReal (pathArea T e)) r) = _
      rw [hexp,ENNReal.ofReal_mul hc,mul_assoc]
      ac_rfl
    _ = ENNReal.ofReal (c*Real.exp (-energy lambda T/2))*
        ENNReal.ofReal (((T : ℝ)^(3/2 : ℝ))^r*wrightConstant r) := by
      rw [lintegral_const_mul _ hm,hmoment]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hc (Real.exp_pos _).le),
        energy_eq_twice_criticalExponent]
      congr 1
      have he : -(2*criticalExponent 1 1 lambda (T : ℝ))/2 =
          -criticalExponent 1 1 lambda (T : ℝ) := by ring
      rw [he]
      have hp := sizeFactor_eq_complete_area_prefactor T hT r
      change c*(((T : ℝ)^(3/2 : ℝ))^r*wrightConstant r) = sizeFactor 1 (T : ℝ) r at hp
      rw [show (c*Real.exp (-criticalExponent 1 1 lambda (T : ℝ)))*
          (((T : ℝ)^(3/2 : ℝ))^r*wrightConstant r) =
          Real.exp (-criticalExponent 1 1 lambda (T : ℝ))*
            (c*(((T : ℝ)^(3/2 : ℝ))^r*wrightConstant r)) by ring,hp]

theorem actual_unit_entrance_dilated_poisson_intensity
    (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    (∫⁻ e : Path,
      ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*(T : ℝ)*(T : ℝ)*Real.sqrt (T : ℝ)))*
        (ENNReal.ofReal (Real.exp (pathArea T (brownianDilation T e)-energy lambda T/2))*
          poissonWeight (Real.toNNReal (pathArea T (brownianDilation T e))) r)
            ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) =
      ENNReal.ofReal (Real.exp (-criticalExponent 1 1 lambda (T : ℝ))*sizeFactor 1 (T : ℝ) r) := by
  have hm : Measurable (fun e : Path ↦
      ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*(T : ℝ)*(T : ℝ)*Real.sqrt (T : ℝ)))*
        (ENNReal.ofReal (Real.exp (pathArea T e-energy lambda T/2))*
          poissonWeight (Real.toNNReal (pathArea T e)) r)) :=
    measurable_const.mul (((measurable_pathArea T).sub_const _).exp.ennreal_ofReal.mul
      ((measurable_poissonWeight r).comp (measurable_pathArea T).real_toNNReal))
  rw [← lintegral_duration_scaling T hT _ hm]
  exact actual_duration_entrance_poisson_intensity lambda T hT r

end PerronWright.BrownianCompletedExcursionPoissonSizeFactor
