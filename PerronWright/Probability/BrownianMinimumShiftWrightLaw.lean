import PerronWright.Probability.BrownianMinimumShiftEntranceIdentification
import PerronWright.Probability.BrownianPositiveBridgeAreaTiltedTransfer
import PerronWright.Probability.BrownianEntranceAreaWrightGeneratingFunction
import PerronWright.Probability.BrownianExcursionTuplePoissonWeights

/-! # Literal Wright moments and Poisson weights of the actual minimum shift

The genuine equality of continuous-path laws transports the proved entrance
moment and exponential-series identities to the actual cyclic minimum
transform. Area tilt cancels the literal full-area Poisson exponential,
leaving the unchanged enumerative Wright constant at every surplus.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianMinimumShiftWrightLaw

open BrownianPathLaw BrownianBridgeCyclicArea BrownianBridgeMinimumShift
open BrownianMinimumShiftEntranceIdentification BrownianPositiveBridgeAreaLawIdentification
open BrownianPositiveBridgeAreaTiltedTransfer BrownianPositiveBridgeAreaExponentialTails
open BrownianEntranceAreaWrightGeneratingFunction PerronWrightFormulaMainTerm
open BrownianExcursionTuplePoissonWeights

theorem actual_minimumShift_area_pow_integrable (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    Integrable (fun f : Path ↦ pathArea T f^r) (minimumShiftLaw T hT) := by
  rw [actual_minimumShiftLaw_eq_entrance]
  exact entrance_area_pow_integrable T hT r

theorem actual_minimumShift_area_moment_eq_wrightConstant (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    (∫ f : Path, pathArea T f^r ∂minimumShiftLaw T hT) =
      ((T : ℝ)^(3/2 : ℝ))^r*(r.factorial : ℝ)*wrightConstant r := by
  rw [actual_minimumShiftLaw_eq_entrance]
  exact actual_entrance_area_real_moment_eq_wrightConstant T hT r

theorem actual_minimumShift_area_exp_integrable (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    Integrable (fun f : Path ↦ Real.exp (u*pathArea T f)) (minimumShiftLaw T hT) := by
  rw [actual_minimumShiftLaw_eq_entrance]
  exact entrance_area_exp_integrable T hT u

theorem hasSum_actual_minimumShift_area_mgf_wright (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    HasSum (fun r : ℕ ↦ wrightConstant r*(u*(T : ℝ)^(3/2 : ℝ))^r)
      (∫ f : Path, Real.exp (u*pathArea T f) ∂minimumShiftLaw T hT) := by
  rw [actual_minimumShiftLaw_eq_entrance]
  exact hasSum_actual_entrance_area_mgf_wright T hT u

theorem actual_minimumShift_area_mgf_eq_wright_series (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (∫ f : Path, Real.exp (u*pathArea T f) ∂minimumShiftLaw T hT) =
      ∑' r : ℕ, wrightConstant r*(u*(T : ℝ)^(3/2 : ℝ))^r :=
  (hasSum_actual_minimumShift_area_mgf_wright T hT u).tsum_eq.symm

theorem actual_minimumShift_area_tilt_eq_entrance (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (minimumShiftLaw T hT).tilted (fun f ↦ u*pathArea T f) =
      (BrownianEntranceContinuousRealization.pathLaw T hT).tilted (fun f ↦ u*pathArea T f) := by
  rw [actual_minimumShiftLaw_eq_entrance]

theorem actual_minimumShift_area_tilt_isProbability (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    IsProbabilityMeasure ((minimumShiftLaw T hT).tilted (fun f ↦ u*pathArea T f)) := by
  rw [actual_minimumShift_area_tilt_eq_entrance]
  exact entrance_area_tilt_isProbability T hT u

theorem poissonWeight_exp_cancel (A : ℝ) (hA : 0 ≤ A) (r : ℕ) :
    ENNReal.ofReal (Real.exp A)*poissonWeight (Real.toNNReal A) r =
      ENNReal.ofReal (A^r/(r.factorial : ℝ)) := by
  rw [poissonWeight,Real.coe_toNNReal A hA,← ENNReal.ofReal_mul (Real.exp_pos A).le]
  congr 1
  rw [mul_div_assoc,← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]

theorem actual_minimumShift_tilted_poisson_weight_eq_wrightConstant
    (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    (∫⁻ f : Path, ENNReal.ofReal (Real.exp (pathArea T f))*
      poissonWeight (Real.toNNReal (pathArea T f)) r ∂minimumShiftLaw T hT) =
        ENNReal.ofReal (((T : ℝ)^(3/2 : ℝ))^r*wrightConstant r) := by
  have hn : ∀ᵐ f ∂minimumShiftLaw T hT, 0 ≤ pathArea T f := by
    rw [actual_minimumShiftLaw_eq_entrance]
    exact ae_entrance_pathArea_nonneg T hT
  have he : (∫⁻ f : Path, ENNReal.ofReal (Real.exp (pathArea T f))*
      poissonWeight (Real.toNNReal (pathArea T f)) r ∂minimumShiftLaw T hT) =
      ∫⁻ f : Path, ENNReal.ofReal (pathArea T f^r/(r.factorial : ℝ)) ∂minimumShiftLaw T hT := by
    apply lintegral_congr_ae
    filter_upwards [hn] with f hf
    exact poissonWeight_exp_cancel _ hf r
  have hi : Integrable (fun f : Path ↦ pathArea T f^r/(r.factorial : ℝ))
      (minimumShiftLaw T hT) := (actual_minimumShift_area_pow_integrable T hT r).div_const _
  have hp : ∀ᵐ f ∂minimumShiftLaw T hT, 0 ≤ pathArea T f^r/(r.factorial : ℝ) := by
    filter_upwards [hn] with f hf
    positivity
  rw [he,← ofReal_integral_eq_lintegral_ofReal hi hp,integral_div,
    actual_minimumShift_area_moment_eq_wrightConstant T hT r]
  congr 1
  have hf : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp

end PerronWright.BrownianMinimumShiftWrightLaw
