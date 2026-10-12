import PerronWright.Probability.BrownianBoundaryLiteralConnectedCompensation
import PerronWright.Probability.BrownianEntranceAreaGammaTransform

/-! # Exact Gamma normalization of the actual slopes is Wright's constant

Only the already proved literal connected compensation identity and
Gamma's functional equation are used. This is the algebraic normalization
needed after the genuine entrance-duration transform has been identified.
-/

open Polynomial
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBoundaryGammaWrightIdentification

open BrownianBoundaryLiteralConnectedCompensation BrownianBoundarySeriesInitialSlope
open BrownianBoundaryWrightCoefficients BrownianKilledBoundaryPolynomial
open BrownianEntranceAreaGammaTransform GraphCore

theorem boundaryPolynomial_one_initial_slope : (boundaryPolynomial 1 1).derivative.eval 0 = 1 := by
  have h := actual_slope_eq_logCoefficient 0
  norm_num [logCoefficient_one] at h
  exact h

def gammaNormalizedInitialSlope (n : ℕ) : ℝ :=
  (Real.sqrt (2*Real.pi)/(2*(n.factorial : ℝ)*Real.Gamma (momentGammaExponent n)))*
    (Real.sqrt 2^(3*n-1))⁻¹*(boundaryPolynomial n 1).derivative.eval 0

theorem gammaNormalizedInitialSlope_one :
    gammaNormalizedInitialSlope 1 = PerronWrightFormulaMainTerm.wrightConstant 1 := by
  unfold gammaNormalizedInitialSlope
  rw [boundaryPolynomial_one_initial_slope]
  norm_num [momentGammaExponent,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2),
    PerronWrightFormulaMainTerm.wrightConstant_one,
    UnicyclicPerronWrightFormula.unicyclicWrightConstant]
  ring

theorem gammaNormalizedInitialSlope_succ_succ (ell : ℕ) :
    gammaNormalizedInitialSlope (ell+2) = PerronWrightFormulaMainTerm.wrightConstant (ell+2) := by
  have hslope := actual_boundary_slope_eq_literal_connected_compensation (ell+1) (by omega)
  have hindex : ell+1+1 = ell+2 := by omega
  rw [hindex] at hslope
  let a : ℝ := 3*((ell+1 : ℕ) : ℝ)/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hGamma : Real.Gamma (momentGammaExponent (ell+2)) = a*Real.Gamma a := by
    rw [show momentGammaExponent (ell+2) = a+1 by dsimp [momentGammaExponent,a]; push_cast; ring]
    exact Real.Gamma_add_one ha.ne'
  have hpower : Real.sqrt 2^(3*(ell+2)-1) = Real.sqrt 2^(3*(ell+1))*2 := by
    rw [show 3*(ell+2)-1 = 3*(ell+1)+2 by omega,pow_add,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
  have hf : ((ell+2).factorial : ℝ) ≠ 0 := by positivity
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hpow : Real.sqrt 2^(3*(ell+1)) ≠ 0 := by positivity
  unfold gammaNormalizedInitialSlope
  rw [hslope,hGamma,hpower,wrightConstant_eq_literal_connectedCompensation]
  change (Real.sqrt (2*Real.pi)/(2*((ell+2).factorial : ℝ)*(a*Real.Gamma a)))*
    (Real.sqrt 2^(3*(ell+1))*2)⁻¹*
    (6*((ell+1 : ℕ) : ℝ)*((ell+2).factorial : ℝ)*connectedCubicCompensation (ell+1)) =
    (Real.sqrt (2*Real.pi)/Real.Gamma a)*(Real.sqrt 2^(3*(ell+1)))⁻¹*
      connectedCubicCompensation (ell+1)
  field_simp
  dsimp [a]
  ring

theorem half_parameter_gamma_power (n : ℕ) (hn : 0 < n) :
    (1/(1/2 : ℝ))^(momentGammaExponent n) = Real.sqrt 2^(3*n-1) := by
  norm_num only [one_div_div]
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 2)]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ 3*n)]
  dsimp [momentGammaExponent]
  push_cast
  ring

theorem gammaNormalizedInitialSlope_eq_wrightConstant (n : ℕ) (hn : 0 < n) :
    gammaNormalizedInitialSlope n = PerronWrightFormulaMainTerm.wrightConstant n := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => exact gammaNormalizedInitialSlope_one
    | succ n => exact gammaNormalizedInitialSlope_succ_succ n

theorem boundaryPolynomial_positive_initial_slope (n : ℕ) (hn : 0 < n) :
    0 < (boundaryPolynomial n 1).derivative.eval 0 := by
  have hpos : 0 < gammaNormalizedInitialSlope n := by
    rw [gammaNormalizedInitialSlope_eq_wrightConstant n hn]
    exact PerronWrightFormulaMainTerm.wrightConstant_pos n
  have hc : 0 <
      (Real.sqrt (2*Real.pi)/(2*(n.factorial : ℝ)*Real.Gamma (momentGammaExponent n)))*
        (Real.sqrt 2^(3*n-1))⁻¹ := by
    have hG := Real.Gamma_pos_of_pos (momentGammaExponent_pos n hn)
    positivity
  unfold gammaNormalizedInitialSlope at hpos
  by_contra hbad
  have hnpos : (boundaryPolynomial n 1).derivative.eval 0 ≤ 0 := le_of_not_gt hbad
  exact not_le_of_gt hpos (mul_nonpos_of_nonneg_of_nonpos hc.le hnpos)

end PerronWright.BrownianBoundaryGammaWrightIdentification
