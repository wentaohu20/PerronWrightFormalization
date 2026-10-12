import PerronWright.Probability.BrownianEntranceAreaDurationLaplace
import PerronWright.Probability.BrownianEntranceLaplaceStateIntegral
import PerronWright.Probability.BrownianBoundaryGammaWrightIdentification

/-! # Genuine all-order entrance area moments are the literal Wright constants

The actual time-cube and Green-chain proofs identify the true Gamma
duration transform with the actual boundary-polynomial slope. Its proved
literal connected compensation normalization gives every Wright constant;
neither a moment identity nor an Airy transform is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianEntranceAreaWrightMoments

open BrownianEntranceAreaDurationLaplace BrownianEntranceAreaOrderedIntegral
open BrownianEntranceAreaGammaTransform BrownianPositiveBridgeAreaMomentLimits
open BrownianEntranceLaplaceStateIntegral BrownianBoundaryGammaWrightIdentification
open BrownianKilledBoundaryPolynomial PerronWrightFormulaMainTerm
open BrownianEntranceAreaScaling

theorem actual_entrance_gamma_eq_initial_slope (n : ℕ) (hn : 0 < n)
    (p : ℝ) (hp : 0 < p) :
    ENNReal.ofReal (((2/Real.sqrt (2*Real.pi))*(entranceAreaMoment 1 n).toReal)*
        ((1/p)^(momentGammaExponent n)*Real.Gamma (momentGammaExponent n))) =
      ENNReal.ofReal ((boundaryPolynomial n (Real.sqrt (2*p))).derivative.eval 0) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [← boundaryMomentTransform_lintegral (n+1) (by omega) p hp]
    calc
      _ = ∫⁻ T : ℝ in Ioi 0, heatLaplaceWeight p T*
          entranceAreaMoment (Real.toNNReal T) (n+1) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
        exact ofReal_boundaryMomentIntegrand n p T hT
      _ = _ := by
        rw [actual_entrance_duration_laplace n p hp]
        exact factorial_transformed_stateIntegral_ofReal_product_eq_initial_slope n p hp

theorem actual_entrance_gamma_half (n : ℕ) (hn : 0 < n) :
    ((2/Real.sqrt (2*Real.pi))*(entranceAreaMoment 1 n).toReal)*
      (Real.sqrt 2^(3*n-1)*Real.Gamma (momentGammaExponent n)) =
        (boundaryPolynomial n 1).derivative.eval 0 := by
  have he := actual_entrance_gamma_eq_initial_slope n hn (1/2) (by norm_num)
  have hs : Real.sqrt (2*(1/2 : ℝ)) = 1 := by norm_num
  rw [hs,half_parameter_gamma_power n hn] at he
  have hc : 0 ≤ ((2/Real.sqrt (2*Real.pi))*(entranceAreaMoment 1 n).toReal)*
      (Real.sqrt 2^(3*n-1)*Real.Gamma (momentGammaExponent n)) := by
    have hG := Real.Gamma_pos_of_pos (momentGammaExponent_pos n hn)
    positivity
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal hc,
    ENNReal.toReal_ofReal (boundaryPolynomial_positive_initial_slope n hn).le] at hr
  exact hr

theorem entranceAreaMoment_unit_div_factorial_eq_wrightConstant (n : ℕ) :
    (entranceAreaMoment 1 n).toReal/(n.factorial : ℝ) = wrightConstant n := by
  cases n with
  | zero => simp [entranceAreaMoment]
  | succ n =>
    have hn : 0 < n+1 := by omega
    have he := actual_entrance_gamma_half (n+1) hn
    rw [← gammaNormalizedInitialSlope_eq_wrightConstant (n+1) hn]
    unfold gammaNormalizedInitialSlope
    rw [← he]
    have hroot : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
    have hfac : ((n+1).factorial : ℝ) ≠ 0 := by positivity
    have hpow : Real.sqrt 2^(3*(n+1)-1) ≠ 0 := by positivity
    have hG : Real.Gamma (momentGammaExponent (n+1)) ≠ 0 :=
      (Real.Gamma_pos_of_pos (momentGammaExponent_pos (n+1) hn)).ne'
    field_simp [hroot,hfac,hpow,hG]

theorem entranceAreaMoment_unit_eq_factorial_mul_wrightConstant (n : ℕ) :
    (entranceAreaMoment 1 n).toReal = (n.factorial : ℝ)*wrightConstant n := by
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have h := entranceAreaMoment_unit_div_factorial_eq_wrightConstant n
  exact (div_eq_iff hfac).mp h |>.trans (mul_comm _ _)

theorem entranceAreaMoment_duration_eq_wrightConstant (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (entranceAreaMoment T n).toReal =
      ((T : ℝ)^(3/2 : ℝ))^n*(n.factorial : ℝ)*wrightConstant n := by
  rw [entranceAreaMoment_real_duration_scaling T hT n,
    entranceAreaMoment_unit_eq_factorial_mul_wrightConstant]
  exact (mul_assoc _ _ _).symm

end PerronWright.BrownianEntranceAreaWrightMoments
