import PerronWright.Probability.BrownianEntranceAreaScaling
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # Genuine entrance-area duration transform and its Gamma normalization

The scalar heat coefficient is exactly the already used entrance--exit
normalization `(2/T) gaussianPDFReal 0 T 0`. Actual area scaling reduces
its all-positive-order duration transform to the convergent Gamma
integral. No formula for the unit area moment is supplied or asserted.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceAreaGammaTransform

open BrownianPositiveBridgeAreaMomentLimits BrownianEntranceAreaScaling

def boundaryHeatCoefficient (T : ℝ≥0) : ℝ :=
  (2/(T : ℝ))*gaussianPDFReal 0 T 0

theorem boundaryHeatCoefficient_eq_rpow (T : ℝ≥0) (hT : 0 < T) :
    boundaryHeatCoefficient T = (2/Real.sqrt (2*Real.pi))*(T : ℝ)^(-(3/2 : ℝ)) := by
  have ht : (0 : ℝ) < T := hT
  have hp : (T : ℝ)^(-(3/2 : ℝ)) = (T : ℝ)⁻¹*(Real.sqrt (T : ℝ))⁻¹ := by
    rw [show -(3/2 : ℝ) = (-1 : ℝ)+(-(1/2 : ℝ)) by norm_num,
      Real.rpow_add ht,Real.rpow_neg_one,Real.rpow_neg,← Real.sqrt_eq_rpow]
    exact T.coe_nonneg
  unfold boundaryHeatCoefficient gaussianPDFReal
  simp only [sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),neg_zero,zero_div,Real.exp_zero,mul_one]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi),mul_inv_rev,hp]
  simp only [div_eq_mul_inv]
  ring

def momentGammaExponent (n : ℕ) : ℝ := (3*(n : ℝ)-1)/2

theorem momentGammaExponent_pos (n : ℕ) (hn : 0 < n) : 0 < momentGammaExponent n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  dsimp [momentGammaExponent]
  linarith

def boundaryMomentIntegrand (n : ℕ) (p T : ℝ) : ℝ :=
  Real.exp (-p*T)*boundaryHeatCoefficient (Real.toNNReal T)*
    (entranceAreaMoment (Real.toNNReal T) n).toReal

theorem boundaryMomentIntegrand_eq_gamma (n : ℕ) (p T : ℝ) (hT : 0 < T) :
    boundaryMomentIntegrand n p T =
      ((2/Real.sqrt (2*Real.pi))*(entranceAreaMoment 1 n).toReal)*
        (T^(momentGammaExponent n-1)*Real.exp (-p*T)) := by
  have hp : T^(-(3/2 : ℝ))*((T^(3/2 : ℝ))^n) = T^(momentGammaExponent n-1) := by
    rw [← Real.rpow_mul_natCast hT.le,← Real.rpow_add hT]
    congr 1
    dsimp [momentGammaExponent]
    ring
  unfold boundaryMomentIntegrand
  rw [boundaryHeatCoefficient_eq_rpow _ (Real.toNNReal_pos.mpr hT),
    entranceAreaMoment_real_duration_scaling _ (Real.toNNReal_pos.mpr hT) n,
    Real.coe_toNNReal _ hT.le]
  calc
    _ = ((2/Real.sqrt (2*Real.pi))*(entranceAreaMoment 1 n).toReal)*
        ((T^(-(3/2 : ℝ))*((T^(3/2 : ℝ))^n))*Real.exp (-p*T)) := by ring
    _ = _ := by rw [hp]

theorem integrable_gamma_integrand (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 0 < p) :
    Integrable (fun T : ℝ ↦ T^(momentGammaExponent n-1)*Real.exp (-p*T))
      (volume.restrict (Ioi 0)) := by
  by_contra hi
  have he : (∫ T : ℝ in Ioi 0, T^(momentGammaExponent n-1)*Real.exp (-p*T)) =
      (1/p)^(momentGammaExponent n)*Real.Gamma (momentGammaExponent n) := by
    simpa only [← neg_mul] using
      Real.integral_rpow_mul_exp_neg_mul_Ioi (momentGammaExponent_pos n hn) hp
  rw [integral_undef hi] at he
  have hpos : 0 < (1/p)^(momentGammaExponent n)*Real.Gamma (momentGammaExponent n) :=
    mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.Gamma_pos_of_pos (momentGammaExponent_pos n hn))
  linarith

theorem integrable_boundaryMomentIntegrand (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 0 < p) :
    Integrable (boundaryMomentIntegrand n p) (volume.restrict (Ioi 0)) := by
  apply ((integrable_gamma_integrand n hn p hp).const_mul
    ((2/Real.sqrt (2*Real.pi))*(entranceAreaMoment 1 n).toReal)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  exact (boundaryMomentIntegrand_eq_gamma n p T hT).symm

def boundaryMomentTransform (n : ℕ) (p : ℝ) : ℝ :=
  ∫ T : ℝ in Ioi 0, boundaryMomentIntegrand n p T

theorem boundaryMomentTransform_eq_Gamma (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 0 < p) :
    boundaryMomentTransform n p =
      ((2/Real.sqrt (2*Real.pi))*(entranceAreaMoment 1 n).toReal)*
        ((1/p)^(momentGammaExponent n)*Real.Gamma (momentGammaExponent n)) := by
  unfold boundaryMomentTransform
  calc
    _ = ∫ T : ℝ in Ioi 0,
        ((2/Real.sqrt (2*Real.pi))*(entranceAreaMoment 1 n).toReal)*
          (T^(momentGammaExponent n-1)*Real.exp (-p*T)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro T hT
      exact boundaryMomentIntegrand_eq_gamma n p T hT
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [← neg_mul] using
        Real.integral_rpow_mul_exp_neg_mul_Ioi (momentGammaExponent_pos n hn) hp

theorem boundaryMomentIntegrand_nonneg (n : ℕ) (p T : ℝ) :
    0 ≤ boundaryMomentIntegrand n p T := by
  unfold boundaryMomentIntegrand boundaryHeatCoefficient
  exact mul_nonneg (mul_nonneg (Real.exp_nonneg _)
    (mul_nonneg (div_nonneg (by norm_num) (Real.toNNReal T).coe_nonneg)
      (gaussianPDFReal_nonneg _ _ _))) ENNReal.toReal_nonneg

theorem boundaryMomentTransform_lintegral (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 0 < p) :
    (∫⁻ T : ℝ in Ioi 0, ENNReal.ofReal (boundaryMomentIntegrand n p T)) =
      ENNReal.ofReal (((2/Real.sqrt (2*Real.pi))*(entranceAreaMoment 1 n).toReal)*
        ((1/p)^(momentGammaExponent n)*Real.Gamma (momentGammaExponent n))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_boundaryMomentIntegrand n hn p hp)
    (ae_of_all _ (boundaryMomentIntegrand_nonneg n p)),← boundaryMomentTransform,
    boundaryMomentTransform_eq_Gamma n hn p hp]

end PerronWright.BrownianEntranceAreaGammaTransform
