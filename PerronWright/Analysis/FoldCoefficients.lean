import PerronWright.Analysis.PerronFunctional
import PerronWright.Analysis.TreeCritical
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory PerronWright

noncomputable section

namespace PerronWright.FoldCoefficients

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem weightedIntegralComplex_one (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    M.weightedIntegralComplex hM 1 = 1 := by
  unfold CompactBJRModel.weightedIntegralComplex
  simp only [ContinuousMap.one_apply, mul_one]
  rw [integral_complex_ofReal, M.perronFunction_integral]
  exact Complex.ofReal_one

theorem normalizedPerronFunctional_one (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    M.normalizedPerronFunctional hM 1 = 1 / (M.alpha hM : ℂ) := by
  simp only [CompactBJRModel.normalizedPerronFunctional, smul_apply, smul_eq_mul,
    CompactBJRModel.weightedIntegralComplexCLM_apply, weightedIntegralComplex_one,
    mul_one, one_div]

theorem weightedIntegralComplex_perron_sq (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    M.weightedIntegralComplex hM (M.complexPerronFunction hM ^ 2) = (M.beta hM : ℂ) := by
  unfold CompactBJRModel.weightedIntegralComplex CompactBJRModel.beta
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ContinuousMap.pow_apply, CompactBJRModel.complexPerronFunction_apply,
    Complex.ofReal_pow]
  ring

theorem normalizedPerronFunctional_perron_sq (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    M.normalizedPerronFunctional hM (M.complexPerronFunction hM ^ 2) =
      (M.beta hM : ℂ) / (M.alpha hM : ℂ) := by
  simp only [CompactBJRModel.normalizedPerronFunctional, smul_apply, smul_eq_mul,
    CompactBJRModel.weightedIntegralComplexCLM_apply, weightedIntegralComplex_perron_sq,
    div_eq_mul_inv, mul_comm]

theorem critical_first_scalar (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    M.normalizedPerronFunctional hM
      (-(deriv (fun z : ℂ ↦ TreeCritical.residual M ((z, 0), 1)) 1)) =
      1 / (M.alpha hM : ℂ) := by
  rw [TreeCritical.critical_z_deriv, neg_neg, normalizedPerronFunctional_one]

theorem critical_second_scalar (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    M.normalizedPerronFunctional hM
      ((fderiv ℂ (fun U : C(S, ℂ) ↦
        (fderiv ℂ (fun V : C(S, ℂ) ↦ TreeCritical.residual M ((1, 0), V)) U)
          (M.complexPerronFunction hM)) 1) (M.complexPerronFunction hM)) =
      -(M.beta hM : ℂ) / (M.alpha hM : ℂ) := by
  rw [TreeCritical.critical_second_unknown]
  simp only [ContinuousKernel.complexActionCLM_apply,
    CompactBJRModel.complexPerronFunction_fixed]
  rw [map_neg, ← pow_two, normalizedPerronFunctional_perron_sq, neg_div]

theorem first_scalar_ne_zero (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (1 / (M.alpha hM : ℂ)) ≠ 0 :=
  div_ne_zero one_ne_zero (Complex.ofReal_ne_zero.mpr (M.alpha_pos hM).ne')

theorem second_scalar_ne_zero (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (-(M.beta hM : ℂ) / (M.alpha hM : ℂ)) ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (M.beta_pos hM).ne'))
    (Complex.ofReal_ne_zero.mpr (M.alpha_pos hM).ne')

def gamma (M : CompactBJRModel S) (hM : M.IsRegularCritical) : ℝ :=
  Real.sqrt (2 / M.beta hM)

theorem gamma_pos (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    0 < gamma M hM := by
  unfold gamma
  exact Real.sqrt_pos.2 (div_pos (by norm_num) (M.beta_pos hM))

theorem gamma_sq (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    gamma M hM ^ 2 = 2 / M.beta hM := by
  unfold gamma
  exact Real.sq_sqrt (div_nonneg (by norm_num) (M.beta_pos hM).le)

theorem gamma_sq_mul_beta (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    gamma M hM ^ 2 * M.beta hM = 2 := by
  rw [gamma_sq, div_mul_cancel₀ _ (M.beta_pos hM).ne']

theorem gamma_fold_balance (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    1 / M.alpha hM + (gamma M hM ^ 2 / 2) * (-M.beta hM / M.alpha hM) = 0 := by
  rw [gamma_sq]
  field_simp [(M.alpha_pos hM).ne', (M.beta_pos hM).ne']
  ring

theorem gamma_fold_balance_complex (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    1 / (M.alpha hM : ℂ) + ((gamma M hM : ℂ) ^ 2 / 2) *
      (-(M.beta hM : ℂ) / (M.alpha hM : ℂ)) = 0 := by
  exact_mod_cast gamma_fold_balance M hM

end PerronWright.FoldCoefficients

