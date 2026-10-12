import PerronWright.Analysis.FiniteIrreducibleAugmented
import PerronWright.Analysis.TreeCritical

/-! Actual finite tree residual and its nondegenerate Perron coefficients. -/

open scoped BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

omit [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem weightedFunctional_one (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    M.weightedFunctional hcrit 1 = 1 := by
  rw [M.weightedFunctional_apply]
  simp only [ContinuousMap.one_apply, mul_one]
  rw [← Complex.ofReal_sum]
  exact congrArg Complex.ofReal (M.perronFunction_average hcrit)

omit [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem normalizedPerronFunctional_one (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    M.normalizedPerronFunctional hcrit 1 = 1 / (M.alpha hcrit : ℂ) := by
  change (M.alpha hcrit : ℂ)⁻¹ * M.weightedFunctional hcrit 1 = _
  rw [M.weightedFunctional_one, mul_one, one_div]

omit [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem normalizedPerronFunctional_one_ne_zero (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) : M.normalizedPerronFunctional hcrit 1 ≠ 0 := by
  rw [M.normalizedPerronFunctional_one]
  exact div_ne_zero one_ne_zero (Complex.ofReal_ne_zero.mpr (M.alpha_pos hcrit).ne')

omit [MeasurableSpace S] [BorelSpace S] in
theorem weightedFunctional_perron_sq (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    M.weightedFunctional hcrit (M.complexPerronFunction hcrit ^ 2) = (M.beta hcrit : ℂ) := by
  rw [M.weightedFunctional_apply]
  simp only [ContinuousMap.pow_apply, complexPerronFunction_apply, beta, average,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [MeasurableSpace S] [BorelSpace S] in
theorem normalizedPerronFunctional_perron_sq (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    M.normalizedPerronFunctional hcrit (M.complexPerronFunction hcrit ^ 2) =
      (M.beta hcrit : ℂ) / (M.alpha hcrit : ℂ) := by
  change (M.alpha hcrit : ℂ)⁻¹ *
    M.weightedFunctional hcrit (M.complexPerronFunction hcrit ^ 2) = _
  rw [M.weightedFunctional_perron_sq, div_eq_mul_inv, mul_comm]

def treeResidual (M : FiniteIrreducibleModel S) := TreeCritical.residual M.bjrModel

theorem treeResidual_analytic (M : FiniteIrreducibleModel S)
    (p : (ℂ × C(S, ℂ)) × C(S, ℂ)) : AnalyticAt ℂ M.treeResidual p :=
  TreeAnalytic.residual_analytic M.bjrModel.kernel M.bjrModel.mu
    (TreeCritical.degree M.bjrModel) p

theorem treeResidual_base (M : FiniteIrreducibleModel S) : M.treeResidual ((1, 0), 1) = 0 :=
  TreeCritical.critical_base M.bjrModel

theorem treeResidual_fderiv_unknown (M : FiniteIrreducibleModel S) :
    fderiv ℂ (fun U : C(S, ℂ) ↦ M.treeResidual ((1, 0), U)) 1 =
      ContinuousLinearMap.id ℂ C(S, ℂ) - M.complexOperator :=
  TreeCritical.critical_fderiv_unknown M.bjrModel

theorem treeResidual_kernel (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (f : C(S, ℂ)) :
    (fderiv ℂ (fun U : C(S, ℂ) ↦ M.treeResidual ((1, 0), U)) 1) f = 0 ↔
      f = M.normalizedPerronFunctional hcrit f • M.complexPerronFunction hcrit := by
  rw [M.treeResidual_fderiv_unknown]
  change f - M.complexOperator f = 0 ↔ _
  constructor
  · intro hf
    exact M.complex_fixed_eq_perronFunctional_smul hcrit f (sub_eq_zero.mp hf).symm
  · intro hf
    rw [hf, map_smul, M.complexPerronFunction_fixed, sub_self]

theorem treeResidual_first_scalar (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    M.normalizedPerronFunctional hcrit
      (-(deriv (fun z : ℂ ↦ M.treeResidual ((z, 0), 1)) 1)) =
      1 / (M.alpha hcrit : ℂ) := by
  rw [show deriv (fun z : ℂ ↦ M.treeResidual ((z, 0), 1)) 1 = -(1 : C(S, ℂ)) from
    TreeCritical.critical_z_deriv M.bjrModel, neg_neg, M.normalizedPerronFunctional_one]

theorem treeResidual_second_scalar (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    M.normalizedPerronFunctional hcrit
      ((fderiv ℂ (fun U : C(S, ℂ) ↦
        (fderiv ℂ (fun V : C(S, ℂ) ↦ M.treeResidual ((1, 0), V)) U)
          (M.complexPerronFunction hcrit)) 1) (M.complexPerronFunction hcrit)) =
      -(M.beta hcrit : ℂ) / (M.alpha hcrit : ℂ) := by
  rw [show ((fderiv ℂ (fun U : C(S, ℂ) ↦
        (fderiv ℂ (fun V : C(S, ℂ) ↦ M.treeResidual ((1, 0), V)) U)
          (M.complexPerronFunction hcrit)) 1) (M.complexPerronFunction hcrit)) =
      -(M.complexOperator (M.complexPerronFunction hcrit) *
        M.complexOperator (M.complexPerronFunction hcrit)) from
    TreeCritical.critical_second_unknown M.bjrModel _ _]
  rw [M.complexPerronFunction_fixed, map_neg, ← pow_two,
    M.normalizedPerronFunctional_perron_sq, neg_div]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem treeResidual_second_scalar_ne_zero (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) : (-(M.beta hcrit : ℂ) / (M.alpha hcrit : ℂ)) ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (M.beta_pos hcrit).ne'))
    (Complex.ofReal_ne_zero.mpr (M.alpha_pos hcrit).ne')

end PerronWright.FiniteIrreducibleModel
