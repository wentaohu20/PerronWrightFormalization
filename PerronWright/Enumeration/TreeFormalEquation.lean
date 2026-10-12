import PerronWright.Enumeration.TreeCoefficientSeries
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
Formal-series operators for the rooted-tree equation.  No coefficient
recursion is assumed here: the purpose is to state the eventual finite-tree
identity using the actual coefficientwise kernel action.
-/

noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Apply the actual compact-BJR kernel action coefficientwise to a formal
power series with continuous type profiles. -/
def CompactBJRModel.kernelActionPowerSeries
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℝ)) :
    PowerSeries C(S, ℝ) :=
  PowerSeries.mk fun n => M.kernel.actionCLM M.mu (PowerSeries.coeff n F)

@[simp] theorem CompactBJRModel.kernelActionPowerSeries_coeff
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℝ)) (n : ℕ) :
    PowerSeries.coeff n (M.kernelActionPowerSeries F) =
      M.kernel.actionCLM M.mu (PowerSeries.coeff n F) := by
  simp [CompactBJRModel.kernelActionPowerSeries]

@[simp] theorem CompactBJRModel.kernelActionPowerSeries_zero
    (M : CompactBJRModel S) :
    M.kernelActionPowerSeries 0 = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [M.kernelActionPowerSeries_coeff, map_zero]

theorem CompactBJRModel.kernelActionPowerSeries_add
    (M : CompactBJRModel S) (F G : PowerSeries C(S, ℝ)) :
    M.kernelActionPowerSeries (F + G) =
      M.kernelActionPowerSeries F + M.kernelActionPowerSeries G := by
  apply PowerSeries.ext
  intro n
  simp only [M.kernelActionPowerSeries_coeff, map_add]

theorem CompactBJRModel.kernelActionPowerSeries_constantCoeff
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℝ)) :
    PowerSeries.constantCoeff (M.kernelActionPowerSeries F) =
      M.kernel.actionCLM M.mu (PowerSeries.constantCoeff F) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  exact M.kernelActionPowerSeries_coeff F 0

theorem CompactBJRModel.kernelAction_typeRootedTreeEGF_constantCoeff
    (M : CompactBJRModel S) :
    PowerSeries.constantCoeff
      (M.kernelActionPowerSeries M.typeRootedTreeEGF) = 0 := by
  rw [M.kernelActionPowerSeries_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  rw [M.typeRootedTreeEGF_coeff_zero]
  exact (M.kernel.actionCLM M.mu).map_zero

/-- The formal right-hand side of the type-resolved rooted-tree equation
`T = X exp(-d) exp(KT)`, formed using the actual kernel action and the actual
single-vertex weight. -/
def CompactBJRModel.rootedTreeFormalRHS
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℝ)) :
    PowerSeries C(S, ℝ) :=
  PowerSeries.X *
    (PowerSeries.C M.zeroTreeVertexFactor *
      PowerSeries.subst (M.kernelActionPowerSeries F)
        (PowerSeries.exp C(S, ℝ)))

theorem CompactBJRModel.kernelAction_typeRootedTreeEGF_hasSubst
    (M : CompactBJRModel S) :
    PowerSeries.HasSubst
      (M.kernelActionPowerSeries M.typeRootedTreeEGF) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    M.kernelAction_typeRootedTreeEGF_constantCoeff

@[simp] theorem CompactBJRModel.rootedTreeFormalRHS_coeff_zero
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℝ)) :
    PowerSeries.coeff 0 (M.rootedTreeFormalRHS F) = 0 := by
  simp [CompactBJRModel.rootedTreeFormalRHS,
    PowerSeries.coeff_zero_X_mul]

/-- Substituting a zero-constant kernel series into the formal exponential
still has constant coefficient one. -/
theorem CompactBJRModel.rootedTreeFormalExponential_constantCoeff
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℝ))
    (hF : PowerSeries.constantCoeff (M.kernelActionPowerSeries F) = 0) :
    PowerSeries.constantCoeff
      (PowerSeries.subst (M.kernelActionPowerSeries F)
        (PowerSeries.exp C(S, ℝ))) = 1 := by
  let A := M.kernelActionPowerSeries F
  have hA : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simpa [A] using hF)
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_subst' hA (PowerSeries.exp C(S, ℝ)) 0,
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_pow, show PowerSeries.constantCoeff A = 0 by simpa [A] using hF,
      zero_pow hd]
    simp

/-- The degree-one coefficient of the formal rooted-tree equation is exactly
the genuine single-vertex type profile. -/
theorem CompactBJRModel.rootedTreeFormalRHS_coeff_one
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℝ))
    (hF : PowerSeries.constantCoeff (M.kernelActionPowerSeries F) = 0) :
    PowerSeries.coeff 1 (M.rootedTreeFormalRHS F) =
      M.zeroTreeVertexFactor := by
  rw [show 1 = 0 + 1 by omega,
    CompactBJRModel.rootedTreeFormalRHS,
    PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, PowerSeries.constantCoeff_C,
    M.rootedTreeFormalExponential_constantCoeff F hF]
  simp

end PerronWright
