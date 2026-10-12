import PerronWright.Enumeration.RootedTreeFormalUniqueness
import PerronWright.Analysis.TreeRealComplexBridge
import Mathlib.Analysis.RCLike.ContinuousMap

/-!
# The complex formal rooted-tree equation

This file contains only the algebraic complexification of the already proved
real rooted-tree identity.  It does not use convergence or identify any
analytic Taylor coefficient.
-/

open scoped Classical
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Coefficientwise complexification of a real continuous type profile. -/
def continuousMapComplexifyRingHom : C(S, ℝ) →+* C(S, ℂ) :=
  (ContinuousMap.realToRCLikeStarAlgHom S ℂ).toAlgHom.toRingHom

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem continuousMapComplexifyRingHom_apply (f : C(S, ℝ)) :
    continuousMapComplexifyRingHom f =
      TreeRealComplexBridge.complexify f :=
  rfl

/-- Apply the complex compact-BJR kernel action coefficientwise. -/
def CompactBJRModel.complexKernelActionPowerSeries
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℂ)) :
    PowerSeries C(S, ℂ) :=
  PowerSeries.mk fun n =>
    M.kernel.complexActionCLM M.mu (PowerSeries.coeff n F)

@[simp] theorem CompactBJRModel.complexKernelActionPowerSeries_coeff
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℂ)) (n : ℕ) :
    PowerSeries.coeff n (M.complexKernelActionPowerSeries F) =
      M.kernel.complexActionCLM M.mu (PowerSeries.coeff n F) := by
  simp [CompactBJRModel.complexKernelActionPowerSeries]

theorem CompactBJRModel.complexKernelActionPowerSeries_constantCoeff
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℂ)) :
    PowerSeries.constantCoeff (M.complexKernelActionPowerSeries F) =
      M.kernel.complexActionCLM M.mu (PowerSeries.constantCoeff F) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  exact M.complexKernelActionPowerSeries_coeff F 0

/-- The formal rooted-tree right-hand side over complex type profiles. -/
def CompactBJRModel.complexRootedTreeFormalRHS
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℂ)) :
    PowerSeries C(S, ℂ) :=
  PowerSeries.X *
    (PowerSeries.C
        (continuousMapComplexifyRingHom M.zeroTreeVertexFactor) *
      PowerSeries.subst (M.complexKernelActionPowerSeries F)
        (PowerSeries.exp C(S, ℂ)))

@[simp] theorem CompactBJRModel.complexRootedTreeFormalRHS_coeff_zero
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℂ)) :
    PowerSeries.coeff 0 (M.complexRootedTreeFormalRHS F) = 0 := by
  simp [CompactBJRModel.complexRootedTreeFormalRHS,
    PowerSeries.coeff_zero_X_mul]

/-- Complexification commutes with the coefficientwise kernel action. -/
theorem CompactBJRModel.complexKernelActionPowerSeries_map
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℝ)) :
    M.complexKernelActionPowerSeries
        (PowerSeries.map continuousMapComplexifyRingHom F) =
      PowerSeries.map continuousMapComplexifyRingHom
        (M.kernelActionPowerSeries F) := by
  apply PowerSeries.ext
  intro n
  simp only [M.complexKernelActionPowerSeries_coeff,
    PowerSeries.coeff_map, M.kernelActionPowerSeries_coeff,
    continuousMapComplexifyRingHom_apply]
  exact (TreeRealComplexBridge.complexify_action M
    (PowerSeries.coeff n F)).symm

/-- Mapping the real formal equation coefficientwise to `ℂ` gives the
complex formal equation. -/
theorem CompactBJRModel.map_rootedTreeFormalRHS
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℝ))
    (hF0 : PowerSeries.constantCoeff F = 0) :
    PowerSeries.map continuousMapComplexifyRingHom
        (M.rootedTreeFormalRHS F) =
      M.complexRootedTreeFormalRHS
        (PowerSeries.map continuousMapComplexifyRingHom F) := by
  have hA0 : PowerSeries.constantCoeff
      (M.kernelActionPowerSeries F) = 0 := by
    rw [M.kernelActionPowerSeries_constantCoeff, hF0, map_zero]
  have hA : PowerSeries.HasSubst (M.kernelActionPowerSeries F) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  have hsubst :
      PowerSeries.map continuousMapComplexifyRingHom
          (PowerSeries.subst (M.kernelActionPowerSeries F)
            (PowerSeries.exp C(S, ℝ))) =
        PowerSeries.subst
          (PowerSeries.map continuousMapComplexifyRingHom
            (M.kernelActionPowerSeries F))
          (PowerSeries.exp C(S, ℂ)) := by
    change MvPowerSeries.map continuousMapComplexifyRingHom
        (PowerSeries.subst (M.kernelActionPowerSeries F)
          (PowerSeries.exp C(S, ℝ))) =
      PowerSeries.subst
        (MvPowerSeries.map continuousMapComplexifyRingHom
          (M.kernelActionPowerSeries F))
        (PowerSeries.exp C(S, ℂ))
    rw [PowerSeries.map_subst hA
      (h := continuousMapComplexifyRingHom)
      (PowerSeries.exp C(S, ℝ)), PowerSeries.map_exp]
  unfold CompactBJRModel.rootedTreeFormalRHS
    CompactBJRModel.complexRootedTreeFormalRHS
  rw [map_mul, PowerSeries.map_X, map_mul, PowerSeries.map_C, hsubst,
    M.complexKernelActionPowerSeries_map F]

/-- The actual real labelled-tree series, mapped coefficientwise to complex
type profiles. -/
def CompactBJRModel.complexTypeRootedTreeEGF (M : CompactBJRModel S) :
    PowerSeries C(S, ℂ) :=
  PowerSeries.map continuousMapComplexifyRingHom M.typeRootedTreeEGF

@[simp] theorem CompactBJRModel.complexTypeRootedTreeEGF_coeff
    (M : CompactBJRModel S) (n : ℕ) :
    PowerSeries.coeff n M.complexTypeRootedTreeEGF =
      continuousMapComplexifyRingHom
        (PowerSeries.coeff n M.typeRootedTreeEGF) :=
  rfl

@[simp] theorem CompactBJRModel.complexTypeRootedTreeEGF_constantCoeff
    (M : CompactBJRModel S) :
    PowerSeries.constantCoeff M.complexTypeRootedTreeEGF = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [M.complexTypeRootedTreeEGF_coeff,
    M.typeRootedTreeEGF_coeff_zero, map_zero]

/-- The coefficientwise complexification of the actual labelled-tree series
satisfies the complex formal rooted-tree equation. -/
theorem CompactBJRModel.complexTypeRootedTreeEGF_eq_complexRootedTreeFormalRHS
    (M : CompactBJRModel S) :
    M.complexTypeRootedTreeEGF =
      M.complexRootedTreeFormalRHS M.complexTypeRootedTreeEGF := by
  have hmap := congrArg
    (PowerSeries.map continuousMapComplexifyRingHom)
    M.typeRootedTreeEGF_eq_rootedTreeFormalRHS
  rw [M.map_rootedTreeFormalRHS M.typeRootedTreeEGF
    (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff] using
      M.typeRootedTreeEGF_coeff_zero)] at hmap
  exact hmap

/-- The complexified genuine labelled-tree series is the unique
zero-constant complex formal fixed point. -/
theorem CompactBJRModel.complexRootedTreeFormalRHS_fixedPoint_unique
    (M : CompactBJRModel S) (F : PowerSeries C(S, ℂ))
    (hF0 : PowerSeries.constantCoeff F = 0)
    (hF : F = M.complexRootedTreeFormalRHS F) :
    F = M.complexTypeRootedTreeEGF := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          calc
            PowerSeries.coeff 0 F = 0 := by
              simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hF0
            _ = PowerSeries.coeff 0 M.complexTypeRootedTreeEGF := by
              simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
                M.complexTypeRootedTreeEGF_constantCoeff.symm
      | succ m =>
          let AF := M.complexKernelActionPowerSeries F
          let AT := M.complexKernelActionPowerSeries M.complexTypeRootedTreeEGF
          have hAF0 : PowerSeries.constantCoeff AF = 0 := by
            dsimp only [AF]
            rw [M.complexKernelActionPowerSeries_constantCoeff, hF0, map_zero]
          have hAT0 : PowerSeries.constantCoeff AT = 0 := by
            dsimp only [AT]
            rw [M.complexKernelActionPowerSeries_constantCoeff,
              M.complexTypeRootedTreeEGF_constantCoeff, map_zero]
          have hAcoeff : ∀ k ≤ m,
              PowerSeries.coeff k AF = PowerSeries.coeff k AT := by
            intro k hk
            dsimp only [AF, AT]
            simp only [M.complexKernelActionPowerSeries_coeff]
            rw [ih k (by omega)]
          have hExp := powerSeries_subst_exp_coeff_eq_of_coeff_eq_up_to
            AF AT hAF0 hAT0 m hAcoeff
          have hFn := congrArg (PowerSeries.coeff (m + 1)) hF
          have hTn := congrArg (PowerSeries.coeff (m + 1))
            M.complexTypeRootedTreeEGF_eq_complexRootedTreeFormalRHS
          rw [CompactBJRModel.complexRootedTreeFormalRHS,
            PowerSeries.coeff_succ_X_mul,
            PowerSeries.coeff_C_mul] at hFn hTn
          calc
            PowerSeries.coeff (m + 1) F =
                continuousMapComplexifyRingHom M.zeroTreeVertexFactor *
                  PowerSeries.coeff m
                    (PowerSeries.subst AF (PowerSeries.exp C(S, ℂ))) := by
              simpa only [AF] using hFn
            _ = continuousMapComplexifyRingHom M.zeroTreeVertexFactor *
                  PowerSeries.coeff m
                    (PowerSeries.subst AT (PowerSeries.exp C(S, ℂ))) := by
              rw [hExp]
            _ = PowerSeries.coeff (m + 1) M.complexTypeRootedTreeEGF := by
              simpa only [AT] using hTn.symm

end PerronWright

