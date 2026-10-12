import PerronWright.Model.FiniteIrreducibleBJRBridge
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The actual weighted L² realization of the finite matrix

The square-root diagonal coordinates give a constructed isometric
equivalence with the actual Bochner L² space of the atomic probability
measure.  This realizes B1, not B2, from literal matrix criticality.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def continuousToHilbert (M : FiniteIrreducibleModel S) : C(S, ℝ) ≃ₗ[ℝ] M.Hilbert where
  toFun f := M.toHilbert f
  invFun v := ⟨M.toHilbert.symm v, continuous_of_discreteTopology⟩
  left_inv f := by ext a; exact congrFun (M.toHilbert.symm_apply_apply f) a
  right_inv v := M.toHilbert.apply_symm_apply v
  map_add' f g := M.toHilbert.map_add f g
  map_smul' c f := M.toHilbert.map_smul c f

omit [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem continuousToHilbert_symm_apply (M : FiniteIrreducibleModel S)
    (v : M.Hilbert) (a : S) : M.continuousToHilbert.symm v a = v a / M.sqrtWeight a := rfl

def hilbertToL2LinearMap (M : FiniteIrreducibleModel S) : M.Hilbert →ₗ[ℝ] M.bjrModel.L2 :=
  (ContinuousMap.toLp 2 M.measure ℝ).toLinearMap.comp M.continuousToHilbert.symm.toLinearMap

theorem hilbertToL2_inner (M : FiniteIrreducibleModel S) (v w : M.Hilbert) :
    inner ℝ (M.hilbertToL2LinearMap v) (M.hilbertToL2LinearMap w) = inner ℝ v w := by
  change inner ℝ (ContinuousMap.toLp 2 M.measure ℝ (M.continuousToHilbert.symm v))
    (ContinuousMap.toLp 2 M.measure ℝ (M.continuousToHilbert.symm w)) = _
  rw [ContinuousMap.inner_toLp, M.integral_measure, PiLp.inner_apply]
  simp only [conj_trivial, smul_eq_mul, continuousToHilbert_symm_apply, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [← M.sqrtWeight_sq a]
  field_simp [(M.sqrtWeight_pos a).ne']

def hilbertToL2Isometry (M : FiniteIrreducibleModel S) : M.Hilbert →ₗᵢ[ℝ] M.bjrModel.L2 :=
  M.hilbertToL2LinearMap.isometryOfInner (M.hilbertToL2_inner)

theorem hilbertToL2_surjective (M : FiniteIrreducibleModel S) :
    Function.Surjective M.hilbertToL2Isometry := by
  intro v
  let f : C(S, ℝ) := ⟨fun a ↦ v a, continuous_of_discreteTopology⟩
  refine ⟨M.continuousToHilbert f, ?_⟩
  change ContinuousMap.toLp 2 M.measure ℝ
    (M.continuousToHilbert.symm (M.continuousToHilbert f)) = v
  rw [M.continuousToHilbert.symm_apply_apply]
  exact Lp.ext (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) M.measure f)

def l2Equiv (M : FiniteIrreducibleModel S) : M.Hilbert ≃ₗᵢ[ℝ] M.bjrModel.L2 :=
  LinearIsometryEquiv.ofSurjective M.hilbertToL2Isometry M.hilbertToL2_surjective

@[simp] theorem l2Equiv_apply (M : FiniteIrreducibleModel S) (v : M.Hilbert) :
    M.l2Equiv v = ContinuousMap.toLp 2 M.measure ℝ (M.continuousToHilbert.symm v) := rfl

theorem l2Equiv_toHilbert (M : FiniteIrreducibleModel S) (f : C(S, ℝ)) :
    M.l2Equiv (M.toHilbert f) = ContinuousMap.toLp 2 M.measure ℝ f := by
  change M.l2Equiv (M.continuousToHilbert f) = _
  rw [M.l2Equiv_apply, M.continuousToHilbert.symm_apply_apply]

def l2Operator (M : FiniteIrreducibleModel S) : M.bjrModel.L2 →L[ℝ] M.bjrModel.L2 :=
  M.l2Equiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (M.operator.comp M.l2Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem l2Operator_apply (M : FiniteIrreducibleModel S) (v : M.bjrModel.L2) :
    M.l2Operator v = M.l2Equiv (M.operator (M.l2Equiv.symm v)) := rfl

theorem l2Operator_intertwines (M : FiniteIrreducibleModel S) (f : C(S, ℝ)) :
    M.l2Operator (ContinuousMap.toLp 2 M.measure ℝ f) =
      ContinuousMap.toLp 2 M.measure ℝ (M.continuousKernel.action M.measure f) := by
  rw [← M.l2Equiv_toHilbert f, M.l2Operator_apply, M.l2Equiv.symm_apply_apply,
    M.toHilbert_intertwines]
  have he : M.action f = (M.continuousKernel.action M.measure f : S → ℝ) := by
    funext a
    exact (M.continuous_action_apply f a).symm
  rw [he, M.l2Equiv_toHilbert]

theorem l2Operator_associated (M : FiniteIrreducibleModel S) :
    M.bjrModel.IsAssociatedL2Operator M.l2Operator := by
  intro f g
  change inner ℝ (M.l2Operator (ContinuousMap.toLp 2 M.measure ℝ f))
    (ContinuousMap.toLp 2 M.measure ℝ g) =
      ∫ a, g a * M.bjrModel.integralAction f a ∂M.measure
  rw [M.l2Operator_intertwines, M.bjr_integralAction]
  have hi := ContinuousMap.inner_toLp (μ := M.measure)
    (M.continuousKernel.action M.measure f) g
  simp only [conj_trivial] at hi
  refine hi.trans ?_
  apply integral_congr_ae
  filter_upwards [] with a
  rw [M.continuous_action_apply]

theorem l2Operator_isCompact (M : FiniteIrreducibleModel S) :
    IsCompactOperator M.l2Operator :=
  (M.isCompactOperator_operator.comp_clm
    M.l2Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      M.l2Equiv.toContinuousLinearEquiv.toContinuousLinearMap

theorem l2Operator_isSymmetric (M : FiniteIrreducibleModel S) :
    M.l2Operator.toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (M.l2Operator v) w = inner ℝ v (M.l2Operator w)
  rw [M.l2Operator_apply, M.l2Operator_apply]
  have hv : v = M.l2Equiv (M.l2Equiv.symm v) := (M.l2Equiv.apply_symm_apply v).symm
  have hw : w = M.l2Equiv (M.l2Equiv.symm w) := (M.l2Equiv.apply_symm_apply w).symm
  conv_lhs => rw [hw]
  conv_rhs => rw [hv]
  rw [M.l2Equiv.inner_map_map, M.l2Equiv.inner_map_map]
  exact M.isSymmetric_operator _ _

theorem norm_l2Operator (M : FiniteIrreducibleModel S) : ‖M.l2Operator‖ = ‖M.operator‖ := by
  unfold l2Operator
  rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp M.l2Equiv]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv M.operator M.l2Equiv.symm

def b1Witness (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) : M.bjrModel.B1Witness where
  operator := M.l2Operator
  associated := M.l2Operator_associated
  isCompact := M.l2Operator_isCompact
  isSymmetric := M.l2Operator_isSymmetric
  norm_eq_one := (M.norm_l2Operator).trans (M.norm_operator_eq_one hcrit)

theorem bjrModel_b1 (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) : M.bjrModel.B1 :=
  ⟨M.b1Witness hcrit⟩

end PerronWright.FiniteIrreducibleModel
