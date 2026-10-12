import PerronWright.Kernel.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrating continuous kernels

The constructions here keep the integral in the Banach space `C(S, ℝ)`.
This makes continuity of the degree function and of the integral-kernel action
part of the construction, rather than a separate pointwise argument.
-/

open MeasureTheory

noncomputable section

namespace PerronWright
namespace ContinuousKernel

variable {S : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The continuous family of columns `y ↦ (x ↦ κ(x,y))`. -/
def columns (k : ContinuousKernel S) : C(S, C(S, ℝ)) :=
  (k.toContinuousMap.comp (ContinuousMap.prodSwap : C(S × S, S × S))).curry

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem columns_apply (k : ContinuousKernel S) (y x : S) :
    k.columns y x = k x y :=
  rfl

/-- The continuous family of rows `x ↦ (y ↦ κ(x,y))`. -/
def rows (k : ContinuousKernel S) : C(S, C(S, ℝ)) :=
  k.toContinuousMap.curry

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem rows_apply (k : ContinuousKernel S) (x y : S) :
    k.rows x y = k x y :=
  rfl

theorem integrable_columns (k : ContinuousKernel S) (mu : Measure S)
    [IsFiniteMeasure mu] : Integrable k.columns mu := by
  apply k.columns.continuous.integrable_of_hasCompactSupport
  exact isClosed_closure.isCompact

/-- The degree function bundled as an element of `C(S, ℝ)`. -/
def degreeMap (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu] : C(S, ℝ) :=
  ∫ y, k.columns y ∂mu

@[simp]
theorem degreeMap_apply (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu]
    (x : S) : k.degreeMap mu x = k.degree mu x := by
  rw [degreeMap, ContinuousMap.integral_apply (k.integrable_columns mu) x]
  simp only [columns_apply, degree]

theorem continuous_degree (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu] :
    Continuous (k.degree mu) := by
  have hfun : k.degree mu = (k.degreeMap mu : S → ℝ) := by
    funext x
    exact (k.degreeMap_apply mu x).symm
  rw [hfun]
  exact (k.degreeMap mu).continuous

/-- The `C(S, ℝ)`-valued integrand defining the action of a kernel on a
continuous function. -/
def actionIntegrand (k : ContinuousKernel S) (f : C(S, ℝ)) : C(S, C(S, ℝ)) where
  toFun y := f y • k.columns y
  continuous_toFun := f.continuous.smul k.columns.continuous

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem actionIntegrand_apply (k : ContinuousKernel S) (f : C(S, ℝ)) (y x : S) :
    k.actionIntegrand f y x = k x y * f y := by
  change f y * k x y = k x y * f y
  exact mul_comm _ _

omit [MeasurableSpace S] [BorelSpace S] in
theorem actionIntegrand_add (k : ContinuousKernel S) (f g : C(S, ℝ)) :
    k.actionIntegrand (f + g) = k.actionIntegrand f + k.actionIntegrand g := by
  ext y x
  simp only [actionIntegrand_apply, ContinuousMap.add_apply]
  ring

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
theorem actionIntegrand_smul (k : ContinuousKernel S) (c : ℝ) (f : C(S, ℝ)) :
    k.actionIntegrand (c • f) = c • k.actionIntegrand f := by
  ext y x
  simp only [actionIntegrand_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

omit [MeasurableSpace S] [BorelSpace S] in
theorem norm_columns_le (k : ContinuousKernel S) (y : S) :
    ‖k.columns y‖ ≤ ‖k.toContinuousMap‖ := by
  apply (ContinuousMap.norm_le (k.columns y) (norm_nonneg _)).2
  intro x
  simpa only [columns_apply] using k.toContinuousMap.norm_coe_le_norm (x, y)

omit [MeasurableSpace S] [BorelSpace S] in
theorem norm_actionIntegrand_le (k : ContinuousKernel S) (f : C(S, ℝ)) (y : S) :
    ‖k.actionIntegrand f y‖ ≤ ‖k.toContinuousMap‖ * ‖f‖ := by
  change ‖f y • k.columns y‖ ≤ ‖k.toContinuousMap‖ * ‖f‖
  rw [norm_smul]
  calc
    ‖f y‖ * ‖k.columns y‖ ≤ ‖f‖ * ‖k.toContinuousMap‖ := by
      gcongr
      · exact f.norm_coe_le_norm y
      · exact k.norm_columns_le y
    _ = ‖k.toContinuousMap‖ * ‖f‖ := mul_comm _ _

theorem integrable_actionIntegrand (k : ContinuousKernel S) (mu : Measure S)
    [IsFiniteMeasure mu] (f : C(S, ℝ)) : Integrable (k.actionIntegrand f) mu := by
  apply (k.actionIntegrand f).continuous.integrable_of_hasCompactSupport
  exact isClosed_closure.isCompact

/-- The integral-kernel action, before bundling it as a continuous linear map. -/
def action (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu]
    (f : C(S, ℝ)) : C(S, ℝ) :=
  ∫ y, k.actionIntegrand f y ∂mu

@[simp]
theorem action_apply (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu]
    (f : C(S, ℝ)) (x : S) :
    k.action mu f x = ∫ y, k x y * f y ∂mu := by
  rw [action, ContinuousMap.integral_apply (k.integrable_actionIntegrand mu f) x]
  simp only [actionIntegrand_apply]

theorem action_add (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu]
    (f g : C(S, ℝ)) : k.action mu (f + g) = k.action mu f + k.action mu g := by
  unfold action
  rw [actionIntegrand_add]
  change (∫ y, k.actionIntegrand f y + k.actionIntegrand g y ∂mu) =
    (∫ y, k.actionIntegrand f y ∂mu) + ∫ y, k.actionIntegrand g y ∂mu
  exact integral_add (k.integrable_actionIntegrand mu f) (k.integrable_actionIntegrand mu g)

omit [BorelSpace S] in
theorem action_smul (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu]
    (c : ℝ) (f : C(S, ℝ)) : k.action mu (c • f) = c • k.action mu f := by
  unfold action
  rw [actionIntegrand_smul]
  change (∫ y, c • k.actionIntegrand f y ∂mu) = c • ∫ y, k.actionIntegrand f y ∂mu
  exact integral_smul (𝕜 := ℝ) c (fun y ↦ k.actionIntegrand f y)

/-- The integral-kernel action as a linear map on `C(S, ℝ)`. -/
def actionLinearMap (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu] :
    C(S, ℝ) →ₗ[ℝ] C(S, ℝ) where
  toFun := k.action mu
  map_add' := k.action_add mu
  map_smul' := k.action_smul mu

@[simp]
theorem actionLinearMap_apply (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu]
    (f : C(S, ℝ)) : k.actionLinearMap mu f = k.action mu f :=
  rfl

omit [BorelSpace S] in
theorem norm_action_le (k : ContinuousKernel S) (mu : Measure S) [IsProbabilityMeasure mu]
    (f : C(S, ℝ)) : ‖k.action mu f‖ ≤ ‖k.toContinuousMap‖ * ‖f‖ := by
  unfold action
  calc
    ‖∫ y, k.actionIntegrand f y ∂mu‖
        ≤ (‖k.toContinuousMap‖ * ‖f‖) * mu.real Set.univ :=
      norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall (fun y ↦ k.norm_actionIntegrand_le f y))
    _ = ‖k.toContinuousMap‖ * ‖f‖ := by simp

/-- The integral operator on `C(S, ℝ)` associated with the kernel. -/
def actionCLM (k : ContinuousKernel S) (mu : Measure S) [IsProbabilityMeasure mu] :
    C(S, ℝ) →L[ℝ] C(S, ℝ) :=
  (k.actionLinearMap mu).mkContinuous ‖k.toContinuousMap‖ (k.norm_action_le mu)

@[simp]
theorem actionCLM_apply (k : ContinuousKernel S) (mu : Measure S) [IsProbabilityMeasure mu]
    (f : C(S, ℝ)) : k.actionCLM mu f = k.action mu f :=
  rfl

theorem norm_actionCLM_le (k : ContinuousKernel S) (mu : Measure S)
    [IsProbabilityMeasure mu] : ‖k.actionCLM mu‖ ≤ ‖k.toContinuousMap‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) (k.norm_action_le mu)

end ContinuousKernel
end PerronWright
