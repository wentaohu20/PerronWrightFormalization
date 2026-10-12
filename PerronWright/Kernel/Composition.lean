import PerronWright.Kernel.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Composition of continuous integral kernels

For continuous kernels `a` and `b`, their operator-composition kernel is

`(x,y) ↦ ∫ z, a(x,z) * b(z,y) ∂μ`.

The integral is taken in `C(S × S, ℝ)`, so continuity of the resulting
kernel is built into the definition.
-/

open MeasureTheory

noncomputable section

namespace PerronWright
namespace KernelMap

variable {S : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The `C(S × S, ℝ)`-valued integrand for composition of two kernels. -/
def compositionIntegrand (a b : C(S × S, ℝ)) : C(S, C(S × S, ℝ)) :=
  ContinuousMap.curry
    { toFun := fun p : S × (S × S) ↦ a (p.2.1, p.1) * b (p.1, p.2.2)
      continuous_toFun := by fun_prop }

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem compositionIntegrand_apply (a b : C(S × S, ℝ)) (z x y : S) :
    compositionIntegrand a b z (x, y) = a (x, z) * b (z, y) :=
  rfl

theorem integrable_compositionIntegrand (a b : C(S × S, ℝ)) (mu : Measure S)
    [IsFiniteMeasure mu] : Integrable (compositionIntegrand a b) mu := by
  apply (compositionIntegrand a b).continuous.integrable_of_hasCompactSupport
  exact isClosed_closure.isCompact

/-- Composition of two continuous integral kernels. -/
def comp (mu : Measure S) [IsFiniteMeasure mu] (a b : C(S × S, ℝ)) : C(S × S, ℝ) :=
  ∫ z, compositionIntegrand a b z ∂mu

@[simp]
theorem comp_apply (mu : Measure S) [IsFiniteMeasure mu] (a b : C(S × S, ℝ))
    (x y : S) :
    comp mu a b (x, y) = ∫ z, a (x, z) * b (z, y) ∂mu := by
  rw [comp, ContinuousMap.integral_apply (integrable_compositionIntegrand a b mu) (x, y)]
  simp only [compositionIntegrand_apply]

/-- The continuous family of columns of an arbitrary continuous kernel. -/
def columns (a : C(S × S, ℝ)) : C(S, C(S, ℝ)) :=
  (a.comp (ContinuousMap.prodSwap : C(S × S, S × S))).curry

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem columns_apply (a : C(S × S, ℝ)) (y x : S) :
    columns a y x = a (x, y) :=
  rfl

/-- The Banach-valued integrand for applying an arbitrary continuous kernel. -/
def actionIntegrand (a : C(S × S, ℝ)) (f : C(S, ℝ)) : C(S, C(S, ℝ)) where
  toFun y := f y • columns a y
  continuous_toFun := f.continuous.smul (columns a).continuous

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem actionIntegrand_apply (a : C(S × S, ℝ)) (f : C(S, ℝ))
    (y x : S) : actionIntegrand a f y x = a (x, y) * f y := by
  change f y * a (x, y) = a (x, y) * f y
  exact mul_comm _ _

theorem integrable_actionIntegrand (a : C(S × S, ℝ)) (f : C(S, ℝ))
    (mu : Measure S) [IsFiniteMeasure mu] : Integrable (actionIntegrand a f) mu := by
  apply (actionIntegrand a f).continuous.integrable_of_hasCompactSupport
  exact isClosed_closure.isCompact

/-- Action of an arbitrary continuous kernel on a continuous function. -/
def action (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (f : C(S, ℝ)) : C(S, ℝ) :=
  ∫ y, actionIntegrand a f y ∂mu

@[simp]
theorem action_apply (mu : Measure S) [IsFiniteMeasure mu] (a : C(S × S, ℝ))
    (f : C(S, ℝ)) (x : S) :
    action mu a f x = ∫ y, a (x, y) * f y ∂mu := by
  rw [action, ContinuousMap.integral_apply (integrable_actionIntegrand a f mu) x]
  simp only [actionIntegrand_apply]

/-- The generic kernel-map action specializes to the action already attached
to a `ContinuousKernel`.  This is the bridge used to connect pointwise kernel
composition with powers of the bundled integral operator. -/
@[simp]
theorem action_toContinuousMap (mu : Measure S) [IsFiniteMeasure mu]
    (k : ContinuousKernel S) (f : C(S, ℝ)) :
    action mu k.toContinuousMap f = k.action mu f := by
  ext x
  simp only [action_apply, ContinuousKernel.action_apply]

/-- A pointwise strictly positive continuous kernel sends every nonzero
nonnegative continuous function to a pointwise strictly positive function,
provided the measure has full support. -/
theorem action_pos_of_kernel_pos (mu : Measure S) [IsFiniteMeasure mu]
    [mu.IsOpenPosMeasure] (a : C(S × S, ℝ))
    (ha : ∀ x y, 0 < a (x, y)) (f : C(S, ℝ))
    (hf : ∀ y, 0 ≤ f y) (hf_ne : f ≠ 0) (x : S) :
    0 < action mu a f x := by
  rw [action_apply]
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    apply hf_ne
    ext z
    simpa using h z
  apply integral_pos_of_integrable_nonneg_nonzero (x := y)
  · fun_prop
  · apply (show Continuous (fun z ↦ a (x, z) * f z) by fun_prop).integrable_of_hasCompactSupport
    exact isClosed_closure.isCompact
  · intro z
    exact mul_nonneg (ha x z).le (hf z)
  · exact mul_ne_zero (ha x y).ne' hy

/-- Kernel composition agrees with composition of the corresponding actions. -/
theorem action_comp (mu : Measure S) [IsFiniteMeasure mu] (a b : C(S × S, ℝ))
    (f : C(S, ℝ)) :
    action mu (comp mu a b) f = action mu a (action mu b f) := by
  ext x
  rw [action_apply, action_apply]
  simp_rw [comp_apply, action_apply]
  change
    (∫ y, (∫ z, a (x, z) * b (z, y) ∂mu) * f y ∂mu) =
      ∫ z, a (x, z) * (∫ y, b (z, y) * f y ∂mu) ∂mu
  have hleft (y : S) :
      (∫ z, a (x, z) * (b (z, y) * f y) ∂mu) =
        (∫ z, a (x, z) * b (z, y) ∂mu) * f y := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with z
    exact (mul_assoc _ _ _).symm
  have hright (z : S) :
      (∫ y, a (x, z) * (b (z, y) * f y) ∂mu) =
        a (x, z) * (∫ y, b (z, y) * f y ∂mu) := by
    exact integral_const_mul _ _
  calc
    (∫ y, (∫ z, a (x, z) * b (z, y) ∂mu) * f y ∂mu) =
        ∫ y, ∫ z, a (x, z) * (b (z, y) * f y) ∂mu ∂mu := by
          apply integral_congr_ae
          filter_upwards [] with y
          exact (hleft y).symm
    _ = ∫ z, ∫ y, a (x, z) * (b (z, y) * f y) ∂mu ∂mu :=
      (integral_integral_swap_of_hasCompactSupport
        (μ := mu) (ν := mu)
        (f := fun z y ↦ a (x, z) * (b (z, y) * f y))
        (by fun_prop) isClosed_closure.isCompact).symm
    _ = ∫ z, a (x, z) * (∫ y, b (z, y) * f y ∂mu) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hright z

end KernelMap
end PerronWright
