import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous symmetric nonnegative kernels

This file starts the formalization of the regular compact-type BJR model used in
the Perron--Wright theorem.  It contains only definitions and consequences of
the data; no spectral or positivity theorem is assumed here.
-/

open MeasureTheory

noncomputable section

namespace PerronWright

/-- A continuous, symmetric, pointwise nonnegative real kernel on `S`.

The compactness and measure on `S` belong to the ambient BJR model rather than
to the kernel itself.  Keeping them separate lets the same kernel be realized
on `C(S)` and on `L²(μ)` later.
-/
structure ContinuousKernel (S : Type*) [TopologicalSpace S] where
  toContinuousMap : C(S × S, ℝ)
  symmetric' : ∀ x y, toContinuousMap (x, y) = toContinuousMap (y, x)
  nonneg' : ∀ x y, 0 ≤ toContinuousMap (x, y)

namespace ContinuousKernel

variable {S : Type*} [TopologicalSpace S]

instance : CoeFun (ContinuousKernel S) (fun _ ↦ S → S → ℝ) where
  coe κ x y := κ.toContinuousMap (x, y)

@[simp]
theorem coe_toContinuousMap (k : ContinuousKernel S) (x y : S) :
    k.toContinuousMap (x, y) = k x y :=
  rfl

theorem symmetric (k : ContinuousKernel S) (x y : S) : k x y = k y x :=
  k.symmetric' x y

theorem nonneg (k : ContinuousKernel S) (x y : S) : 0 ≤ k x y :=
  k.nonneg' x y

theorem continuous_uncurry (k : ContinuousKernel S) :
    Continuous (fun p : S × S ↦ k p.1 p.2) :=
  k.toContinuousMap.continuous

theorem continuous_left (k : ContinuousKernel S) (x : S) :
    Continuous (fun y ↦ k x y) := by
  change Continuous (fun y ↦ k.toContinuousMap (x, y))
  exact k.toContinuousMap.continuous.comp (continuous_const.prodMk continuous_id)

theorem continuous_right (k : ContinuousKernel S) (y : S) :
    Continuous (fun x ↦ k x y) := by
  change Continuous (fun x ↦ k.toContinuousMap (x, y))
  exact k.toContinuousMap.continuous.comp (continuous_id.prodMk continuous_const)

theorem measurable_left [MeasurableSpace S] [BorelSpace S]
    (k : ContinuousKernel S) (x : S) : Measurable (fun y ↦ k x y) :=
  (k.continuous_left x).measurable

theorem measurable_right [MeasurableSpace S] [BorelSpace S]
    (k : ContinuousKernel S) (y : S) : Measurable (fun x ↦ k x y) :=
  (k.continuous_right y).measurable

theorem integrable_left [CompactSpace S] [MeasurableSpace S] [BorelSpace S]
    (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu] (x : S) :
    Integrable (fun y ↦ k x y) mu := by
  apply (k.continuous_left x).integrable_of_hasCompactSupport
  exact isClosed_closure.isCompact

theorem integrable_right [CompactSpace S] [MeasurableSpace S] [BorelSpace S]
    (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu] (y : S) :
    Integrable (fun x ↦ k x y) mu := by
  apply (k.continuous_right y).integrable_of_hasCompactSupport
  exact isClosed_closure.isCompact

/-- The degree function `d(x) = ∫ κ(x,y) dμ(y)` from the paper. -/
def degree [MeasurableSpace S] (k : ContinuousKernel S) (mu : Measure S) (x : S) : ℝ :=
  ∫ y, k x y ∂mu

theorem degree_nonneg [MeasurableSpace S] [BorelSpace S]
    (k : ContinuousKernel S) (mu : Measure S) (x : S) :
    0 ≤ k.degree mu x := by
  exact integral_nonneg fun y ↦ k.nonneg x y

end ContinuousKernel

end PerronWright
