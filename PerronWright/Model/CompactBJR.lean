import PerronWright.Kernel.Composition
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# The regular compact-type BJR model

This file records exactly the data and the two hypotheses `(B1)`--`(B2)`
from Definition 3.2 of the paper.  In particular, no Perron eigenvalue,
eigenfunction, or simplicity conclusion is included in the model.

The integral operator in `(B1)` is characterized on continuous functions by
its weak `L²` pairing.  This avoids choosing representatives of arbitrary
`L²` classes while still saying that the operator is the one associated with
the displayed kernel.  The kernel occurring in `(B2)` is tied pointwise to an
explicit iterated-integral definition, so it is not an independent positivity
assumption about an unrelated operator.
-/

open MeasureTheory

noncomputable section

namespace PerronWright

/-- The data of a compact-type BJR model before the criticality and
primitivity assumptions `(B1)`--`(B2)` are imposed. -/
structure CompactBJRModel (S : Type*) [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] where
  /-- The type law. -/
  mu : Measure S
  /-- The type law is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure mu
  /-- Full support, expressed by positivity on every nonempty open set. -/
  isOpenPosMeasure : mu.IsOpenPosMeasure
  /-- The continuous, symmetric, nonnegative edge kernel. -/
  kernel : ContinuousKernel S

namespace CompactBJRModel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

instance (M : CompactBJRModel S) : IsProbabilityMeasure M.mu :=
  M.isProbabilityMeasure

instance (M : CompactBJRModel S) : M.mu.IsOpenPosMeasure :=
  M.isOpenPosMeasure

/-- The Hilbert space on which the kernel operator in `(B1)` acts. -/
abbrev L2 (M : CompactBJRModel S) := MeasureTheory.Lp ℝ 2 M.mu

/-- The action of the kernel on a test function, written pointwise.

No integrability proof is hidden in this definition: the Bochner integral is
total in Lean.  For continuous `f`, integrability follows from compactness and
is proved in the analytic kernel layer when it is needed.
-/
def integralAction (M : CompactBJRModel S) (f : S → ℝ) (x : S) : ℝ :=
  ∫ y, M.kernel x y * f y ∂M.mu

/-- A bounded operator on `L²(μ)` is associated with the BJR kernel when its
weak pairing against continuous test functions is the expected double
integral.

Continuous functions are dense in `L²(μ)` in the present compact Borel
setting, so this condition uniquely determines the bounded operator; it also
avoids making arbitrary choices of representatives of `L²` classes.
-/
def IsAssociatedL2Operator (M : CompactBJRModel S)
    (K : M.L2 →L[ℝ] M.L2) : Prop :=
  ∀ f g : C(S, ℝ),
    inner ℝ (K (ContinuousMap.toLp 2 M.mu ℝ f))
        (ContinuousMap.toLp 2 M.mu ℝ g) =
      ∫ x, g x * M.integralAction f x ∂M.mu

/-- A witness for assumption `(B1)`: the associated `L²` integral operator is
compact, self-adjoint (expressed as symmetry of its underlying linear map),
and has operator norm one.

The field `associated` prevents an arbitrary compact operator from serving as
the witness for the kernel in the model.
-/
structure B1Witness (M : CompactBJRModel S) where
  operator : M.L2 →L[ℝ] M.L2
  associated : M.IsAssociatedL2Operator operator
  isCompact : IsCompactOperator operator
  isSymmetric : operator.toLinearMap.IsSymmetric
  norm_eq_one : ‖operator‖ = 1

/-- Assumption `(B1)` of the regular compact-type BJR model. -/
def B1 (M : CompactBJRModel S) : Prop :=
  Nonempty M.B1Witness

/-- The integral kernel of `K^(n+1)`, defined by iterating kernel composition.

The index is shifted by one because the identity operator need not possess a
continuous integral kernel.  Thus `iteratedKernel 0` is the kernel of `K`, and
`iteratedKernel n` is the kernel of `K^(n+1)`.
-/
def iteratedKernel (M : CompactBJRModel S) : ℕ → S → S → ℝ
  | 0 => fun x y ↦ M.kernel x y
  | n + 1 => fun x y ↦ ∫ z, M.kernel x z * M.iteratedKernel n z y ∂M.mu

@[simp]
theorem iteratedKernel_zero (M : CompactBJRModel S) (x y : S) :
    M.iteratedKernel 0 x y = M.kernel x y :=
  rfl

@[simp]
theorem iteratedKernel_succ (M : CompactBJRModel S) (n : ℕ) (x y : S) :
    M.iteratedKernel (n + 1) x y =
      ∫ z, M.kernel x z * M.iteratedKernel n z y ∂M.mu :=
  rfl

/-- The same iterated kernel bundled as a continuous map. -/
def iteratedKernelMap (M : CompactBJRModel S) : ℕ → C(S × S, ℝ)
  | 0 => M.kernel.toContinuousMap
  | n + 1 => KernelMap.comp M.mu M.kernel.toContinuousMap (M.iteratedKernelMap n)

@[simp]
theorem iteratedKernelMap_zero (M : CompactBJRModel S) :
    M.iteratedKernelMap 0 = M.kernel.toContinuousMap :=
  rfl

@[simp]
theorem iteratedKernelMap_succ (M : CompactBJRModel S) (n : ℕ) :
    M.iteratedKernelMap (n + 1) =
      KernelMap.comp M.mu M.kernel.toContinuousMap (M.iteratedKernelMap n) :=
  rfl

@[simp]
theorem iteratedKernelMap_apply (M : CompactBJRModel S) (n : ℕ) (x y : S) :
    M.iteratedKernelMap n (x, y) = M.iteratedKernel n x y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
      rw [iteratedKernelMap_succ, KernelMap.comp_apply, iteratedKernel_succ]
      simp only [ih]

/-- The action of the `n`-th iterated kernel is exactly the `(n+1)`-st
power of the continuous integral operator.  Thus `(B2)` below concerns the
actual operator from the model, not merely a formally iterated function. -/
theorem iteratedKernelMap_action (M : CompactBJRModel S) (n : ℕ)
    (f : C(S, ℝ)) :
    KernelMap.action M.mu (M.iteratedKernelMap n) f =
      (M.kernel.actionCLM M.mu ^ n.succ) f := by
  induction n with
  | zero =>
      simp only [iteratedKernelMap_zero, KernelMap.action_toContinuousMap,
        pow_one, ContinuousKernel.actionCLM_apply]
  | succ n ih =>
      calc
        KernelMap.action M.mu (M.iteratedKernelMap n.succ) f =
            KernelMap.action M.mu M.kernel.toContinuousMap
              (KernelMap.action M.mu (M.iteratedKernelMap n) f) := by
                rw [iteratedKernelMap_succ, KernelMap.action_comp]
        _ = M.kernel.action M.mu
              ((M.kernel.actionCLM M.mu ^ n.succ) f) := by
                rw [KernelMap.action_toContinuousMap, ih]
        _ = M.kernel.actionCLM M.mu
              ((M.kernel.actionCLM M.mu ^ n.succ) f) := rfl
        _ = (M.kernel.actionCLM M.mu *
              M.kernel.actionCLM M.mu ^ n.succ) f := by
                rw [mul_apply_eq_comp]
        _ = (M.kernel.actionCLM M.mu ^ n.succ.succ) f := by
                rw [← pow_succ']

/-- Assumption `(B2)`: some positive power of the associated operator has a
strictly positive kernel everywhere.  Continuity is not an extra field of the
hypothesis: `iteratedKernelMap` constructs it from the original continuous
kernel by Banach-valued integration. -/
def B2 (M : CompactBJRModel S) : Prop :=
  ∃ n : ℕ, ∀ x y, 0 < M.iteratedKernelMap n (x, y)

/-- Operator-theoretic content of `(B2)`: a positive power of the actual
continuous integral operator maps every nonzero nonnegative function into
the interior of the positive cone. -/
theorem B2.stronglyPositivePower (M : CompactBJRModel S) (h : M.B2) :
    ∃ n : ℕ, ∀ f : C(S, ℝ), (∀ y, 0 ≤ f y) → f ≠ 0 →
      ∀ x, 0 < (M.kernel.actionCLM M.mu ^ n.succ) f x := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  intro f hf hf_ne x
  rw [← M.iteratedKernelMap_action n f]
  exact KernelMap.action_pos_of_kernel_pos M.mu (M.iteratedKernelMap n)
    hn f hf hf_ne x

/-- The hypotheses defining the regular critical compact-type BJR regime. -/
structure IsRegularCritical (M : CompactBJRModel S) : Prop where
  b1 : M.B1
  b2 : M.B2

end CompactBJRModel

end PerronWright
