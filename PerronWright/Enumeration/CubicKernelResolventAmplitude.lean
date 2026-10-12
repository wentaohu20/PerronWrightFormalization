import PerronWright.Enumeration.BoundedKernelPathAmplitude
import PerronWright.Enumeration.CubicKernelPathGeneratingSeries

/-!
# The pole-removed resolvent amplitude of one labelled cubic kernel

The general bounded-kernel construction removes one simple marked-path pole
per kernel edge.  A labelled cubic kernel of surplus `ell` has exactly
`3 * ell` edge labels, so its specialization gives a jointly analytic
amplitude whose punctured value is

`X ^ (3 * ell) * product(pathResolventKernel)`.

This file also inserts the finite product of branch-profile factors.  At the
joint base point those factors are all one, while every normalized edge
factor is the frozen Perron residue kernel.  Consequently the value of the
full pointwise amplitude at `X = 0` is the literal `3 * ell`-fold residue
product.

No parameter integral is taken here.  The currently public integration
interfaces act on one copy of the type space; passing from the pointwise
statement below to integration over `Fin (2 * ell) -> S` requires a separate
Banach-valued pullback construction into the corresponding continuous-map
space.  Pointwise analyticity alone is deliberately not used to justify that
step.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.GraphCore

namespace CKRA_MPR

export PerronWright.MarkedPathResolvent
  (profile profile_analytic profile_base
   residueKernel residueKernel_base pathResolventKernel)

end CKRA_MPR

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## The cubic specialization of the bounded edge amplitude -/

/-- The analytic pole-removed edge product of one fixed labelled cubic
kernel, evaluated at fixed branch coordinates. -/
def cubicKernelNormalizedPathAmplitude
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) (q : C(S, ℂ) × ℂ) : ℂ :=
  boundedKernelNormalizedPathAmplitude M hM
    (cubicKernelBoundedShape K) x q

/-- The pole-removed product for a cubic kernel is jointly analytic in the
field and fold coordinate. -/
theorem cubicKernelNormalizedPathAmplitude_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) :
    AnalyticAt ℂ (cubicKernelNormalizedPathAmplitude M hM K x) (0, 0) := by
  unfold cubicKernelNormalizedPathAmplitude
  exact boundedKernelNormalizedPathAmplitude_analytic M hM
    (cubicKernelBoundedShape K) x

/-- On the punctured fold germ, the cubic analytic amplitude is exactly
`X ^ (3 * ell)` times the unrestricted product of marked-path resolvent
kernels over the labelled kernel edges. -/
theorem cubicKernelNormalizedPathAmplitude_eq_pow_mul_resolventProduct
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      cubicKernelNormalizedPathAmplitude M hM K x q =
        q.2 ^ (3 * ell) *
          ∏ e : Fin (3 * ell),
    CKRA_MPR.pathResolventKernel M hM q
              (x (cubicKernelOrderedEndpoints K.graph e).1,
                x (cubicKernelOrderedEndpoints K.graph e).2) := by
  filter_upwards
    [boundedNormalizedPathKernel_eq_smul_pathResolventKernel M hM] with q hq
  intro hX
  have hedge (e : Fin (3 * ell)) :
      boundedKernelNormalizedEdgeFactor M hM
          (cubicKernelBoundedShape K) x e q =
        q.2 * CKRA_MPR.pathResolventKernel M hM q
          (x (cubicKernelOrderedEndpoints K.graph e).1,
            x (cubicKernelOrderedEndpoints K.graph e).2) := by
    have hfun := congrArg
      (fun k : C(S × S, ℂ) ↦
        k (x (cubicKernelOrderedEndpoints K.graph e).1,
          x (cubicKernelOrderedEndpoints K.graph e).2))
      (hq hX)
    simpa only [boundedKernelNormalizedEdgeFactor,
      boundedKernelOrderedEndpoints_cubicKernelBoundedShape,
      ContinuousMap.smul_apply, smul_eq_mul] using hfun
  unfold cubicKernelBoundedShape at hedge
  unfold cubicKernelNormalizedPathAmplitude cubicKernelBoundedShape
    boundedKernelNormalizedPathAmplitude
  simp_rw [hedge]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The critical value of the cubic edge amplitude is the finite product of
the frozen residue kernel over its `3 * ell` labelled edges. -/
@[simp] theorem cubicKernelNormalizedPathAmplitude_base
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) :
    cubicKernelNormalizedPathAmplitude M hM K x (0, 0) =
      ∏ e : Fin (3 * ell),
        CKRA_MPR.residueKernel M hM 0
          (x (cubicKernelOrderedEndpoints K.graph e).1,
            x (cubicKernelOrderedEndpoints K.graph e).2) := by
  unfold cubicKernelNormalizedPathAmplitude cubicKernelBoundedShape
  rw [boundedKernelNormalizedPathAmplitude_base]
  apply Finset.prod_congr rfl
  intro e _
  rfl

/-- The same base value with the Perron residue written explicitly at every
kernel edge. -/
theorem cubicKernelNormalizedPathAmplitude_base_explicit
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) :
    cubicKernelNormalizedPathAmplitude M hM K x (0, 0) =
      ∏ e : Fin (3 * ell),
        M.complexPerronFunction hM
            (x (cubicKernelOrderedEndpoints K.graph e).1) *
          M.complexPerronFunction hM
            (x (cubicKernelOrderedEndpoints K.graph e).2) /
          (Real.sqrt (2 * M.beta hM) : ℂ) := by
  rw [cubicKernelNormalizedPathAmplitude_base]
  apply Finset.prod_congr rfl
  intro e _
  exact CKRA_MPR.residueKernel_base M hM _ _

/-! ## Adding the branch-profile factors -/

/-- Product of the actual joint fold profile over the `2 * ell` cubic
branch vertices. -/
def cubicKernelBranchProfileProduct
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (x : Fin (2 * ell) → S)
    (q : C(S, ℂ) × ℂ) : ℂ :=
  ∏ v : Fin (2 * ell), CKRA_MPR.profile M hM q (x v)

private theorem cubicKernelBranchProfileFactor_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (x : Fin (2 * ell) → S) (v : Fin (2 * ell)) :
    AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦
      CKRA_MPR.profile M hM q (x v)) (0, 0) := by
  have heval : AnalyticAt ℂ
      (fun tau : C(S, ℂ) ↦ tau (x v))
      (CKRA_MPR.profile M hM (0, 0)) :=
    (ContinuousMap.evalCLM ℂ (x v) : C(S, ℂ) →L[ℂ] ℂ).analyticAt _
  exact heval.comp_of_eq (CKRA_MPR.profile_analytic M hM) rfl

/-- The finite branch-profile product is jointly analytic. -/
theorem cubicKernelBranchProfileProduct_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (x : Fin (2 * ell) → S) :
    AnalyticAt ℂ (cubicKernelBranchProfileProduct M hM x) (0, 0) := by
  unfold cubicKernelBranchProfileProduct
  exact (Finset.univ : Finset (Fin (2 * ell))).analyticAt_fun_prod
    (fun v _ ↦ cubicKernelBranchProfileFactor_analytic M hM x v)

/-- Every branch-profile factor is one at the joint base point. -/
@[simp] theorem cubicKernelBranchProfileProduct_base
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (x : Fin (2 * ell) → S) :
    cubicKernelBranchProfileProduct M hM x (0, 0) = 1 := by
  unfold cubicKernelBranchProfileProduct
  rw [CKRA_MPR.profile_base]
  simp

/-- Full pointwise cubic-kernel amplitude: branch profiles times the
pole-removed marked-path edge product. -/
def cubicKernelNormalizedResolventIntegrand
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) (q : C(S, ℂ) × ℂ) : ℂ :=
  cubicKernelBranchProfileProduct M hM x q *
    cubicKernelNormalizedPathAmplitude M hM K x q

/-- The full pointwise cubic-kernel amplitude is jointly analytic. -/
theorem cubicKernelNormalizedResolventIntegrand_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) :
    AnalyticAt ℂ (cubicKernelNormalizedResolventIntegrand M hM K x)
      (0, 0) :=
  (cubicKernelBranchProfileProduct_analytic M hM x).mul
    (cubicKernelNormalizedPathAmplitude_analytic M hM K x)

/-- Before pole removal, the pointwise kernel integrand is the branch
profile product times the unrestricted marked-path resolvent product. -/
def cubicKernelResolventIntegrand
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) (q : C(S, ℂ) × ℂ) : ℂ :=
  cubicKernelBranchProfileProduct M hM x q *
    ∏ e : Fin (3 * ell),
      CKRA_MPR.pathResolventKernel M hM q
        (x (cubicKernelOrderedEndpoints K.graph e).1,
          x (cubicKernelOrderedEndpoints K.graph e).2)

/-- On the punctured fold germ, multiplying the raw pointwise integrand by
the cubic pole order gives the jointly analytic normalized integrand. -/
theorem cubicKernelNormalizedResolventIntegrand_eq_pow_mul
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      cubicKernelNormalizedResolventIntegrand M hM K x q =
        q.2 ^ (3 * ell) *
          cubicKernelResolventIntegrand M hM K x q := by
  filter_upwards
    [cubicKernelNormalizedPathAmplitude_eq_pow_mul_resolventProduct
      M hM K x] with q hpath
  intro hX
  rw [cubicKernelNormalizedResolventIntegrand,
    cubicKernelResolventIntegrand, hpath hX]
  ring

/-- The branch factors disappear at the base point, leaving exactly the
`3 * ell`-fold residue product. -/
@[simp] theorem cubicKernelNormalizedResolventIntegrand_base
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) :
    cubicKernelNormalizedResolventIntegrand M hM K x (0, 0) =
      ∏ e : Fin (3 * ell),
        CKRA_MPR.residueKernel M hM 0
          (x (cubicKernelOrderedEndpoints K.graph e).1,
            x (cubicKernelOrderedEndpoints K.graph e).2) := by
  rw [cubicKernelNormalizedResolventIntegrand,
    cubicKernelBranchProfileProduct_base,
    cubicKernelNormalizedPathAmplitude_base, one_mul]

/-- Fully explicit base value of the normalized pointwise integrand. -/
theorem cubicKernelNormalizedResolventIntegrand_base_explicit
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) :
    cubicKernelNormalizedResolventIntegrand M hM K x (0, 0) =
      ∏ e : Fin (3 * ell),
        M.complexPerronFunction hM
            (x (cubicKernelOrderedEndpoints K.graph e).1) *
          M.complexPerronFunction hM
            (x (cubicKernelOrderedEndpoints K.graph e).2) /
          (Real.sqrt (2 * M.beta hM) : ℂ) := by
  rw [cubicKernelNormalizedResolventIntegrand_base]
  apply Finset.prod_congr rfl
  intro e _
  exact CKRA_MPR.residueKernel_base M hM _ _

end PerronWright.GraphCore
