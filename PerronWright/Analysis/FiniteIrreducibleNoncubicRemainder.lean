import PerronWright.Analysis.FiniteIrreducibleBoundedKernelAmplitude
import PerronWright.Enumeration.NoncubicBoundedKernelRemainder
import PerronWright.Enumeration.FixedSurplusNoncubicCoreAnalytic

/-!
# Joint analytic remainder for noncubic bounded kernels

This file supplies the analytic half of the lower-order noncubic argument.
For an arbitrary bounded endpoint table, it multiplies the pole-removed
marked-path product by the genuine branch-profile factors.  If the table has
strictly fewer than `3 * ell` edges, cubic normalization leaves a canonical
jointly analytic remainder and one explicit factor of the fold coordinate.

The construction is then summed over the literal finite type of noncubic
admissible cores of one fixed size.  This consumes the already proved strict
edge-count gap and introduces no analytic hypothesis.  The sum in the last
section is deliberately named a *shape-integrand* sum: identifying it with
the full all-length fixed-surplus graph contribution still requires the
general (variable-valence) subdivision/fibre regrouping theorem.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleKernelAmplitude
open GraphCore

namespace NCBKR_MPR

export PerronWright.FiniteIrreducibleMarkedPathResolvent
  (profile profile_analytic profile_base pathResolventKernel)

end NCBKR_MPR

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## One bounded shape -/

/-- Product of the actual joint fold profile over all branch coordinates of
one bounded kernel table. -/
def boundedKernelBranchProfileProduct
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (D : GraphCore.BoundedKernelShape ell)
    (x : Fin D.1.val → S) (q : C(S, ℂ) × ℂ) : ℂ :=
  ∏ v : Fin D.1.val, NCBKR_MPR.profile M hM q (x v)

private theorem boundedKernelBranchProfileFactor_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (D : GraphCore.BoundedKernelShape ell)
    (x : Fin D.1.val → S) (v : Fin D.1.val) :
    AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦
      NCBKR_MPR.profile M hM q (x v)) (0, 0) := by
  have heval : AnalyticAt ℂ
      (fun tau : C(S, ℂ) ↦ tau (x v))
      (NCBKR_MPR.profile M hM (0, 0)) :=
    (ContinuousMap.evalCLM ℂ (x v) : C(S, ℂ) →L[ℂ] ℂ).analyticAt _
  exact heval.comp_of_eq (NCBKR_MPR.profile_analytic M hM) rfl

/-- The bounded-kernel branch-profile product is jointly analytic. -/
theorem boundedKernelBranchProfileProduct_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (D : GraphCore.BoundedKernelShape ell)
    (x : Fin D.1.val → S) :
    AnalyticAt ℂ (boundedKernelBranchProfileProduct M hM D x)
      (0, 0) := by
  unfold boundedKernelBranchProfileProduct
  exact (Finset.univ : Finset (Fin D.1.val)).analyticAt_fun_prod
    (fun v _ ↦ boundedKernelBranchProfileFactor_analytic M hM D x v)

/-- Every branch-profile factor equals one at the joint base point. -/
@[simp] theorem boundedKernelBranchProfileProduct_base
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (D : GraphCore.BoundedKernelShape ell)
    (x : Fin D.1.val → S) :
    boundedKernelBranchProfileProduct M hM D x (0, 0) = 1 := by
  unfold boundedKernelBranchProfileProduct
  rw [NCBKR_MPR.profile_base]
  simp

/-- Branch profiles times the product of all pole-removed path kernels for
one bounded endpoint table. -/
def boundedKernelNormalizedCoreIntegrand
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (D : GraphCore.BoundedKernelShape ell)
    (x : Fin D.1.val → S) (q : C(S, ℂ) × ℂ) : ℂ :=
  boundedKernelBranchProfileProduct M hM D x q *
    boundedKernelNormalizedPathAmplitude M hM D x q

/-- The full pole-removed bounded-kernel integrand is jointly analytic. -/
theorem boundedKernelNormalizedCoreIntegrand_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (D : GraphCore.BoundedKernelShape ell)
    (x : Fin D.1.val → S) :
    AnalyticAt ℂ (boundedKernelNormalizedCoreIntegrand M hM D x)
      (0, 0) :=
  (boundedKernelBranchProfileProduct_analytic M hM D x).mul
    (boundedKernelNormalizedPathAmplitude_analytic M hM D x)

/-- The corresponding unrestricted marked-path-resolvent integrand. -/
def boundedKernelCoreResolventIntegrand
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (D : GraphCore.BoundedKernelShape ell)
    (x : Fin D.1.val → S) (q : C(S, ℂ) × ℂ) : ℂ :=
  boundedKernelBranchProfileProduct M hM D x q *
    ∏ e : Fin D.2.1.val,
      NCBKR_MPR.pathResolventKernel M hM q
        (x (boundedKernelOrderedEndpoints D e).1,
          x (boundedKernelOrderedEndpoints D e).2)

/-- On the punctured germ, the normalized integrand is exactly the edge
power times the unrestricted resolvent integrand. -/
theorem boundedKernelNormalizedCoreIntegrand_eq_pow_mul_resolvent
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (D : GraphCore.BoundedKernelShape ell)
    (x : Fin D.1.val → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      boundedKernelNormalizedCoreIntegrand M hM D x q =
        q.2 ^ D.2.1.val *
          boundedKernelCoreResolventIntegrand M hM D x q := by
  filter_upwards
    [boundedKernelNormalizedPathAmplitude_eq_pow_mul_resolventProduct
      M hM D x] with q hpath
  intro hX
  rw [boundedKernelNormalizedCoreIntegrand,
    boundedKernelCoreResolventIntegrand, hpath hX]
  ring

/-- Canonical joint analytic remainder after removing one of the powers
left by cubic normalization. -/
def boundedKernelCubicDefectRemainder
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (D : GraphCore.BoundedKernelShape ell)
    (x : Fin D.1.val → S) (q : C(S, ℂ) × ℂ) : ℂ :=
  q.2 ^ (3 * ell - D.2.1.val - 1) *
    boundedKernelNormalizedCoreIntegrand M hM D x q

/-- The canonical defect remainder is jointly analytic.  Analyticity itself
does not require the strict edge gap; the gap is used in the factorization
below. -/
theorem boundedKernelCubicDefectRemainder_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (D : GraphCore.BoundedKernelShape ell)
    (x : Fin D.1.val → S) :
    AnalyticAt ℂ (boundedKernelCubicDefectRemainder M hM D x)
      (0, 0) := by
  exact (analyticAt_snd.pow (3 * ell - D.2.1.val - 1)).mul
    (boundedKernelNormalizedCoreIntegrand_analytic M hM D x)

/-- A strict edge deficit gives an identity, on the whole parameter space,
with one explicit factor of the fold coordinate. -/
theorem boundedKernel_cubicNormalizedIntegrand_eq_X_mul_remainder
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (D : GraphCore.BoundedKernelShape ell)
    (x : Fin D.1.val → S)
    (hedges : D.2.1.val < 3 * ell)
    (q : C(S, ℂ) × ℂ) :
    q.2 ^ (3 * ell - D.2.1.val) *
        boundedKernelNormalizedCoreIntegrand M hM D x q =
      q.2 * boundedKernelCubicDefectRemainder M hM D x q := by
  have hsucc :
      3 * ell - D.2.1.val - 1 + 1 = 3 * ell - D.2.1.val := by
    omega
  unfold boundedKernelCubicDefectRemainder
  have hpow :
      q.2 ^ (3 * ell - D.2.1.val) =
        q.2 ^ (3 * ell - D.2.1.val - 1) * q.2 := by
    conv_lhs => rw [← hsucc, pow_succ]
  rw [hpow]
  ring

/-! ## Literal fixed-size noncubic core index -/

/-- Cubic-normalized finite sum of the bounded-shape integrands indexed by
all literal noncubic admissible cores of one fixed size.  A coordinate
vector is supplied for each (possibly differently sized) bounded table. -/
def fixedSizeNoncubicShapeIntegrandSum
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {q ell : ℕ} (hell : 0 < ell)
    (x : ∀ H : NoncubicAdmissibleAttachmentCore q ell,
      Fin (noncubicAdmissibleCoreBoundedShape hell H).1.val → S)
    (z : C(S, ℂ) × ℂ) : ℂ :=
  ∑ H : NoncubicAdmissibleAttachmentCore q ell,
    z.2 ^ (3 * ell -
      (noncubicAdmissibleCoreBoundedShape hell H).2.1.val) *
      boundedKernelNormalizedCoreIntegrand M hM
        (noncubicAdmissibleCoreBoundedShape hell H) (x H) z

/-- Finite sum of the corresponding canonical joint analytic remainders. -/
def fixedSizeNoncubicShapeRemainderSum
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {q ell : ℕ} (hell : 0 < ell)
    (x : ∀ H : NoncubicAdmissibleAttachmentCore q ell,
      Fin (noncubicAdmissibleCoreBoundedShape hell H).1.val → S)
    (z : C(S, ℂ) × ℂ) : ℂ :=
  ∑ H : NoncubicAdmissibleAttachmentCore q ell,
    boundedKernelCubicDefectRemainder M hM
      (noncubicAdmissibleCoreBoundedShape hell H) (x H) z

/-- The fixed-size noncubic remainder sum is jointly analytic. -/
theorem fixedSizeNoncubicShapeRemainderSum_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {q ell : ℕ} (hell : 0 < ell)
    (x : ∀ H : NoncubicAdmissibleAttachmentCore q ell,
      Fin (noncubicAdmissibleCoreBoundedShape hell H).1.val → S) :
    AnalyticAt ℂ
      (fixedSizeNoncubicShapeRemainderSum M hM hell x) (0, 0) := by
  unfold fixedSizeNoncubicShapeRemainderSum
  exact (Finset.univ : Finset
      (NoncubicAdmissibleAttachmentCore q ell)).analyticAt_fun_sum
    (fun H _ ↦ boundedKernelCubicDefectRemainder_analytic M hM
      (noncubicAdmissibleCoreBoundedShape hell H) (x H))

/-- Exact finite-sum lower-order statement: cubic normalization of the
whole literal noncubic shape-indexed family has one explicit factor `X`,
and the remaining factor is the preceding jointly analytic sum. -/
theorem fixedSizeNoncubicShapeIntegrandSum_eq_X_mul_remainder
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {q ell : ℕ} (hell : 0 < ell)
    (x : ∀ H : NoncubicAdmissibleAttachmentCore q ell,
      Fin (noncubicAdmissibleCoreBoundedShape hell H).1.val → S)
    (z : C(S, ℂ) × ℂ) :
    fixedSizeNoncubicShapeIntegrandSum M hM hell x z =
      z.2 * fixedSizeNoncubicShapeRemainderSum M hM hell x z := by
  unfold fixedSizeNoncubicShapeIntegrandSum
    fixedSizeNoncubicShapeRemainderSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  exact boundedKernel_cubicNormalizedIntegrand_eq_X_mul_remainder
    M hM (noncubicAdmissibleCoreBoundedShape hell H) (x H)
      (noncubicAdmissibleCoreBoundedShape_edgeCount_lt hell H) z

end PerronWright.FiniteIrreducibleKernelAmplitude


