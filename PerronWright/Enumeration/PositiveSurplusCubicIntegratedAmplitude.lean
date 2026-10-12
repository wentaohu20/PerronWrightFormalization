import PerronWright.Enumeration.PositiveSurplusWrightConstant
import PerronWright.Enumeration.CubicKernelForbiddenLengthCorrection

/-!
# The finite positive-surplus cubic amplitude

This module forms the exact inverse-presentation-multiplicity sum of the
integrated normalized amplitudes of all labelled connected cubic kernels of
one fixed surplus.  Finiteness makes analyticity immediate.  At the joint
base point the value is the cubic EGF constant times `sqrt(beta) ^ ell`; on the
punctured fold germ it is `X ^ (3 * ell)` times the corresponding finite sum
of unrestricted path-resolvent integrals.

The last section records the finite coefficient-level interface for the
simple-graph correction.  It sums the already proved
admissible/forbidden decomposition over the same cubic kernels and exact
multiplicity weights.  No analyticity assertion about the forbidden
correction is assumed here.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## Finite analytic cubic-kernel sum -/

/-- Exact finite sum of all integrated pole-removed cubic-kernel amplitudes,
with the inverse global presentation multiplicity of the existing
regrouping theorem. -/
def positiveSurplusCubicIntegratedAmplitude
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelIntegratedNormalizedAmplitude M hM K q

/-- The finite cubic-kernel sum is jointly analytic in the field and fold
coordinate. -/
theorem positiveSurplusCubicIntegratedAmplitude_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    AnalyticAt ℂ (positiveSurplusCubicIntegratedAmplitude M hM ell)
      (0, 0) := by
  let _ := labelledConnectedCubicKernelFintype ell
  unfold positiveSurplusCubicIntegratedAmplitude
  let F : LabelledConnectedCubicKernel ell →
      (C(S, ℂ) × ℂ → ℂ) := fun K q ↦
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelIntegratedNormalizedAmplitude M hM K q
  change AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦ ∑ K, F K q) (0, 0)
  have hsum : AnalyticAt ℂ (∑ K, F K) (0, 0) := by
    apply Finset.analyticAt_sum Finset.univ
    intro K _
    exact analyticAt_const.mul
      (cubicKernelIntegratedNormalizedAmplitude_analytic M hM K)
  have hfun : (∑ K, F K) =
      (fun q : C(S, ℂ) × ℂ ↦ ∑ K, F K q) := by
    funext q
    exact Fintype.sum_apply q F
  rw [← hfun]
  exact hsum

/-- At the joint base point, the finite analytic sum has the exact Wright
constant value. -/
theorem positiveSurplusCubicIntegratedAmplitude_base
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    positiveSurplusCubicIntegratedAmplitude M hM ell (0, 0) =
      positiveSurplusCubicEGFConstant ell *
        (Real.sqrt (M.beta hM) : ℂ) ^ ell := by
  change positiveSurplusCubicLeadingAmplitude M hM ell = _
  exact positiveSurplusCubicLeadingAmplitude_eq_egfConstant M hM ell

/-! ## Punctured identity with the unrestricted resolvent sum -/

/-- Exact finite inverse-multiplicity sum of the unrestricted integrated
cubic path-resolvent products. -/
def positiveSurplusCubicIntegratedResolventSum
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelIntegratedResolventProduct M hM K q

/-- On one common punctured neighborhood (common because the kernel type is
finite), the analytic cubic sum is exactly `X ^ (3 * ell)` times the finite
unrestricted resolvent sum. -/
theorem positiveSurplusCubicIntegratedAmplitude_eq_pow_mul_resolventSum
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      positiveSurplusCubicIntegratedAmplitude M hM ell q =
        q.2 ^ (3 * ell) *
          positiveSurplusCubicIntegratedResolventSum M hM ell q := by
  let _ := labelledConnectedCubicKernelFintype ell
  have hall :
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        ∀ K : LabelledConnectedCubicKernel ell, q.2 ≠ 0 →
          cubicKernelIntegratedNormalizedAmplitude M hM K q =
            q.2 ^ (3 * ell) *
              cubicKernelIntegratedResolventProduct M hM K q := by
    rw [Filter.eventually_all]
    intro K
    exact cubicKernelIntegratedNormalizedAmplitude_eq_pow_mul M hM K
  filter_upwards [hall] with q hq
  intro hX
  unfold positiveSurplusCubicIntegratedAmplitude
    positiveSurplusCubicIntegratedResolventSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [hq K hX]
  ring

/-! ## Exact finite forbidden-correction interface -/

/-- Inverse-multiplicity sum of the unrestricted fixed-degree path-product
coefficient over all labelled cubic kernels. -/
def positiveSurplusCubicUnrestrictedPathCoefficient
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (ell : ℕ) (x : Fin (2 * ell) → S) (d : ℕ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      PowerSeries.coeff d (cubicKernelPathProductSeries M tau K x)

/-- Inverse-multiplicity sum of the admissible fixed-degree path coefficient
over all labelled cubic kernels. -/
def positiveSurplusCubicAdmissiblePathCoefficient
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (ell : ℕ) (x : Fin (2 * ell) → S) (d : ℕ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelAdmissiblePathCoefficient M tau K x d

/-- Inverse-multiplicity sum of the explicit forbidden fixed-degree
correction over all labelled cubic kernels. -/
def positiveSurplusCubicForbiddenPathCoefficient
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (ell : ℕ) (x : Fin (2 * ell) → S) (d : ℕ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      cubicKernelForbiddenPathCoefficient M tau K x d

/-- The global weighted unrestricted coefficient is exactly its admissible
part plus the explicit finite forbidden correction.  This is the precise
coefficient interface to be integrated in the next simple-graph assembly. -/
theorem positiveSurplusCubicUnrestrictedPathCoefficient_eq_admissible_add_forbidden
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (ell : ℕ) (x : Fin (2 * ell) → S) (d : ℕ) :
    positiveSurplusCubicUnrestrictedPathCoefficient M tau ell x d =
      positiveSurplusCubicAdmissiblePathCoefficient M tau ell x d +
        positiveSurplusCubicForbiddenPathCoefficient M tau ell x d := by
  let _ := labelledConnectedCubicKernelFintype ell
  unfold positiveSurplusCubicUnrestrictedPathCoefficient
    positiveSurplusCubicAdmissiblePathCoefficient
    positiveSurplusCubicForbiddenPathCoefficient
  simp_rw [cubicKernelPathProductSeries_coeff_eq_admissible_add_forbidden,
    mul_add]
  exact Finset.sum_add_distrib

end PerronWright.GraphCore
