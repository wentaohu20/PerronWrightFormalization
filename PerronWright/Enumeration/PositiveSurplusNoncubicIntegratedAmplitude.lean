import PerronWright.Enumeration.NoncubicBoundedKernelAdmissibleSeries

/-!
# Finite weighted noncubic bounded-kernel amplitude

For each connected noncubic bounded kernel, this file packages the genuine
admissible pole-removed integrand from
`NoncubicBoundedKernelAdmissibleSeries` as a continuous function of all
branch coordinates and integrates it against the finite product type law.
It then sums over the finite type of connected noncubic bounded kernels with
the reciprocal of the already defined coordinate multiplicity

`nv! * ne! * 2^(number of loop labels)`.

Every individual kernel has fewer than `3 * ell` suppressed edges.  Hence
its cubic-normalized integrated amplitude, and therefore the finite weighted
sum, is one explicit fold coordinate times a jointly analytic remainder.

This remains a presentation-level theorem.  We do not identify the weighted
sum with the actual noncubic core contribution here; that final statement
requires the separate global presentation-fibre theorem.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## Continuous-function-valued bounded-kernel integrands -/

private def boundedKernelVertexCoordinateMap
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (v : Fin K.shape.1.val) : C((Fin K.shape.1.val → S), S) :=
  ⟨fun x ↦ x v, continuous_apply v⟩

private def boundedKernelVertexPullbackCLM
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (v : Fin K.shape.1.val) :
    C(S, ℂ) →L[ℂ] C((Fin K.shape.1.val → S), ℂ) :=
  ContinuousMap.compCLM ℂ ℂ (boundedKernelVertexCoordinateMap K v)

private def boundedKernelEdgeCoordinateMap
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) :
    C((Fin K.shape.1.val → S), S × S) :=
  ⟨fun x ↦
      (x (boundedKernelOrderedEndpoints K.shape e).1,
        x (boundedKernelOrderedEndpoints K.shape e).2),
    (continuous_apply (boundedKernelOrderedEndpoints K.shape e).1).prodMk
      (continuous_apply (boundedKernelOrderedEndpoints K.shape e).2)⟩

private def boundedKernelEdgePullbackCLM
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) :
    C(S × S, ℂ) →L[ℂ] C((Fin K.shape.1.val → S), ℂ) :=
  ContinuousMap.compCLM ℂ ℂ (boundedKernelEdgeCoordinateMap K e)

/-- Joint fold profile, pulled back and multiplied over all branch
coordinates of a bounded kernel. -/
def boundedKernelBranchProfileFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) : C((Fin K.shape.1.val → S), ℂ) :=
  ∏ v : Fin K.shape.1.val,
    boundedKernelVertexPullbackCLM K v (NBKAS_MPR.profile M hM q)

theorem boundedKernelBranchProfileFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell) :
    AnalyticAt ℂ (boundedKernelBranchProfileFunction M hM K) (0, 0) := by
  unfold boundedKernelBranchProfileFunction
  apply (Finset.univ : Finset (Fin K.shape.1.val)).analyticAt_fun_prod
  intro v _
  exact (boundedKernelVertexPullbackCLM K v).analyticAt _ |>.comp
    (MarkedPathResolvent.profile_analytic M hM)

@[simp] theorem boundedKernelBranchProfileFunction_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    boundedKernelBranchProfileFunction M hM K q x =
      boundedKernelBranchProfileProduct M hM K.shape x q := by
  unfold boundedKernelBranchProfileFunction boundedKernelBranchProfileProduct
  rw [ContinuousMap.prod_apply]
  rfl

/-- One pole-removed edge factor, pulled back to the common branch space. -/
def boundedKernelNormalizedEdgeFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ) :
    C((Fin K.shape.1.val → S), ℂ) :=
  boundedKernelEdgePullbackCLM K e (boundedNormalizedPathKernel M hM q)

theorem boundedKernelNormalizedEdgeFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) :
    AnalyticAt ℂ (boundedKernelNormalizedEdgeFunction M hM K e)
      (0, 0) :=
  ((boundedKernelEdgePullbackCLM K e :
      C(S × S, ℂ) →L[ℂ] C((Fin K.shape.1.val → S), ℂ))).analyticAt _
    |>.comp_of_eq
    (boundedNormalizedPathKernel_analytic M hM) rfl

@[simp] theorem boundedKernelNormalizedEdgeFunction_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S) :
    boundedKernelNormalizedEdgeFunction M hM K e q x =
      boundedKernelNormalizedEdgeFactor M hM K.shape x e q :=
  rfl

/-- Product of all pole-removed edge factors as one continuous function. -/
def boundedKernelNormalizedPathFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) : C((Fin K.shape.1.val → S), ℂ) :=
  ∏ e : Fin K.shape.2.1.val,
    boundedKernelNormalizedEdgeFunction M hM K e q

theorem boundedKernelNormalizedPathFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell) :
    AnalyticAt ℂ (boundedKernelNormalizedPathFunction M hM K) (0, 0) :=
  (Finset.univ : Finset (Fin K.shape.2.1.val)).analyticAt_fun_prod
    (fun e _ ↦ boundedKernelNormalizedEdgeFunction_analytic M hM K e)

@[simp] theorem boundedKernelNormalizedPathFunction_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    boundedKernelNormalizedPathFunction M hM K q x =
      boundedKernelNormalizedPathAmplitude M hM K.shape x q := by
  unfold boundedKernelNormalizedPathFunction
    boundedKernelNormalizedPathAmplitude
  rw [ContinuousMap.prod_apply]
  rfl

/-- Uncorrected normalized core integrand as a continuous function. -/
def boundedKernelNormalizedCoreIntegrandFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) : C((Fin K.shape.1.val → S), ℂ) :=
  boundedKernelBranchProfileFunction M hM K q *
    boundedKernelNormalizedPathFunction M hM K q

theorem boundedKernelNormalizedCoreIntegrandFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell) :
    AnalyticAt ℂ (boundedKernelNormalizedCoreIntegrandFunction M hM K)
      (0, 0) :=
  (boundedKernelBranchProfileFunction_analytic M hM K).mul
    (boundedKernelNormalizedPathFunction_analytic M hM K)

@[simp] theorem boundedKernelNormalizedCoreIntegrandFunction_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    boundedKernelNormalizedCoreIntegrandFunction M hM K q x =
      boundedKernelNormalizedCoreIntegrand M hM K.shape x q := by
  simp [boundedKernelNormalizedCoreIntegrandFunction,
    boundedKernelNormalizedCoreIntegrand]

/-! ## Continuous-function form of the finite admissibility correction -/

private def boundedKernelFixedLengthEdgeFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (n : ℕ) (q : C(S, ℂ) × ℂ) :
    C((Fin K.shape.1.val → S), ℂ) :=
  boundedKernelEdgePullbackCLM K e (cubicFixedLengthPathKernel M hM n q)

private theorem boundedKernelFixedLengthEdgeFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (n : ℕ) :
    AnalyticAt ℂ (boundedKernelFixedLengthEdgeFunction M hM K e n)
      (0, 0) :=
  ((boundedKernelEdgePullbackCLM K e :
      C(S × S, ℂ) →L[ℂ] C((Fin K.shape.1.val → S), ℂ))).analyticAt _
    |>.comp_of_eq
    (cubicFixedLengthPathKernel_analytic M hM n) rfl

private def boundedKernelForbiddenNormalizedPatternEdgeFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ) :
    C((Fin K.shape.1.val → S), ℂ) :=
  if BoundedKernelForbiddenPatternForcesEdge J e then
    q.2 • boundedKernelFixedLengthEdgeFunction M hM K e
      (boundedKernelForbiddenPatternLength J e) q
  else
    boundedKernelNormalizedEdgeFunction M hM K e q

private theorem boundedKernelForbiddenNormalizedPatternEdgeFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) :
    AnalyticAt ℂ
      (boundedKernelForbiddenNormalizedPatternEdgeFunction M hM K J e)
      (0, 0) := by
  classical
  unfold boundedKernelForbiddenNormalizedPatternEdgeFunction
  split_ifs
  · exact analyticAt_snd.smul
      (boundedKernelFixedLengthEdgeFunction_analytic M hM K e
        (boundedKernelForbiddenPatternLength J e))
  · exact boundedKernelNormalizedEdgeFunction_analytic M hM K e

@[simp] private theorem
    boundedKernelForbiddenNormalizedPatternEdgeFunction_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S) :
    boundedKernelForbiddenNormalizedPatternEdgeFunction M hM K J e q x =
      boundedKernelForbiddenNormalizedPatternEdgeFactor M hM K J e q x := by
  classical
  by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
  · simp [boundedKernelForbiddenNormalizedPatternEdgeFunction,
      boundedKernelForbiddenNormalizedPatternEdgeFactor, he,
      boundedKernelFixedLengthEdgeFunction,
      boundedKernelFixedLengthEdgeFactor]
    left
    exact cubicFixedLengthPathKernel_apply M hM
      (boundedKernelForbiddenPatternLength J e) q
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2)
  · simp [boundedKernelForbiddenNormalizedPatternEdgeFunction,
      boundedKernelForbiddenNormalizedPatternEdgeFactor, he]

private def boundedKernelForbiddenNormalizedIntersectionFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) : C((Fin K.shape.1.val → S), ℂ) :=
  if BoundedKernelForbiddenPatternCompatible J then
    boundedKernelBranchProfileFunction M hM K q *
      ∏ e : Fin K.shape.2.1.val,
        boundedKernelForbiddenNormalizedPatternEdgeFunction M hM K J e q
  else 0

private theorem boundedKernelForbiddenNormalizedIntersectionFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K)) :
    AnalyticAt ℂ
      (boundedKernelForbiddenNormalizedIntersectionFunction M hM K J)
      (0, 0) := by
  classical
  unfold boundedKernelForbiddenNormalizedIntersectionFunction
  split_ifs
  · exact (boundedKernelBranchProfileFunction_analytic M hM K).mul
      ((Finset.univ : Finset (Fin K.shape.2.1.val)).analyticAt_fun_prod
        (fun e _ ↦
          boundedKernelForbiddenNormalizedPatternEdgeFunction_analytic
            M hM K J e))
  · exact analyticAt_const

@[simp] private theorem
    boundedKernelForbiddenNormalizedIntersectionFunction_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    boundedKernelForbiddenNormalizedIntersectionFunction M hM K J q x =
      boundedKernelForbiddenNormalizedIntersection M hM K J q x := by
  classical
  by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
  · simp [boundedKernelForbiddenNormalizedIntersectionFunction,
      boundedKernelForbiddenNormalizedIntersection, hcompat]
  · simp [boundedKernelForbiddenNormalizedIntersectionFunction,
      boundedKernelForbiddenNormalizedIntersection, hcompat]

/-- Continuous-function-valued finite admissibility correction. -/
def boundedKernelNormalizedForbiddenCorrectionFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) : C((Fin K.shape.1.val → S), ℂ) := by
  letI := boundedKernelForbiddenLengthWitnessFintype K
  exact ∑ J ∈ (Finset.univ :
      Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
        Finset.Nonempty,
    (-1 : ℂ) ^ (J.card + 1) •
      boundedKernelForbiddenNormalizedIntersectionFunction M hM K J q

theorem boundedKernelNormalizedForbiddenCorrectionFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell) :
    AnalyticAt ℂ
      (boundedKernelNormalizedForbiddenCorrectionFunction M hM K)
      (0, 0) := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  unfold boundedKernelNormalizedForbiddenCorrectionFunction
  let s := (Finset.univ :
    Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
      Finset.Nonempty
  let F : Finset (BoundedKernelForbiddenLengthWitness K) →
      (C(S, ℂ) × ℂ → C((Fin K.shape.1.val → S), ℂ)) :=
    fun J q ↦ (-1 : ℂ) ^ (J.card + 1) •
      boundedKernelForbiddenNormalizedIntersectionFunction M hM K J q
  change AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦
    ∑ J ∈ s, F J q) (0, 0)
  have hsum : AnalyticAt ℂ (∑ J ∈ s, F J) (0, 0) := by
    apply Finset.analyticAt_sum
    intro J _
    have hconst : AnalyticAt ℂ
        (fun _q : C(S, ℂ) × ℂ ↦ (-1 : ℂ) ^ (J.card + 1)) (0, 0) :=
      analyticAt_const
    exact hconst.smul
      (boundedKernelForbiddenNormalizedIntersectionFunction_analytic
        M hM K J)
  have hfun : (∑ J ∈ s, F J) =
      (fun q : C(S, ℂ) × ℂ ↦ ∑ J ∈ s, F J q) := by
    funext q
    exact Finset.sum_apply q s F
  rw [← hfun]
  exact hsum

@[simp] theorem boundedKernelNormalizedForbiddenCorrectionFunction_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    boundedKernelNormalizedForbiddenCorrectionFunction M hM K q x =
      boundedKernelNormalizedForbiddenCorrection M hM K q x := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  unfold boundedKernelNormalizedForbiddenCorrectionFunction
    boundedKernelNormalizedForbiddenCorrection
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    boundedKernelForbiddenNormalizedIntersectionFunction_apply]

/-- Genuine admissible pole-removed integrand, now valued in the Banach
space of continuous branch-coordinate functions. -/
def boundedKernelAdmissibleNormalizedIntegrandFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) : C((Fin K.shape.1.val → S), ℂ) :=
  boundedKernelNormalizedCoreIntegrandFunction M hM K q -
    boundedKernelNormalizedForbiddenCorrectionFunction M hM K q

theorem boundedKernelAdmissibleNormalizedIntegrandFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell) :
    AnalyticAt ℂ
      (boundedKernelAdmissibleNormalizedIntegrandFunction M hM K)
      (0, 0) :=
  (boundedKernelNormalizedCoreIntegrandFunction_analytic M hM K).sub
    (boundedKernelNormalizedForbiddenCorrectionFunction_analytic M hM K)

@[simp] theorem boundedKernelAdmissibleNormalizedIntegrandFunction_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    boundedKernelAdmissibleNormalizedIntegrandFunction M hM K q x =
      boundedKernelAdmissibleNormalizedCoreIntegrand M hM K q x := by
  simp [boundedKernelAdmissibleNormalizedIntegrandFunction,
    boundedKernelAdmissibleNormalizedCoreIntegrand]

/-! ## Cubic normalization before and after branch integration -/

/-- Cubic-normalized admissible integrand of one connected noncubic kernel. -/
def connectedNoncubicKernelCubicNormalizedIntegrandFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (q : C(S, ℂ) × ℂ) :
    C((Fin K.1.toLabelledBoundedKernel.shape.1.val → S), ℂ) :=
  q.2 ^ (3 * ell -
      K.1.toLabelledBoundedKernel.shape.2.1.val) •
    boundedKernelAdmissibleNormalizedIntegrandFunction M hM
      K.1.toLabelledBoundedKernel q

theorem connectedNoncubicKernelCubicNormalizedIntegrandFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell) :
    AnalyticAt ℂ
      (connectedNoncubicKernelCubicNormalizedIntegrandFunction M hM K)
      (0, 0) :=
  (analyticAt_snd.pow
      (3 * ell - K.1.toLabelledBoundedKernel.shape.2.1.val)).smul
    (boundedKernelAdmissibleNormalizedIntegrandFunction_analytic
      M hM K.1.toLabelledBoundedKernel)

/-- Continuous-function-valued analytic remainder after removing the one
explicit fold coordinate. -/
def connectedNoncubicKernelIntegratedRemainderFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (q : C(S, ℂ) × ℂ) :
    C((Fin K.1.toLabelledBoundedKernel.shape.1.val → S), ℂ) :=
  q.2 ^ (3 * ell -
      K.1.toLabelledBoundedKernel.shape.2.1.val - 1) •
    boundedKernelAdmissibleNormalizedIntegrandFunction M hM
      K.1.toLabelledBoundedKernel q

theorem connectedNoncubicKernelIntegratedRemainderFunction_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell) :
    AnalyticAt ℂ
      (connectedNoncubicKernelIntegratedRemainderFunction M hM K)
      (0, 0) :=
  (analyticAt_snd.pow
      (3 * ell - K.1.toLabelledBoundedKernel.shape.2.1.val - 1)).smul
    (boundedKernelAdmissibleNormalizedIntegrandFunction_analytic
      M hM K.1.toLabelledBoundedKernel)

theorem connectedNoncubicKernelCubicNormalizedIntegrandFunction_eq_X_smul
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (q : C(S, ℂ) × ℂ) :
    connectedNoncubicKernelCubicNormalizedIntegrandFunction M hM K q =
      q.2 • connectedNoncubicKernelIntegratedRemainderFunction M hM K q := by
  ext x
  simp only [connectedNoncubicKernelCubicNormalizedIntegrandFunction,
    connectedNoncubicKernelIntegratedRemainderFunction,
    ContinuousMap.smul_apply, smul_eq_mul,
    boundedKernelAdmissibleNormalizedIntegrandFunction_apply]
  exact connectedNoncubicKernel_cubicNormalizedAdmissible_eq_X_mul
    M hM K q x

/-- Product measure on the branch coordinates of a bounded kernel. -/
def boundedKernelBranchProductMeasure
    (M : CompactBJRModel S) {ell : ℕ} (K : LabelledBoundedKernel ell) :
    Measure (Fin K.shape.1.val → S) :=
  Measure.pi (fun _ : Fin K.shape.1.val ↦ M.mu)

private instance boundedKernelBranchProductMeasure_isFinite
    (M : CompactBJRModel S) {ell : ℕ} (K : LabelledBoundedKernel ell) :
    IsFiniteMeasure (boundedKernelBranchProductMeasure M K) := by
  unfold boundedKernelBranchProductMeasure
  infer_instance

/-- Continuous linear integration over all branch coordinates of one
bounded kernel. -/
def boundedKernelBranchIntegralCLM
    (M : CompactBJRModel S) {ell : ℕ} (K : LabelledBoundedKernel ell) :
    C((Fin K.shape.1.val → S), ℂ) →L[ℂ] ℂ :=
  (MeasureTheory.L1.integralCLM'
      (α := Fin K.shape.1.val → S) (E := ℂ)
      (μ := boundedKernelBranchProductMeasure M K) ℂ).comp
    (ContinuousMap.toLp 1 (boundedKernelBranchProductMeasure M K) ℂ)

theorem boundedKernelBranchIntegralCLM_apply
    (M : CompactBJRModel S) {ell : ℕ} (K : LabelledBoundedKernel ell)
    (f : C((Fin K.shape.1.val → S), ℂ)) :
    boundedKernelBranchIntegralCLM M K f =
      ∫ x : Fin K.shape.1.val → S, f x
        ∂boundedKernelBranchProductMeasure M K := by
  unfold boundedKernelBranchIntegralCLM
  rw [ContinuousLinearMap.comp_apply, ← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  apply integral_congr_ae
  exact ContinuousMap.coeFn_toLp
    (p := 1) (μ := boundedKernelBranchProductMeasure M K) (𝕜 := ℂ) f

/-- Integrated cubic-normalized genuine admissible amplitude of one fixed
connected noncubic bounded kernel. -/
def connectedNoncubicKernelIntegratedAmplitude
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (q : C(S, ℂ) × ℂ) : ℂ :=
  boundedKernelBranchIntegralCLM M K.1.toLabelledBoundedKernel
    (connectedNoncubicKernelCubicNormalizedIntegrandFunction M hM K q)

theorem connectedNoncubicKernelIntegratedAmplitude_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell) :
    AnalyticAt ℂ (connectedNoncubicKernelIntegratedAmplitude M hM K)
      (0, 0) :=
  (boundedKernelBranchIntegralCLM M
      K.1.toLabelledBoundedKernel).analyticAt _ |>.comp
    (connectedNoncubicKernelCubicNormalizedIntegrandFunction_analytic
      M hM K)

/-- Integrated analytic remainder for one fixed noncubic kernel. -/
def connectedNoncubicKernelIntegratedRemainder
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (q : C(S, ℂ) × ℂ) : ℂ :=
  boundedKernelBranchIntegralCLM M K.1.toLabelledBoundedKernel
    (connectedNoncubicKernelIntegratedRemainderFunction M hM K q)

theorem connectedNoncubicKernelIntegratedRemainder_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell) :
    AnalyticAt ℂ (connectedNoncubicKernelIntegratedRemainder M hM K)
      (0, 0) :=
  (boundedKernelBranchIntegralCLM M
      K.1.toLabelledBoundedKernel).analyticAt _ |>.comp
    (connectedNoncubicKernelIntegratedRemainderFunction_analytic M hM K)

theorem connectedNoncubicKernelIntegratedAmplitude_eq_X_mul
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (q : C(S, ℂ) × ℂ) :
    connectedNoncubicKernelIntegratedAmplitude M hM K q =
      q.2 * connectedNoncubicKernelIntegratedRemainder M hM K q := by
  unfold connectedNoncubicKernelIntegratedAmplitude
    connectedNoncubicKernelIntegratedRemainder
  rw [connectedNoncubicKernelCubicNormalizedIntegrandFunction_eq_X_smul,
    map_smul]
  simp only [smul_eq_mul]

/-! ## The finite inverse-coordinate-multiplicity sum -/

/-- Reciprocal of the already proved finite coordinate multiplicity.  This
includes branch-coordinate permutations, edge-coordinate permutations, and
the independent reversal of every loop label. -/
def labelledConnectedNoncubicKernelInverseCoordinateMultiplicity
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell) : ℂ :=
  ((K.1.toLabelledBoundedKernel.coordinateMultiplicity : ℕ) : ℂ)⁻¹

theorem labelledConnectedNoncubicKernelInverseCoordinateMultiplicity_eq
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell) :
    labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K =
      (((K.1.toLabelledBoundedKernel.shape.1.val.factorial *
          K.1.toLabelledBoundedKernel.shape.2.1.val.factorial *
          2 ^ Fintype.card
            (BoundedKernelLoopEdge K.1.toLabelledBoundedKernel) : ℕ) : ℂ))⁻¹ := by
  rfl

/-- Finite weighted sum of the genuine cubic-normalized admissible
amplitudes of every connected noncubic bounded kernel of surplus `ell`. -/
def positiveSurplusNoncubicIntegratedAmplitude
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) : ℂ :=
  letI := labelledConnectedNoncubicKernelFintype ell
  ∑ K : LabelledConnectedNoncubicKernel ell,
    labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K *
      connectedNoncubicKernelIntegratedAmplitude M hM K q

theorem positiveSurplusNoncubicIntegratedAmplitude_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    AnalyticAt ℂ (positiveSurplusNoncubicIntegratedAmplitude M hM ell)
      (0, 0) := by
  let _ := labelledConnectedNoncubicKernelFintype ell
  unfold positiveSurplusNoncubicIntegratedAmplitude
  let F : LabelledConnectedNoncubicKernel ell →
      (C(S, ℂ) × ℂ → ℂ) := fun K q ↦
    labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K *
      connectedNoncubicKernelIntegratedAmplitude M hM K q
  change AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦ ∑ K, F K q)
    (0, 0)
  have hsum : AnalyticAt ℂ (∑ K, F K) (0, 0) := by
    apply Finset.analyticAt_sum Finset.univ
    intro K _
    exact analyticAt_const.mul
      (connectedNoncubicKernelIntegratedAmplitude_analytic M hM K)
  have hfun : (∑ K, F K) =
      (fun q : C(S, ℂ) × ℂ ↦ ∑ K, F K q) := by
    funext q
    exact Fintype.sum_apply q F
  rw [← hfun]
  exact hsum

/-- The corresponding finite weighted analytic remainder sum. -/
def positiveSurplusNoncubicIntegratedRemainder
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) : ℂ :=
  letI := labelledConnectedNoncubicKernelFintype ell
  ∑ K : LabelledConnectedNoncubicKernel ell,
    labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K *
      connectedNoncubicKernelIntegratedRemainder M hM K q

theorem positiveSurplusNoncubicIntegratedRemainder_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) :
    AnalyticAt ℂ (positiveSurplusNoncubicIntegratedRemainder M hM ell)
      (0, 0) := by
  let _ := labelledConnectedNoncubicKernelFintype ell
  unfold positiveSurplusNoncubicIntegratedRemainder
  let F : LabelledConnectedNoncubicKernel ell →
      (C(S, ℂ) × ℂ → ℂ) := fun K q ↦
    labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K *
      connectedNoncubicKernelIntegratedRemainder M hM K q
  change AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦ ∑ K, F K q)
    (0, 0)
  have hsum : AnalyticAt ℂ (∑ K, F K) (0, 0) := by
    apply Finset.analyticAt_sum Finset.univ
    intro K _
    exact analyticAt_const.mul
      (connectedNoncubicKernelIntegratedRemainder_analytic M hM K)
  have hfun : (∑ K, F K) =
      (fun q : C(S, ℂ) × ℂ ↦ ∑ K, F K q) := by
    funext q
    exact Fintype.sum_apply q F
  rw [← hfun]
  exact hsum

/-- The complete finite noncubic bounded-kernel presentation sum has one
explicit fold-coordinate factor. -/
theorem positiveSurplusNoncubicIntegratedAmplitude_eq_X_mul
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) :
    positiveSurplusNoncubicIntegratedAmplitude M hM ell q =
      q.2 * positiveSurplusNoncubicIntegratedRemainder M hM ell q := by
  let _ := labelledConnectedNoncubicKernelFintype ell
  unfold positiveSurplusNoncubicIntegratedAmplitude
    positiveSurplusNoncubicIntegratedRemainder
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [connectedNoncubicKernelIntegratedAmplitude_eq_X_mul]
  ring

end PerronWright.GraphCore
