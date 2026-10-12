import PerronWright.Enumeration.PositiveSurplusNoncubicIntegratedAmplitude
import PerronWright.Enumeration.PositiveSurplusCubicProfileAnalytic

/-!
# The noncubic strict-profile functional and its exact fold-chart bridge

For each connected noncubic bounded kernel, this file forms the genuine
finite inclusion--exclusion resolvent on an arbitrary strict-subcritical
profile.  It integrates over the branch coordinates and then takes the
finite inverse-coordinate-multiplicity sum.

The resulting away-chart functional is analytic on the open unit profile
ball.  On the punctured local fold chart it agrees exactly with the
cubic-normalized local amplitude, with the full factor `X ^ (3 * ell)`.
No graph-series identification is asserted here: this is an exact bridge
between the two already constructed kernel/length-profile charts.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## Profile-valued bounded-kernel factors -/

private def noncubicProfileVertexCoordinateMap
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (v : Fin K.shape.1.val) : C((Fin K.shape.1.val → S), S) :=
  ⟨fun x ↦ x v, continuous_apply v⟩

private def noncubicProfileVertexPullbackCLM
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (v : Fin K.shape.1.val) :
    C(S, ℂ) →L[ℂ] C((Fin K.shape.1.val → S), ℂ) :=
  ContinuousMap.compCLM ℂ ℂ (noncubicProfileVertexCoordinateMap K v)

private def noncubicProfileEdgeCoordinateMap
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) :
    C((Fin K.shape.1.val → S), S × S) :=
  ⟨fun x ↦
      (x (boundedKernelOrderedEndpoints K.shape e).1,
        x (boundedKernelOrderedEndpoints K.shape e).2),
    (continuous_apply (boundedKernelOrderedEndpoints K.shape e).1).prodMk
      (continuous_apply (boundedKernelOrderedEndpoints K.shape e).2)⟩

private def noncubicProfileEdgePullbackCLM
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) :
    C(S × S, ℂ) →L[ℂ] C((Fin K.shape.1.val → S), ℂ) :=
  ContinuousMap.compCLM ℂ ℂ (noncubicProfileEdgeCoordinateMap K e)

/-- Product of a generic profile over the branch coordinates of one
bounded kernel. -/
def boundedKernelProfileBranchFunction
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) : C((Fin K.shape.1.val → S), ℂ) :=
  ∏ v : Fin K.shape.1.val, noncubicProfileVertexPullbackCLM K v tau

omit [MeasurableSpace S] [BorelSpace S] in
theorem boundedKernelProfileBranchFunction_analytic
    {ell : ℕ} (K : LabelledBoundedKernel ell) (tau : C(S, ℂ)) :
    AnalyticAt ℂ (boundedKernelProfileBranchFunction (S := S) K) tau := by
  unfold boundedKernelProfileBranchFunction
  exact (Finset.univ : Finset (Fin K.shape.1.val)).analyticAt_fun_prod
    (fun v _ ↦ (noncubicProfileVertexPullbackCLM K v).analyticAt tau)

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem boundedKernelProfileBranchFunction_apply
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S) :
    boundedKernelProfileBranchFunction K tau x =
      ∏ v : Fin K.shape.1.val, tau (x v) := by
  simp [boundedKernelProfileBranchFunction,
    noncubicProfileVertexPullbackCLM,
    noncubicProfileVertexCoordinateMap]

private def boundedKernelProfileFixedLengthPathKernel
    (M : CompactBJRModel S) (n : ℕ) (tau : C(S, ℂ)) :
    C(S × S, ℂ) :=
  PerronWright.MarkedPathResolvent.operatorKernelize M
    ((PerronWright.MarkedPathResolvent.pathOperatorParameterCLM M tau) ^ n)

private theorem boundedKernelProfileFixedLengthPathKernel_analytic
    (M : CompactBJRModel S) (n : ℕ) (tau : C(S, ℂ)) :
    AnalyticAt ℂ (boundedKernelProfileFixedLengthPathKernel M n) tau := by
  unfold boundedKernelProfileFixedLengthPathKernel
  have hpow : AnalyticAt ℂ
      (fun sigma : C(S, ℂ) ↦
        (PerronWright.MarkedPathResolvent.pathOperatorParameterCLM M sigma) ^ n)
      tau :=
    ((PerronWright.MarkedPathResolvent.pathOperatorParameterCLM M).analyticAt
      tau).pow n
  exact (PerronWright.MarkedPathResolvent.operatorKernelize M).analyticAt _
    |>.comp_of_eq hpow rfl

private def boundedKernelProfileFixedLengthEdgeFunction
    (M : CompactBJRModel S) {ell : ℕ}
    (K : LabelledBoundedKernel ell) (e : Fin K.shape.2.1.val)
    (n : ℕ) (tau : C(S, ℂ)) :
    C((Fin K.shape.1.val → S), ℂ) :=
  noncubicProfileEdgePullbackCLM K e
    (boundedKernelProfileFixedLengthPathKernel M n tau)

private theorem boundedKernelProfileFixedLengthEdgeFunction_analytic
    (M : CompactBJRModel S) {ell : ℕ}
    (K : LabelledBoundedKernel ell) (e : Fin K.shape.2.1.val)
    (n : ℕ) (tau : C(S, ℂ)) :
    AnalyticAt ℂ (boundedKernelProfileFixedLengthEdgeFunction M K e n)
      tau := by
  unfold boundedKernelProfileFixedLengthEdgeFunction
  exact (noncubicProfileEdgePullbackCLM K e).analyticAt _ |>.comp_of_eq
    (boundedKernelProfileFixedLengthPathKernel_analytic M n tau) rfl

@[simp] private theorem boundedKernelProfileFixedLengthEdgeFunction_apply
    (M : CompactBJRModel S) {ell : ℕ}
    (K : LabelledBoundedKernel ell) (e : Fin K.shape.2.1.val)
    (n : ℕ) (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S) :
    boundedKernelProfileFixedLengthEdgeFunction M K e n tau x =
      profilePathEdgeCoefficient M tau
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) n := by
  rfl

/-- The generic profile resolvent pulled back along one bounded-kernel
edge. -/
def boundedKernelProfileResolventEdgeFunction
    (M : CompactBJRModel S) {ell : ℕ}
    (K : LabelledBoundedKernel ell) (e : Fin K.shape.2.1.val)
    (tau : C(S, ℂ)) : C((Fin K.shape.1.val → S), ℂ) :=
  noncubicProfileEdgePullbackCLM K e (profilePathResolventKernel M tau)

theorem boundedKernelProfileResolventEdgeFunction_analyticAt_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ (boundedKernelProfileResolventEdgeFunction M K e)
      tau := by
  unfold boundedKernelProfileResolventEdgeFunction
  exact (noncubicProfileEdgePullbackCLM K e).analyticAt _ |>.comp_of_eq
    (profilePathResolventKernel_analyticAt_of_norm_lt_one M hM htau) rfl

@[simp] theorem boundedKernelProfileResolventEdgeFunction_apply
    (M : CompactBJRModel S) {ell : ℕ}
    (K : LabelledBoundedKernel ell) (e : Fin K.shape.2.1.val)
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S) :
    boundedKernelProfileResolventEdgeFunction M K e tau x =
      profilePathResolventKernel M tau
        (x (boundedKernelOrderedEndpoints K.shape e).1,
          x (boundedKernelOrderedEndpoints K.shape e).2) := by
  rfl

/-! ## Finite generic-profile admissibility correction -/

private def boundedKernelProfileForbiddenPatternEdgeFunction
    (M : CompactBJRModel S) {ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (tau : C(S, ℂ)) :
    C((Fin K.shape.1.val → S), ℂ) :=
  if BoundedKernelForbiddenPatternForcesEdge J e then
    boundedKernelProfileFixedLengthEdgeFunction M K e
      (boundedKernelForbiddenPatternLength J e) tau
  else
    boundedKernelProfileResolventEdgeFunction M K e tau

private theorem
    boundedKernelProfileForbiddenPatternEdgeFunction_analyticAt_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ
      (boundedKernelProfileForbiddenPatternEdgeFunction M K J e) tau := by
  classical
  unfold boundedKernelProfileForbiddenPatternEdgeFunction
  split_ifs
  · exact boundedKernelProfileFixedLengthEdgeFunction_analytic
      M K e (boundedKernelForbiddenPatternLength J e) tau
  · exact boundedKernelProfileResolventEdgeFunction_analyticAt_of_norm_lt_one
      M hM K e htau

private def boundedKernelProfileForbiddenIntersectionFunction
    (M : CompactBJRModel S) {ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (tau : C(S, ℂ)) : C((Fin K.shape.1.val → S), ℂ) :=
  if BoundedKernelForbiddenPatternCompatible J then
    boundedKernelProfileBranchFunction K tau *
      ∏ e : Fin K.shape.2.1.val,
        boundedKernelProfileForbiddenPatternEdgeFunction M K J e tau
  else 0

private theorem
    boundedKernelProfileForbiddenIntersectionFunction_analyticAt_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ
      (boundedKernelProfileForbiddenIntersectionFunction M K J) tau := by
  classical
  unfold boundedKernelProfileForbiddenIntersectionFunction
  split_ifs
  · exact (boundedKernelProfileBranchFunction_analytic K tau).mul
      ((Finset.univ : Finset (Fin K.shape.2.1.val)).analyticAt_fun_prod
        (fun e _ ↦
          boundedKernelProfileForbiddenPatternEdgeFunction_analyticAt_of_norm_lt_one
            M hM K J e htau))
  · exact analyticAt_const

/-- Continuous-function-valued finite inclusion--exclusion correction for
one bounded kernel and one generic profile. -/
def boundedKernelProfileForbiddenCorrectionFunction
    (M : CompactBJRModel S) {ell : ℕ}
    (K : LabelledBoundedKernel ell) (tau : C(S, ℂ)) :
    C((Fin K.shape.1.val → S), ℂ) := by
  letI := boundedKernelForbiddenLengthWitnessFintype K
  exact ∑ J ∈ (Finset.univ :
      Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
        Finset.Nonempty,
    (-1 : ℂ) ^ (J.card + 1) •
      boundedKernelProfileForbiddenIntersectionFunction M K J tau

theorem
    boundedKernelProfileForbiddenCorrectionFunction_analyticAt_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ
      (boundedKernelProfileForbiddenCorrectionFunction M K) tau := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  unfold boundedKernelProfileForbiddenCorrectionFunction
  let s := (Finset.univ :
    Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
      Finset.Nonempty
  let F : Finset (BoundedKernelForbiddenLengthWitness K) →
      (C(S, ℂ) → C((Fin K.shape.1.val → S), ℂ)) := fun J sigma ↦
    (-1 : ℂ) ^ (J.card + 1) •
      boundedKernelProfileForbiddenIntersectionFunction M K J sigma
  change AnalyticAt ℂ
    (fun sigma : C(S, ℂ) ↦ ∑ J ∈ s, F J sigma) tau
  have hsum : AnalyticAt ℂ (∑ J ∈ s, F J) tau := by
    apply Finset.analyticAt_sum
    intro J _
    have hconst : AnalyticAt ℂ
        (fun _sigma : C(S, ℂ) ↦ (-1 : ℂ) ^ (J.card + 1)) tau :=
      analyticAt_const
    exact hconst.smul
      (boundedKernelProfileForbiddenIntersectionFunction_analyticAt_of_norm_lt_one
        M hM K J htau)
  have hfun : (∑ J ∈ s, F J) =
      (fun sigma : C(S, ℂ) ↦ ∑ J ∈ s, F J sigma) := by
    funext sigma
    exact Finset.sum_apply sigma s F
  rw [← hfun]
  exact hsum

/-- The unrestricted generic-profile resolvent product for one bounded
kernel. -/
def boundedKernelProfileUnrestrictedFunction
    (M : CompactBJRModel S) {ell : ℕ}
    (K : LabelledBoundedKernel ell) (tau : C(S, ℂ)) :
    C((Fin K.shape.1.val → S), ℂ) :=
  boundedKernelProfileBranchFunction K tau *
    ∏ e : Fin K.shape.2.1.val,
      boundedKernelProfileResolventEdgeFunction M K e tau

theorem boundedKernelProfileUnrestrictedFunction_analyticAt_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ (boundedKernelProfileUnrestrictedFunction M K) tau := by
  unfold boundedKernelProfileUnrestrictedFunction
  exact (boundedKernelProfileBranchFunction_analytic K tau).mul
    ((Finset.univ : Finset (Fin K.shape.2.1.val)).analyticAt_fun_prod
      (fun e _ ↦
        boundedKernelProfileResolventEdgeFunction_analyticAt_of_norm_lt_one
          M hM K e htau))

/-- Resolvent minus the finite forbidden-pattern correction.  This is the
away-chart realization of the genuine admissible length-profile sum for
one bounded kernel. -/
def boundedKernelAdmissibleProfileIntegrandFunction
    (M : CompactBJRModel S) {ell : ℕ}
    (K : LabelledBoundedKernel ell) (tau : C(S, ℂ)) :
    C((Fin K.shape.1.val → S), ℂ) :=
  boundedKernelProfileUnrestrictedFunction M K tau -
    boundedKernelProfileForbiddenCorrectionFunction M K tau

theorem
    boundedKernelAdmissibleProfileIntegrandFunction_analyticAt_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ (boundedKernelAdmissibleProfileIntegrandFunction M K)
      tau :=
  (boundedKernelProfileUnrestrictedFunction_analyticAt_of_norm_lt_one
    M hM K htau).sub
    (boundedKernelProfileForbiddenCorrectionFunction_analyticAt_of_norm_lt_one
      M hM K htau)

/-! ## Literal generic-profile identification -/

/-- Literal admissible all-length integrand for an arbitrary profile.  The
admissibility predicate is exactly the one represented by
`BoundedKernelLengthProfile`. -/
def boundedKernelLiteralAdmissibleProfileIntegrand
    (M : CompactBJRModel S) {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S) : ℂ :=
  (∏ v : Fin K.shape.1.val, tau (x v)) *
    ∑' l : Fin K.shape.2.1.val → ℕ,
      if BoundedKernelLengthAssignment.IsAdmissible K
          (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin K.shape.2.1.val,
          profilePathEdgeCoefficient M tau
            (x (boundedKernelOrderedEndpoints K.shape e).1)
            (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
      else 0

private def boundedKernelLiteralUnrestrictedProfileIntegrand
    (M : CompactBJRModel S) {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S) : ℂ :=
  (∏ v : Fin K.shape.1.val, tau (x v)) *
    ∑' l : Fin K.shape.2.1.val → ℕ,
      ∏ e : Fin K.shape.2.1.val,
        profilePathEdgeCoefficient M tau
          (x (boundedKernelOrderedEndpoints K.shape e).1)
          (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)

private def boundedKernelLiteralForbiddenProfileIntegrand
    (M : CompactBJRModel S) {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S) : ℂ :=
  (∏ v : Fin K.shape.1.val, tau (x v)) *
    ∑' l : Fin K.shape.2.1.val → ℕ,
      if ∃ w : BoundedKernelForbiddenLengthWitness K,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin K.shape.2.1.val,
          profilePathEdgeCoefficient M tau
            (x (boundedKernelOrderedEndpoints K.shape e).1)
            (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
      else 0

private theorem boundedKernelProfileAssignmentProduct_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    Summable (fun l : Fin K.shape.2.1.val → ℕ ↦
      ∏ e : Fin K.shape.2.1.val,
        profilePathEdgeCoefficient M tau
          (x (boundedKernelOrderedEndpoints K.shape e).1)
          (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)) := by
  exact (summable_finFunction_prod_and_tsum
    (fun e n ↦ profilePathEdgeCoefficient M tau
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2) n)
    (fun e ↦ summable_profilePathEdgeCoefficient M hM tau r hr hr1 htau
      _ _)).1

private theorem boundedKernelProfileUnrestrictedFunction_eq_literal
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    boundedKernelProfileUnrestrictedFunction M K tau x =
      boundedKernelLiteralUnrestrictedProfileIntegrand M K tau x := by
  unfold boundedKernelProfileUnrestrictedFunction
    boundedKernelLiteralUnrestrictedProfileIntegrand
  rw [ContinuousMap.mul_apply, ContinuousMap.prod_apply,
    boundedKernelProfileBranchFunction_apply]
  apply congrArg (fun z : ℂ ↦
    (∏ v : Fin K.shape.1.val, tau (x v)) * z)
  rw [(summable_finFunction_prod_and_tsum
    (fun e n ↦ profilePathEdgeCoefficient M tau
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2) n)
    (fun e ↦ summable_profilePathEdgeCoefficient M hM tau r hr hr1 htau
      _ _)).2]
  apply Finset.prod_congr rfl
  intro e _
  rw [boundedKernelProfileResolventEdgeFunction_apply]
  exact tsum_profilePathEdgeCoefficient_eq_profilePathResolventKernel
    M hM tau r hr hr1 htau _ _ |>.symm

private theorem boundedKernelLiteralAdmissible_add_forbidden_profile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    boundedKernelLiteralAdmissibleProfileIntegrand M K tau x +
        boundedKernelLiteralForbiddenProfileIntegrand M K tau x =
      boundedKernelLiteralUnrestrictedProfileIntegrand M K tau x := by
  classical
  let B : (Fin K.shape.2.1.val → ℕ) → ℂ := fun l ↦
    ∏ e : Fin K.shape.2.1.val,
      profilePathEdgeCoefficient M tau
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
  let A : Set (Fin K.shape.2.1.val → ℕ) := {l |
    BoundedKernelLengthAssignment.IsAdmissible K
      (Finsupp.equivFunOnFinite.symm l)}
  let F : Set (Fin K.shape.2.1.val → ℕ) := {l |
    ∃ w : BoundedKernelForbiddenLengthWitness K,
      w.Occurs (Finsupp.equivFunOnFinite.symm l)}
  have hB : Summable B :=
    boundedKernelProfileAssignmentProduct_summable
      M hM K tau x r hr hr1 htau
  have hA : Summable (A.indicator B) := hB.indicator A
  have hF : Summable (F.indicator B) := hB.indicator F
  have hterm (l : Fin K.shape.2.1.val → ℕ) :
      A.indicator B l + F.indicator B l = B l := by
    have hiff := not_boundedKernelLengthAssignment_admissible_iff K
      (Finsupp.equivFunOnFinite.symm l)
    by_cases ha : BoundedKernelLengthAssignment.IsAdmissible K
        (Finsupp.equivFunOnFinite.symm l)
    · have hf : ¬ ∃ w : BoundedKernelForbiddenLengthWitness K,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) :=
        fun hw ↦ (hiff.mpr hw) ha
      have hAl : l ∈ A := by simpa [A] using ha
      have hFl : l ∉ F := by simpa [F] using hf
      simp [Set.indicator, hAl, hFl]
    · have hf : ∃ w : BoundedKernelForbiddenLengthWitness K,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) := hiff.mp ha
      have hAl : l ∉ A := by simpa [A] using ha
      have hFl : l ∈ F := by simpa [F] using hf
      simp [Set.indicator, hAl, hFl]
  unfold boundedKernelLiteralAdmissibleProfileIntegrand
    boundedKernelLiteralForbiddenProfileIntegrand
    boundedKernelLiteralUnrestrictedProfileIntegrand
  rw [← mul_add]
  apply congrArg (fun z : ℂ ↦
    (∏ v : Fin K.shape.1.val, tau (x v)) * z)
  change (∑' l, A.indicator B l) + (∑' l, F.indicator B l) =
    ∑' l, B l
  rw [← hA.tsum_add hF]
  exact tsum_congr hterm

private def boundedKernelProfileForbiddenPatternEdgeCoefficient
    (M : CompactBJRModel S) {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (tau : C(S, ℂ))
    (x : Fin K.shape.1.val → S) (n : ℕ) : ℂ :=
  if BoundedKernelForbiddenPatternForcesEdge J e then
    if n = boundedKernelForbiddenPatternLength J e then
      profilePathEdgeCoefficient M tau
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) n
    else 0
  else
    profilePathEdgeCoefficient M tau
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2) n

private theorem boundedKernelProfileForbiddenPatternEdgeCoefficient_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (tau : C(S, ℂ))
    (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    Summable (boundedKernelProfileForbiddenPatternEdgeCoefficient
      M K J e tau x) := by
  classical
  by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
  · let c : ℕ → ℂ := fun n ↦
      profilePathEdgeCoefficient M tau
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) n
    exact (hasSum_ite_eq (boundedKernelForbiddenPatternLength J e)
      (c (boundedKernelForbiddenPatternLength J e))).summable.congr
        (fun n ↦ by
          by_cases hn : n = boundedKernelForbiddenPatternLength J e
          · subst n
            simp [boundedKernelProfileForbiddenPatternEdgeCoefficient,
              he, c]
          · simp [boundedKernelProfileForbiddenPatternEdgeCoefficient,
              he, hn, c])
  · exact (summable_profilePathEdgeCoefficient M hM tau r hr hr1 htau
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2)).congr
        (fun n ↦ by
          simp [boundedKernelProfileForbiddenPatternEdgeCoefficient, he])

private theorem tsum_boundedKernelProfileForbiddenPatternEdgeCoefficient
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (tau : C(S, ℂ))
    (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    (∑' n : ℕ,
      boundedKernelProfileForbiddenPatternEdgeCoefficient
        M K J e tau x n) =
      boundedKernelProfileForbiddenPatternEdgeFunction M K J e tau x := by
  classical
  by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
  · let c : ℕ → ℂ := fun n ↦
      profilePathEdgeCoefficient M tau
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) n
    calc
      (∑' n : ℕ,
        boundedKernelProfileForbiddenPatternEdgeCoefficient
          M K J e tau x n) =
          c (boundedKernelForbiddenPatternLength J e) := by
        calc
          _ = ∑' n : ℕ,
              if n = boundedKernelForbiddenPatternLength J e then
                c (boundedKernelForbiddenPatternLength J e) else 0 := by
            apply tsum_congr
            intro n
            by_cases hn : n = boundedKernelForbiddenPatternLength J e
            · subst n
              simp [boundedKernelProfileForbiddenPatternEdgeCoefficient,
                he, c]
            · simp [boundedKernelProfileForbiddenPatternEdgeCoefficient,
                he, hn, c]
          _ = c (boundedKernelForbiddenPatternLength J e) :=
            (hasSum_ite_eq (boundedKernelForbiddenPatternLength J e)
              (c (boundedKernelForbiddenPatternLength J e))).tsum_eq
      _ = boundedKernelProfileForbiddenPatternEdgeFunction
          M K J e tau x := by
        simp [boundedKernelProfileForbiddenPatternEdgeFunction,
          boundedKernelProfileFixedLengthEdgeFunction_apply, he, c]
  · rw [show (∑' n : ℕ,
        boundedKernelProfileForbiddenPatternEdgeCoefficient
          M K J e tau x n) =
        ∑' n : ℕ, profilePathEdgeCoefficient M tau
          (x (boundedKernelOrderedEndpoints K.shape e).1)
          (x (boundedKernelOrderedEndpoints K.shape e).2) n by
      apply tsum_congr
      intro n
      simp [boundedKernelProfileForbiddenPatternEdgeCoefficient, he]]
    rw [tsum_profilePathEdgeCoefficient_eq_profilePathResolventKernel
      M hM tau r hr hr1 htau]
    simp [boundedKernelProfileForbiddenPatternEdgeFunction, he]

private def boundedKernelProfileForbiddenPatternAssignmentWeight
    (M : CompactBJRModel S) {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S)
    (l : Fin K.shape.2.1.val → ℕ) : ℂ :=
  if BoundedKernelForbiddenPatternCompatible J then
    ∏ e : Fin K.shape.2.1.val,
      boundedKernelProfileForbiddenPatternEdgeCoefficient
        M K J e tau x (l e)
  else 0

private theorem boundedKernelProfileForbiddenPatternAssignmentWeight_eq_indicator
    (M : CompactBJRModel S) {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S)
    (l : Fin K.shape.2.1.val → ℕ) :
    boundedKernelProfileForbiddenPatternAssignmentWeight M K J tau x l =
      if ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin K.shape.2.1.val,
          profilePathEdgeCoefficient M tau
            (x (boundedKernelOrderedEndpoints K.shape e).1)
            (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
      else 0 := by
  classical
  by_cases hall :
      ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l)
  · obtain ⟨hcompat, hlength⟩ :=
      (boundedKernelForbiddenPattern_all_occurs_iff J l).mp hall
    rw [if_pos hall]
    unfold boundedKernelProfileForbiddenPatternAssignmentWeight
    rw [if_pos hcompat]
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
    · simp [boundedKernelProfileForbiddenPatternEdgeCoefficient, he,
        hlength e he]
    · simp [boundedKernelProfileForbiddenPatternEdgeCoefficient, he]
  · rw [if_neg hall]
    unfold boundedKernelProfileForbiddenPatternAssignmentWeight
    by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
    · rw [if_pos hcompat]
      have hnot : ¬ ∀ e, BoundedKernelForbiddenPatternForcesEdge J e →
          l e = boundedKernelForbiddenPatternLength J e := by
        intro hlength
        exact hall ((boundedKernelForbiddenPattern_all_occurs_iff J l).mpr
          ⟨hcompat, hlength⟩)
      push Not at hnot
      obtain ⟨e, he, hne⟩ := hnot
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [boundedKernelProfileForbiddenPatternEdgeCoefficient, he, hne]
    · simp [hcompat]

private theorem boundedKernelProfileForbiddenPatternAssignmentWeight_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    Summable (boundedKernelProfileForbiddenPatternAssignmentWeight
      M K J tau x) := by
  classical
  by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
  · exact (summable_finFunction_prod_and_tsum
        (fun e n ↦ boundedKernelProfileForbiddenPatternEdgeCoefficient
          M K J e tau x n)
        (fun e ↦
          boundedKernelProfileForbiddenPatternEdgeCoefficient_summable
            M hM K J e tau x r hr hr1 htau)).1.congr
      (fun l ↦ by
        simp [boundedKernelProfileForbiddenPatternAssignmentWeight, hcompat])
  · exact summable_zero.congr
      (fun l ↦ by
        simp [boundedKernelProfileForbiddenPatternAssignmentWeight, hcompat])

private theorem tsum_boundedKernelProfileForbiddenPatternAssignmentWeight
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r)
    (hcompat : BoundedKernelForbiddenPatternCompatible J) :
    (∑' l : Fin K.shape.2.1.val → ℕ,
      boundedKernelProfileForbiddenPatternAssignmentWeight
        M K J tau x l) =
      ∏ e : Fin K.shape.2.1.val,
        boundedKernelProfileForbiddenPatternEdgeFunction M K J e tau x := by
  classical
  simp only [boundedKernelProfileForbiddenPatternAssignmentWeight,
    hcompat, if_true]
  rw [(summable_finFunction_prod_and_tsum
    (fun e n ↦ boundedKernelProfileForbiddenPatternEdgeCoefficient
      M K J e tau x n)
    (fun e ↦ boundedKernelProfileForbiddenPatternEdgeCoefficient_summable
      M hM K J e tau x r hr hr1 htau)).2]
  apply Finset.prod_congr rfl
  intro e _
  exact tsum_boundedKernelProfileForbiddenPatternEdgeCoefficient
    M hM K J e tau x r hr hr1 htau

private theorem boundedKernelProfileForbiddenCorrection_eq_literal
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    boundedKernelProfileForbiddenCorrectionFunction M K tau x =
      boundedKernelLiteralForbiddenProfileIntegrand M K tau x := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  classical
  let P := (Finset.univ :
    Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
      Finset.Nonempty
  let B : (Fin K.shape.2.1.val → ℕ) → ℂ := fun l ↦
    ∏ e : Fin K.shape.2.1.val,
      profilePathEdgeCoefficient M tau
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
  have hJsum (J : Finset (BoundedKernelForbiddenLengthWitness K)) :
      boundedKernelProfileForbiddenIntersectionFunction M K J tau x =
        (∏ v : Fin K.shape.1.val, tau (x v)) *
          ∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelProfileForbiddenPatternAssignmentWeight
              M K J tau x l := by
    unfold boundedKernelProfileForbiddenIntersectionFunction
    by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
    · rw [if_pos hcompat, ContinuousMap.mul_apply,
          ContinuousMap.prod_apply,
          boundedKernelProfileBranchFunction_apply,
          tsum_boundedKernelProfileForbiddenPatternAssignmentWeight
            M hM K J tau x r hr hr1 htau hcompat]
    · rw [if_neg hcompat]
      have hzero :
          (∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelProfileForbiddenPatternAssignmentWeight
              M K J tau x l) = 0 := by
        simp [boundedKernelProfileForbiddenPatternAssignmentWeight, hcompat]
      simp [hzero]
  have hsumJ (J : Finset (BoundedKernelForbiddenLengthWitness K)) :
      Summable (fun l : Fin K.shape.2.1.val → ℕ ↦
        (-1 : ℂ) ^ (J.card + 1) *
          boundedKernelProfileForbiddenPatternAssignmentWeight
            M K J tau x l) :=
    (boundedKernelProfileForbiddenPatternAssignmentWeight_summable
      M hM K J tau x r hr hr1 htau).mul_left _
  unfold boundedKernelProfileForbiddenCorrectionFunction
    boundedKernelLiteralForbiddenProfileIntegrand
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [hJsum]
  rw [show (∑ J ∈ P, (-1 : ℂ) ^ (J.card + 1) *
        ((∏ v : Fin K.shape.1.val, tau (x v)) *
          ∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelProfileForbiddenPatternAssignmentWeight
              M K J tau x l)) =
      (∏ v : Fin K.shape.1.val, tau (x v)) *
        ∑ J ∈ P, (-1 : ℂ) ^ (J.card + 1) *
          ∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelProfileForbiddenPatternAssignmentWeight
              M K J tau x l by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J _
      ring]
  apply congrArg (fun z : ℂ ↦
    (∏ v : Fin K.shape.1.val, tau (x v)) * z)
  have hscale (J : Finset (BoundedKernelForbiddenLengthWitness K)) :
      (-1 : ℂ) ^ (J.card + 1) *
          ∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelProfileForbiddenPatternAssignmentWeight
              M K J tau x l =
        ∑' l : Fin K.shape.2.1.val → ℕ,
          (-1 : ℂ) ^ (J.card + 1) *
            boundedKernelProfileForbiddenPatternAssignmentWeight
              M K J tau x l :=
    ((boundedKernelProfileForbiddenPatternAssignmentWeight_summable
      M hM K J tau x r hr hr1 htau).tsum_mul_left _).symm
  have hswap := Summable.tsum_finsetSum
    (s := P)
    (f := fun J l ↦ (-1 : ℂ) ^ (J.card + 1) *
      boundedKernelProfileForbiddenPatternAssignmentWeight
        M K J tau x l)
    (fun J _ ↦ hsumJ J)
  simp_rw [hscale]
  rw [← hswap]
  apply tsum_congr
  intro l
  simp_rw [boundedKernelProfileForbiddenPatternAssignmentWeight_eq_indicator]
  convert boundedKernelForbidden_inclusionExclusion_assignment K l (B l) using 1 <;>
    simp only [P, B]
  · apply Finset.sum_congr rfl
    intro J _hJ
    by_cases hocc : ∀ w ∈ J,
        w.Occurs (Finsupp.equivFunOnFinite.symm l) <;> simp_all
  · by_cases hex : ∃ w : BoundedKernelForbiddenLengthWitness K,
        w.Occurs (Finsupp.equivFunOnFinite.symm l) <;> simp_all

/-- On every closed strict-profile ball, the resolvent-minus-correction
integrand is exactly the literal admissible assignment series. -/
theorem boundedKernelAdmissibleProfileIntegrandFunction_eq_literal
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    boundedKernelAdmissibleProfileIntegrandFunction M K tau x =
      boundedKernelLiteralAdmissibleProfileIntegrand M K tau x := by
  have hsplit := boundedKernelLiteralAdmissible_add_forbidden_profile
    M hM K tau x r hr hr1 htau
  rw [← boundedKernelProfileUnrestrictedFunction_eq_literal
      M hM K tau x r hr hr1 htau,
    ← boundedKernelProfileForbiddenCorrection_eq_literal
      M hM K tau x r hr hr1 htau] at hsplit
  unfold boundedKernelAdmissibleProfileIntegrandFunction
  simp only [ContinuousMap.sub_apply]
  exact (eq_sub_of_add_eq hsplit).symm

/-- Continuous-function form of one literal admissible length assignment.
It is exposed for the Taylor reindexing layer; inadmissible assignments are
identically zero. -/
def boundedKernelAdmissibleProfileAssignmentFunction
    (M : CompactBJRModel S) {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (l : Fin K.shape.2.1.val → ℕ) :
    C((Fin K.shape.1.val → S), ℂ) :=
  if BoundedKernelLengthAssignment.IsAdmissible K
      (Finsupp.equivFunOnFinite.symm l) then
    boundedKernelProfileBranchFunction K tau *
      ∏ e : Fin K.shape.2.1.val,
        boundedKernelProfileFixedLengthEdgeFunction M K e (l e) tau
  else 0

@[simp] theorem boundedKernelAdmissibleProfileAssignmentFunction_apply
    (M : CompactBJRModel S) {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (l : Fin K.shape.2.1.val → ℕ)
    (x : Fin K.shape.1.val → S) :
    boundedKernelAdmissibleProfileAssignmentFunction M K tau l x =
      if BoundedKernelLengthAssignment.IsAdmissible K
          (Finsupp.equivFunOnFinite.symm l) then
        (∏ v : Fin K.shape.1.val, tau (x v)) *
          ∏ e : Fin K.shape.2.1.val,
            profilePathEdgeCoefficient M tau
              (x (boundedKernelOrderedEndpoints K.shape e).1)
              (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
      else 0 := by
  classical
  by_cases hl : BoundedKernelLengthAssignment.IsAdmissible K
      (Finsupp.equivFunOnFinite.symm l)
  · simp [boundedKernelAdmissibleProfileAssignmentFunction, hl,
      boundedKernelProfileFixedLengthEdgeFunction_apply,
      boundedKernelProfileBranchFunction_apply,
      ContinuousMap.prod_apply]
  · simp [boundedKernelAdmissibleProfileAssignmentFunction, hl]

private theorem boundedKernelProfileFixedLengthEdgeFunction_norm_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    Summable (fun n : ℕ ↦
      ‖boundedKernelProfileFixedLengthEdgeFunction M K e n tau‖) := by
  obtain ⟨m, hm, hmu⟩ := M.perronFunction_uniform_pos hM
  let C₀ : ℝ := max 1
    (‖M.kernel.complexActionCLM M.mu‖ *
      (‖M.perronFunction hM‖ / m))
  have hKC : ‖M.kernel.complexActionCLM M.mu‖ *
      (‖M.perronFunction hM‖ / m) ≤ C₀ := by
    dsimp only [C₀]
    exact le_max_right (1 : ℝ) _
  have hpow (n : ℕ) :
      ‖(PerronWright.MarkedPathResolvent.pathOperatorParameterCLM M tau) ^ n‖ ≤
        C₀ * r ^ n := by
    cases n with
    | zero =>
        simp only [pow_zero, mul_one]
        exact ContinuousLinearMap.norm_id_le.trans (by
          dsimp only [C₀]
          exact le_max_left (1 : ℝ) _)
    | succ n =>
        have hp := PerronWright.JointSimpleCycleEGF.pathOperator_pow_succ_norm_le
          M hM tau r m hr htau hm hmu n
        exact hp.trans
          (mul_le_mul_of_nonneg_right hKC (pow_nonneg hr _))
  let C : ℝ :=
    ‖noncubicProfileEdgePullbackCLM (S := S) K e‖ *
      ‖PerronWright.MarkedPathResolvent.operatorKernelize M‖ * C₀
  have hmajor : Summable (fun n : ℕ ↦ C * r ^ n) :=
    (summable_geometric_of_lt_one hr hr1).mul_left C
  apply Summable.of_norm_bounded hmajor
  intro n
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  unfold boundedKernelProfileFixedLengthEdgeFunction
    boundedKernelProfileFixedLengthPathKernel
  calc
    ‖noncubicProfileEdgePullbackCLM (S := S) K e
        (PerronWright.MarkedPathResolvent.operatorKernelize M
          ((PerronWright.MarkedPathResolvent.pathOperatorParameterCLM M tau) ^ n))‖ ≤
      ‖noncubicProfileEdgePullbackCLM (S := S) K e‖ *
        ‖PerronWright.MarkedPathResolvent.operatorKernelize M
          ((PerronWright.MarkedPathResolvent.pathOperatorParameterCLM M tau) ^ n)‖ :=
      (noncubicProfileEdgePullbackCLM (S := S) K e).le_opNorm _
    _ ≤ ‖noncubicProfileEdgePullbackCLM (S := S) K e‖ *
        (‖PerronWright.MarkedPathResolvent.operatorKernelize M‖ *
          ‖(PerronWright.MarkedPathResolvent.pathOperatorParameterCLM M tau) ^ n‖) := by
      gcongr
      exact (PerronWright.MarkedPathResolvent.operatorKernelize M).le_opNorm _
    _ ≤ ‖noncubicProfileEdgePullbackCLM (S := S) K e‖ *
        (‖PerronWright.MarkedPathResolvent.operatorKernelize M‖ *
          (C₀ * r ^ n)) := by
      gcongr
      exact hpow n
    _ = C * r ^ n := by
      dsimp only [C]
      ring

theorem boundedKernelAdmissibleProfileAssignmentFunction_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    Summable (boundedKernelAdmissibleProfileAssignmentFunction M K tau) := by
  classical
  let A : Set (Fin K.shape.2.1.val → ℕ) := {l |
    BoundedKernelLengthAssignment.IsAdmissible K
      (Finsupp.equivFunOnFinite.symm l)}
  let P : (Fin K.shape.2.1.val → ℕ) →
      C((Fin K.shape.1.val → S), ℂ) := fun l ↦
    ∏ e : Fin K.shape.2.1.val,
      boundedKernelProfileFixedLengthEdgeFunction M K e (l e) tau
  have hP : Summable P :=
    (summable_norm_finFunction_prod_and_tsum
      (fun e n ↦ boundedKernelProfileFixedLengthEdgeFunction M K e n tau)
      (fun e ↦ boundedKernelProfileFixedLengthEdgeFunction_norm_summable
        M hM K e tau r hr hr1 htau)).1.of_norm
  have hA : Summable (A.indicator P) := hP.indicator A
  have hmul := hA.mul_left (boundedKernelProfileBranchFunction K tau)
  exact hmul.congr (fun l ↦ by
    by_cases hl : BoundedKernelLengthAssignment.IsAdmissible K
        (Finsupp.equivFunOnFinite.symm l)
    · simp [boundedKernelAdmissibleProfileAssignmentFunction, A, P, hl]
    · simp [boundedKernelAdmissibleProfileAssignmentFunction, A, P, hl])

/-- The continuous-function `tsum` of literal admissible assignments is
the pointwise literal admissible integrand. -/
theorem tsum_boundedKernelAdmissibleProfileAssignmentFunction_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    (∑' l : Fin K.shape.2.1.val → ℕ,
      boundedKernelAdmissibleProfileAssignmentFunction M K tau l) x =
      boundedKernelLiteralAdmissibleProfileIntegrand M K tau x := by
  have hs := boundedKernelAdmissibleProfileAssignmentFunction_summable
    M hM K tau r hr hr1 htau
  rw [← ContinuousMap.tsum_apply hs]
  unfold boundedKernelLiteralAdmissibleProfileIntegrand
  rw [← tsum_mul_left]
  apply tsum_congr
  intro l
  simp only [boundedKernelAdmissibleProfileAssignmentFunction_apply]
  by_cases hl : BoundedKernelLengthAssignment.IsAdmissible K
      (Finsupp.equivFunOnFinite.symm l) <;> simp [hl]

/-! ## Integrated and finitely weighted away-chart functional -/

/-- Integrated admissible strict-profile amplitude of one fixed connected
noncubic bounded kernel. -/
def connectedNoncubicKernelAdmissibleProfileFunctional
    (M : CompactBJRModel S) {ell : ℕ}
    (K : LabelledConnectedNoncubicKernel ell)
    (tau : C(S, ℂ)) : ℂ :=
  boundedKernelBranchIntegralCLM M K.1.toLabelledBoundedKernel
    (boundedKernelAdmissibleProfileIntegrandFunction M
      K.1.toLabelledBoundedKernel tau)

theorem
    connectedNoncubicKernelAdmissibleProfileFunctional_analyticAt_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ
      (connectedNoncubicKernelAdmissibleProfileFunctional M K) tau :=
  (boundedKernelBranchIntegralCLM M
      K.1.toLabelledBoundedKernel).analyticAt _ |>.comp
    (boundedKernelAdmissibleProfileIntegrandFunction_analyticAt_of_norm_lt_one
      M hM K.1.toLabelledBoundedKernel htau)

/-- Finite weighted noncubic admissible profile functional.  The weights
are the reciprocal coordinate multiplicities already used by the local
integrated amplitude. -/
def positiveSurplusNoncubicAdmissibleProfileFunctional
    (M : CompactBJRModel S) (ell : ℕ) (tau : C(S, ℂ)) : ℂ :=
  letI := labelledConnectedNoncubicKernelFintype ell
  ∑ K : LabelledConnectedNoncubicKernel ell,
    labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K *
      connectedNoncubicKernelAdmissibleProfileFunctional M K tau

theorem
    positiveSurplusNoncubicAdmissibleProfileFunctional_analyticAt_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (ell : ℕ)
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ
      (positiveSurplusNoncubicAdmissibleProfileFunctional M ell) tau := by
  let _ := labelledConnectedNoncubicKernelFintype ell
  unfold positiveSurplusNoncubicAdmissibleProfileFunctional
  let F : LabelledConnectedNoncubicKernel ell → (C(S, ℂ) → ℂ) :=
    fun K sigma ↦
      labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K *
        connectedNoncubicKernelAdmissibleProfileFunctional M K sigma
  change AnalyticAt ℂ (fun sigma : C(S, ℂ) ↦ ∑ K, F K sigma) tau
  have hsum : AnalyticAt ℂ (∑ K, F K) tau := by
    apply Finset.analyticAt_sum Finset.univ
    intro K _
    exact analyticAt_const.mul
      (connectedNoncubicKernelAdmissibleProfileFunctional_analyticAt_of_norm_lt_one
        M hM K htau)
  have hfun : (∑ K, F K) =
      (fun sigma : C(S, ℂ) ↦ ∑ K, F K sigma) := by
    funext sigma
    exact Fintype.sum_apply sigma F
  rw [← hfun]
  exact hsum

theorem
    positiveSurplusNoncubicAdmissibleProfileFunctional_analyticOnNhd_unitBall
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (ell : ℕ) :
    AnalyticOnNhd ℂ
      (positiveSurplusNoncubicAdmissibleProfileFunctional M ell)
      (Metric.ball (0 : C(S, ℂ)) 1) := by
  intro tau htau
  apply
    positiveSurplusNoncubicAdmissibleProfileFunctional_analyticAt_of_norm_lt_one
      M hM ell
  simpa only [Metric.mem_ball, dist_zero_right] using htau

/-! ## Exact specialization to the local fold chart -/

private theorem boundedKernelProfileResolventEdgeFunction_foldProfile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S) :
    boundedKernelProfileResolventEdgeFunction M K e
        (NBKAS_MPR.profile M hM q) x =
      NBKAS_MPR.pathResolventKernel M hM q
        (x (boundedKernelOrderedEndpoints K.shape e).1,
          x (boundedKernelOrderedEndpoints K.shape e).2) := by
  simp only [boundedKernelProfileResolventEdgeFunction_apply,
    profilePathResolventKernel,
    PerronWright.MarkedPathResolvent.pathResolventKernel,
    PerronWright.MarkedPathResolvent.pathOperator]

private theorem boundedKernelProfileForbiddenPatternEdgeFunction_foldProfile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S) :
    boundedKernelProfileForbiddenPatternEdgeFunction M K J e
        (NBKAS_MPR.profile M hM q) x =
      boundedKernelForbiddenRawPatternEdgeFactor M hM K J e q x := by
  classical
  by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
  · simp [boundedKernelProfileForbiddenPatternEdgeFunction,
      boundedKernelForbiddenRawPatternEdgeFactor, he,
      boundedKernelFixedLengthEdgeFactor_eq_profileCoefficient]
  · simp only [boundedKernelProfileForbiddenPatternEdgeFunction,
      boundedKernelForbiddenRawPatternEdgeFactor, if_neg he]
    exact boundedKernelProfileResolventEdgeFunction_foldProfile M hM K e q x

private theorem boundedKernelProfileForbiddenIntersectionFunction_foldProfile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    boundedKernelProfileForbiddenIntersectionFunction M K J
        (NBKAS_MPR.profile M hM q) x =
      boundedKernelForbiddenRawIntersection M hM K J q x := by
  classical
  by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
  · simp [boundedKernelProfileForbiddenIntersectionFunction,
      boundedKernelForbiddenRawIntersection, hcompat,
      boundedKernelProfileBranchFunction_apply,
      boundedKernelBranchProfileProduct,
      boundedKernelProfileForbiddenPatternEdgeFunction_foldProfile]
  · simp [boundedKernelProfileForbiddenIntersectionFunction,
      boundedKernelForbiddenRawIntersection, hcompat]

@[simp] theorem boundedKernelProfileForbiddenCorrectionFunction_foldProfile_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    boundedKernelProfileForbiddenCorrectionFunction M K
        (NBKAS_MPR.profile M hM q) x =
      boundedKernelRawForbiddenCorrection M hM K q x := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  unfold boundedKernelProfileForbiddenCorrectionFunction
    boundedKernelRawForbiddenCorrection
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    boundedKernelProfileForbiddenIntersectionFunction_foldProfile]

@[simp] theorem boundedKernelProfileUnrestrictedFunction_foldProfile_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    boundedKernelProfileUnrestrictedFunction M K
        (NBKAS_MPR.profile M hM q) x =
      boundedKernelCoreResolventIntegrand M hM K.shape x q := by
  unfold boundedKernelProfileUnrestrictedFunction
    boundedKernelCoreResolventIntegrand
  rw [ContinuousMap.mul_apply, boundedKernelProfileBranchFunction_apply]
  unfold boundedKernelBranchProfileProduct
  congr 1
  rw [ContinuousMap.prod_apply]
  apply Finset.prod_congr rfl
  intro e _he
  exact boundedKernelProfileResolventEdgeFunction_foldProfile M hM K e q x

@[simp] theorem
    boundedKernelAdmissibleProfileIntegrandFunction_foldProfile_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    boundedKernelAdmissibleProfileIntegrandFunction M K
        (NBKAS_MPR.profile M hM q) x =
      boundedKernelCoreResolventIntegrand M hM K.shape x q -
        boundedKernelRawForbiddenCorrection M hM K q x := by
  simp [boundedKernelAdmissibleProfileIntegrandFunction]

private theorem boundedKernelNormalizedPatternEdge_eq_X_mul_profile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S)
    (hpath : boundedNormalizedPathKernel M hM q =
      q.2 • NBKAS_MPR.pathResolventKernel M hM q) :
    boundedKernelForbiddenNormalizedPatternEdgeFactor M hM K J e q x =
      q.2 * boundedKernelProfileForbiddenPatternEdgeFunction M K J e
        (NBKAS_MPR.profile M hM q) x := by
  classical
  by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
  · simp [boundedKernelForbiddenNormalizedPatternEdgeFactor,
      boundedKernelProfileForbiddenPatternEdgeFunction, he,
      boundedKernelFixedLengthEdgeFactor_eq_profileCoefficient]
  · unfold boundedKernelForbiddenNormalizedPatternEdgeFactor
      boundedKernelProfileForbiddenPatternEdgeFunction
      boundedKernelNormalizedEdgeFactor
    rw [if_neg he, if_neg he]
    have hfun := congrArg
      (fun f : C(S × S, ℂ) ↦
        f (x (boundedKernelOrderedEndpoints K.shape e).1,
          x (boundedKernelOrderedEndpoints K.shape e).2)) hpath
    simpa only [ContinuousMap.smul_apply, smul_eq_mul,
      boundedKernelProfileResolventEdgeFunction_foldProfile] using hfun

private theorem boundedKernelNormalizedIntersection_eq_pow_mul_profile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (hpath : boundedNormalizedPathKernel M hM q =
      q.2 • NBKAS_MPR.pathResolventKernel M hM q) :
    boundedKernelForbiddenNormalizedIntersection M hM K J q x =
      q.2 ^ K.shape.2.1.val *
        boundedKernelProfileForbiddenIntersectionFunction M K J
          (NBKAS_MPR.profile M hM q) x := by
  classical
  by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
  · unfold boundedKernelForbiddenNormalizedIntersection
      boundedKernelProfileForbiddenIntersectionFunction
    rw [if_pos hcompat, if_pos hcompat]
    simp_rw [boundedKernelNormalizedPatternEdge_eq_X_mul_profile
      M hM K J _ q x hpath]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp [boundedKernelProfileBranchFunction_apply,
      boundedKernelBranchProfileProduct]
    ring
  · simp [boundedKernelForbiddenNormalizedIntersection,
      boundedKernelProfileForbiddenIntersectionFunction, hcompat]

private theorem boundedKernelNormalizedCorrection_eq_pow_mul_profile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (hpath : boundedNormalizedPathKernel M hM q =
      q.2 • NBKAS_MPR.pathResolventKernel M hM q) :
    boundedKernelNormalizedForbiddenCorrection M hM K q x =
      q.2 ^ K.shape.2.1.val *
        boundedKernelProfileForbiddenCorrectionFunction M K
          (NBKAS_MPR.profile M hM q) x := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  unfold boundedKernelNormalizedForbiddenCorrection
    boundedKernelProfileForbiddenCorrectionFunction
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [boundedKernelNormalizedIntersection_eq_pow_mul_profile
    M hM K J q x hpath]
  ring

private theorem boundedKernelNormalizedCore_eq_pow_mul_profile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (hpath : boundedNormalizedPathKernel M hM q =
      q.2 • NBKAS_MPR.pathResolventKernel M hM q) :
    boundedKernelNormalizedCoreIntegrand M hM K.shape x q =
      q.2 ^ K.shape.2.1.val *
        boundedKernelProfileUnrestrictedFunction M K
          (NBKAS_MPR.profile M hM q) x := by
  unfold boundedKernelNormalizedCoreIntegrand
    boundedKernelNormalizedPathAmplitude
    boundedKernelProfileUnrestrictedFunction
  have hedge (e : Fin K.shape.2.1.val) :
      boundedKernelNormalizedEdgeFactor M hM K.shape x e q =
        q.2 * boundedKernelProfileResolventEdgeFunction M K e
          (NBKAS_MPR.profile M hM q) x := by
    unfold boundedKernelNormalizedEdgeFactor
    have hfun := congrArg
      (fun f : C(S × S, ℂ) ↦
        f (x (boundedKernelOrderedEndpoints K.shape e).1,
          x (boundedKernelOrderedEndpoints K.shape e).2)) hpath
    simpa only [ContinuousMap.smul_apply, smul_eq_mul,
      boundedKernelProfileResolventEdgeFunction_foldProfile] using hfun
  simp_rw [hedge]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ContinuousMap.mul_apply, ContinuousMap.prod_apply]
  simp [boundedKernelProfileBranchFunction_apply,
    boundedKernelBranchProfileProduct]
  ring

private theorem boundedKernelAdmissibleNormalizedFunction_eq_pow_smul_profile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ)
    (hpath : boundedNormalizedPathKernel M hM q =
      q.2 • NBKAS_MPR.pathResolventKernel M hM q) :
    boundedKernelAdmissibleNormalizedIntegrandFunction M hM K q =
      q.2 ^ K.shape.2.1.val •
        boundedKernelAdmissibleProfileIntegrandFunction M K
          (NBKAS_MPR.profile M hM q) := by
  ext x
  simp only [boundedKernelAdmissibleNormalizedIntegrandFunction_apply,
    boundedKernelAdmissibleNormalizedCoreIntegrand,
    ContinuousMap.smul_apply, smul_eq_mul,
    boundedKernelAdmissibleProfileIntegrandFunction_foldProfile_apply]
  rw [boundedKernelNormalizedCore_eq_pow_mul_profile
      M hM K q x hpath,
    boundedKernelNormalizedCorrection_eq_pow_mul_profile
      M hM K q x hpath]
  rw [boundedKernelProfileUnrestrictedFunction_foldProfile_apply,
    boundedKernelProfileForbiddenCorrectionFunction_foldProfile_apply]
  ring

private theorem connectedNoncubicKernelLocalIntegrand_eq_pow_smul_profile
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (q : C(S, ℂ) × ℂ)
    (hpath : boundedNormalizedPathKernel M hM q =
      q.2 • NBKAS_MPR.pathResolventKernel M hM q) :
    connectedNoncubicKernelCubicNormalizedIntegrandFunction M hM K q =
      q.2 ^ (3 * ell) •
        boundedKernelAdmissibleProfileIntegrandFunction M
          K.1.toLabelledBoundedKernel (NBKAS_MPR.profile M hM q) := by
  let B := K.1.toLabelledBoundedKernel
  have hedge : B.shape.2.1.val < 3 * ell := K.2
  have hsum :
      3 * ell = (3 * ell - B.shape.2.1.val) + B.shape.2.1.val := by
    omega
  unfold connectedNoncubicKernelCubicNormalizedIntegrandFunction
  rw [boundedKernelAdmissibleNormalizedFunction_eq_pow_smul_profile
    M hM B q hpath]
  rw [smul_smul, ← pow_add, ← hsum]

theorem connectedNoncubicKernelIntegratedAmplitude_eq_profileFunctional
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      connectedNoncubicKernelIntegratedAmplitude M hM K q =
        q.2 ^ (3 * ell) *
          connectedNoncubicKernelAdmissibleProfileFunctional M K
            (NBKAS_MPR.profile M hM q) := by
  filter_upwards
    [boundedNormalizedPathKernel_eq_smul_pathResolventKernel M hM]
      with q hpath
  intro hX
  unfold connectedNoncubicKernelIntegratedAmplitude
    connectedNoncubicKernelAdmissibleProfileFunctional
  rw [connectedNoncubicKernelLocalIntegrand_eq_pow_smul_profile
    M hM K q (hpath hX), map_smul]
  simp only [smul_eq_mul]

/-- Exact overlap of the finite weighted away chart with the local
cubic-normalized noncubic amplitude.  The statement uses only proved
kernel identities and retains the complete factor `X^(3*ell)`. -/
theorem positiveSurplusNoncubicIntegratedAmplitude_eq_profileFunctional
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (ell : ℕ) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      positiveSurplusNoncubicIntegratedAmplitude M hM ell q =
        q.2 ^ (3 * ell) *
          positiveSurplusNoncubicAdmissibleProfileFunctional M ell
            (NBKAS_MPR.profile M hM q) := by
  let _ := labelledConnectedNoncubicKernelFintype ell
  have hall :
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        ∀ K : LabelledConnectedNoncubicKernel ell,
          q.2 ≠ 0 →
          connectedNoncubicKernelIntegratedAmplitude M hM K q =
            q.2 ^ (3 * ell) *
              connectedNoncubicKernelAdmissibleProfileFunctional M K
                (NBKAS_MPR.profile M hM q) := by
    rw [Filter.eventually_all]
    intro K
    exact connectedNoncubicKernelIntegratedAmplitude_eq_profileFunctional
      M hM K
  filter_upwards [hall] with q hq
  intro hX
  unfold positiveSurplusNoncubicIntegratedAmplitude
    positiveSurplusNoncubicAdmissibleProfileFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  rw [hq K hX]
  ring

end PerronWright.GraphCore
