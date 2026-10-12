import PerronWright.Enumeration.CubicProfileCoefficientBounds
import PerronWright.Analysis.FiniteIrreduciblePathSeriesBounds
import PerronWright.Analysis.FiniteIrreducibleCubicLiteralResolvent
import PerronWright.Enumeration.CubicForbiddenCorrectionBridge
import Mathlib.Analysis.Analytic.Constructions

/-!
# The analytic strict-subcritical cubic profile functional

At fixed positive surplus, the literal cubic profile contribution is the
sum over all admissible internal-length profiles.  This file keeps that
literal `tsum` as the public definition.  Analyticity is proved by identifying
it, on every strict subcritical profile ball, with a finite
inclusion--exclusion expression made from the generic profile resolvent.

The inclusion--exclusion expression is only a proof device.  Its witness
patterns are the already proved loop and repeated-zero-edge obstructions, so
no additional admissibility or convergence hypothesis is introduced here.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleKernelAmplitude
open GraphCore

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

private abbrev ProfilePathEnd
    (S : Type*) [MetricSpace S] [CompactSpace S] :=
  C(S, ℂ) →L[ℂ] C(S, ℂ)

local instance profilePathEndNormedRing :
    NormedRing (ProfilePathEnd S) := inferInstance
local instance profilePathEndSeminormedRing :
    SeminormedRing (ProfilePathEnd S) := NormedRing.toSeminormedRing
@[reducible] local instance profilePathEndNormedAddCommGroup :
    NormedAddCommGroup (ProfilePathEnd S) :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance profilePathEndNormedAlgebra :
    NormedAlgebra ℂ (ProfilePathEnd S) := inferInstance
@[reducible] local instance profilePathEndNormedSpace :
    NormedSpace ℂ (ProfilePathEnd S) :=
  NormedAlgebra.toNormedSpace (ProfilePathEnd S)
local instance profilePathEndNormTopology :
    TopologicalSpace (ProfilePathEnd S) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The genuine generic finite path resolvent kernel. -/
def profilePathResolventKernel (M : FiniteIrreducibleModel S) (tau : C(S, ℂ)) :
    C(S × S, ℂ) :=
  FiniteIrreducibleMarkedPathResolvent.operatorKernelize M
    (Ring.inverse (1 - FiniteIrreducibleMarkedPathResolvent.pathOperatorParameterCLM M tau))

private theorem summable_profilePathEdgeCoefficientKernel
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖tau x‖ ≤ q) :
    Summable (GraphCore.profilePathEdgeCoefficientKernel M.bjrModel tau) := by
  exact (FiniteIrreduciblePathGeneratingSeries.hasSum_pathCoefficientKernel
    M hM tau q hq hq1 ha).summable

private theorem tsum_profilePathEdgeCoefficient_eq_profilePathResolventKernel
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖tau x‖ ≤ q) (a b : S) :
    (∑' n : ℕ, GraphCore.profilePathEdgeCoefficient M.bjrModel tau a b n) =
      profilePathResolventKernel M tau (a,b) := by
  simpa only [profilePathResolventKernel,
    GraphCore.complexProfilePathWeight_eq_profilePathEdgeCoefficient] using
    (FiniteIrreduciblePathGeneratingSeries.hasSum_literal_pathWeight
      M hM tau q hq hq1 ha a b).tsum_eq

/-! ## Literal profile series -/

/-- The literal positive-surplus cubic profile functional.  The `d`-th
summand is the exact admissible length-profile coefficient, including the
labelled-kernel inverse multiplicity. -/
def positiveSurplusCubicProfileSeries
    (M : FiniteIrreducibleModel S) (ell : ℕ) (tau : C(S, ℂ)) : ℂ :=
  ∑' d : ℕ,
    positiveSurplusCubicAdmissibleProfileCoefficient M.bjrModel tau ell d

/-! ## Generic profile resolvent -/

/-- The generic path-resolvent kernel is analytic at every strictly
subcritical profile.  Summability of the operator Neumann series supplies
the unit at the chosen base point; analyticity of inversion is then local
around that unit. -/
theorem profilePathResolventKernel_analyticAt_of_norm_lt_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ (profilePathResolventKernel M) tau := by
  let L : C(S, ℂ) →L[ℂ] ProfilePathEnd S :=
    PerronWright.FiniteIrreducibleMarkedPathResolvent.pathOperatorParameterCLM M
  let q : ℝ := (‖tau‖ + 1) / 2
  have hq : 0 ≤ q := by
    dsimp only [q]
    positivity
  have htauq : ‖tau‖ ≤ q := by
    dsimp only [q]
    linarith
  have hq1 : q < 1 := by
    dsimp only [q]
    linarith
  have hs : Summable (fun n : ℕ ↦ (L tau) ^ n) := by
    simpa only [L] using
      (PerronWright.FiniteIrreduciblePathGeneratingSeries.profilePathOperator_pow_summable
        M hM tau q hq hq1
          (fun x ↦ (tau.norm_coe_le_norm x).trans htauq))
  let U : (ProfilePathEnd S)ˣ :=
    ⟨1 - L tau, ∑' n : ℕ, (L tau) ^ n,
      hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩
  have hU : (U : ProfilePathEnd S) = 1 - L tau := rfl
  have hden : AnalyticAt ℂ
      (fun sigma : C(S, ℂ) ↦ 1 - L sigma) tau :=
    analyticAt_const.sub (L.analyticAt tau)
  have hinv : AnalyticAt ℂ
      (fun sigma : C(S, ℂ) ↦ Ring.inverse (1 - L sigma)) tau := by
    exact (analyticAt_inverse (𝕜 := ℂ) U).comp_of_eq hden hU.symm
  unfold profilePathResolventKernel
  exact (PerronWright.FiniteIrreducibleMarkedPathResolvent.operatorKernelize M).analyticAt _
    |>.comp_of_eq hinv rfl

/-- The zero-profile resolvent germ is the base-point specialization of the
strict-subcritical statement. -/
theorem profilePathResolventKernel_analyticAt_zero
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    AnalyticAt ℂ (profilePathResolventKernel M) (0 : C(S, ℂ)) :=
  profilePathResolventKernel_analyticAt_of_norm_lt_one M hM (by simp)

private def cubicProfileBranchCoordinateMap {ell : ℕ}
    (v : Fin (2 * ell)) : C((Fin (2 * ell) → S), S) :=
  ⟨fun x ↦ x v, continuous_apply v⟩

private def cubicProfileBranchPullbackCLM {ell : ℕ}
    (v : Fin (2 * ell)) :
    C(S, ℂ) →L[ℂ] C((Fin (2 * ell) → S), ℂ) :=
  ContinuousMap.compCLM ℂ ℂ (cubicProfileBranchCoordinateMap v)

private def cubicProfileBranchFunction (ell : ℕ)
    (tau : C(S, ℂ)) : C((Fin (2 * ell) → S), ℂ) :=
  ∏ v : Fin (2 * ell), cubicProfileBranchPullbackCLM v tau

omit [DecidableEq S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
private theorem cubicProfileBranchFunction_analytic (ell : ℕ)
    (tau : C(S, ℂ)) :
    AnalyticAt ℂ (cubicProfileBranchFunction (S := S) ell)
      tau := by
  unfold cubicProfileBranchFunction
  exact (Finset.univ : Finset (Fin (2 * ell))).analyticAt_fun_prod
    (fun v _ ↦ (cubicProfileBranchPullbackCLM v).analyticAt tau)

omit [Fintype S] [DecidableEq S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
@[simp] private theorem cubicProfileBranchFunction_apply (ell : ℕ)
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S) :
    cubicProfileBranchFunction ell tau x =
      ∏ v : Fin (2 * ell), tau (x v) := by
  simp [cubicProfileBranchFunction, cubicProfileBranchPullbackCLM,
    cubicProfileBranchCoordinateMap]

private def cubicProfileFixedLengthPathKernel
    (M : FiniteIrreducibleModel S) (n : ℕ) (tau : C(S, ℂ)) :
    C(S × S, ℂ) :=
  PerronWright.FiniteIrreducibleMarkedPathResolvent.operatorKernelize M
    ((PerronWright.FiniteIrreducibleMarkedPathResolvent.pathOperatorParameterCLM M tau) ^ n)

private theorem cubicProfileFixedLengthPathKernel_analytic
    (M : FiniteIrreducibleModel S) (n : ℕ) (tau : C(S, ℂ)) :
    AnalyticAt ℂ (cubicProfileFixedLengthPathKernel M n)
      tau := by
  unfold cubicProfileFixedLengthPathKernel
  have hpow : AnalyticAt ℂ
      (fun sigma : C(S, ℂ) ↦
        (PerronWright.FiniteIrreducibleMarkedPathResolvent.pathOperatorParameterCLM M sigma) ^ n)
      tau :=
    ((PerronWright.FiniteIrreducibleMarkedPathResolvent.pathOperatorParameterCLM M).analyticAt
      tau).pow n
  exact (PerronWright.FiniteIrreducibleMarkedPathResolvent.operatorKernelize M).analyticAt _
    |>.comp_of_eq hpow rfl

@[simp] private theorem cubicProfileFixedLengthPathKernel_apply
    (M : FiniteIrreducibleModel S) (n : ℕ) (tau : C(S, ℂ)) (a b : S) :
    cubicProfileFixedLengthPathKernel M n tau (a, b) =
      profilePathEdgeCoefficient M.bjrModel tau a b n := by
  rfl

private def cubicProfileEdgeCoordinateMap {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (e : Fin (3 * ell)) :
    C((Fin (2 * ell) → S), S × S) :=
  ⟨fun x ↦
      (x (cubicKernelOrderedEndpoints K.graph e).1,
        x (cubicKernelOrderedEndpoints K.graph e).2),
    (continuous_apply (cubicKernelOrderedEndpoints K.graph e).1).prodMk
      (continuous_apply (cubicKernelOrderedEndpoints K.graph e).2)⟩

private def cubicProfileEdgePullbackCLM {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (e : Fin (3 * ell)) :
    C(S × S, ℂ) →L[ℂ] C((Fin (2 * ell) → S), ℂ) :=
  ContinuousMap.compCLM ℂ ℂ (cubicProfileEdgeCoordinateMap K e)

private def cubicProfileFixedLengthEdgeFunction
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (e : Fin (3 * ell))
    (n : ℕ) (tau : C(S, ℂ)) : C((Fin (2 * ell) → S), ℂ) :=
  cubicProfileEdgePullbackCLM K e
    (cubicProfileFixedLengthPathKernel M n tau)

private theorem cubicProfileFixedLengthEdgeFunction_analytic
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (e : Fin (3 * ell)) (n : ℕ)
    (tau : C(S, ℂ)) :
    AnalyticAt ℂ (cubicProfileFixedLengthEdgeFunction M K e n)
      tau := by
  unfold cubicProfileFixedLengthEdgeFunction
  exact (cubicProfileEdgePullbackCLM K e).analyticAt _ |>.comp_of_eq
    (cubicProfileFixedLengthPathKernel_analytic M n tau) rfl

@[simp] private theorem cubicProfileFixedLengthEdgeFunction_apply
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (e : Fin (3 * ell))
    (n : ℕ) (tau : C(S, ℂ)) (x : Fin (2 * ell) → S) :
    cubicProfileFixedLengthEdgeFunction M K e n tau x =
      profilePathEdgeCoefficient M.bjrModel tau
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) n := by
  rfl

private theorem cubicProfileFixedLengthEdgeFunction_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    Summable (fun n : ℕ ↦ cubicProfileFixedLengthEdgeFunction M K e n tau) := by
  have hs := summable_profilePathEdgeCoefficientKernel M hM tau r hr hr1
    (fun x ↦ (tau.norm_coe_le_norm x).trans htau)
  change Summable (fun n : ℕ ↦ cubicProfileEdgePullbackCLM K e
    (profilePathEdgeCoefficientKernel M.bjrModel tau n))
  refine (hs.map (cubicProfileEdgePullbackCLM K e)
    (cubicProfileEdgePullbackCLM K e).continuous).congr ?_
  intro n
  rfl

private theorem cubicProfileFixedLengthEdgeFunction_norm_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    Summable (fun n : ℕ ↦
      ‖cubicProfileFixedLengthEdgeFunction M K e n tau‖) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_profilePathEdgeCoefficient_geometric_bound M hM
  have htau' : ∀ x, ‖tau x‖ ≤ r := fun x ↦
    (tau.norm_coe_le_norm x).trans htau
  have hgeom : Summable (fun n : ℕ ↦ B * r ^ n) :=
    (summable_geometric_of_lt_one hr hr1).mul_left B
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hgeom
  intro n
  apply (ContinuousMap.norm_le _
    (mul_nonneg hB (pow_nonneg hr n))).2
  intro x
  simpa only [cubicProfileFixedLengthEdgeFunction_apply] using
    hbound tau r hr htau'
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2) n

private def cubicProfileResolventEdgeFunction
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (e : Fin (3 * ell))
    (tau : C(S, ℂ)) : C((Fin (2 * ell) → S), ℂ) :=
  cubicProfileEdgePullbackCLM K e (profilePathResolventKernel M tau)

private theorem cubicProfileResolventEdgeFunction_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (e : Fin (3 * ell))
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ (cubicProfileResolventEdgeFunction M K e)
      tau := by
  unfold cubicProfileResolventEdgeFunction
  exact (cubicProfileEdgePullbackCLM K e).analyticAt _ |>.comp_of_eq
    (profilePathResolventKernel_analyticAt_of_norm_lt_one M hM htau) rfl

@[simp] private theorem cubicProfileResolventEdgeFunction_apply
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (e : Fin (3 * ell))
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S) :
    cubicProfileResolventEdgeFunction M K e tau x =
      profilePathResolventKernel M tau
        (x (cubicKernelOrderedEndpoints K.graph e).1,
          x (cubicKernelOrderedEndpoints K.graph e).2) := by
  rfl

/-! ## Finite inclusion--exclusion expression -/

private def cubicProfilePatternEdgeFunction
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) (tau : C(S, ℂ)) :
    C((Fin (2 * ell) → S), ℂ) :=
  if CubicForbiddenPatternForcesEdge J e then
    cubicProfileFixedLengthEdgeFunction M K e
      (cubicForbiddenPatternLength J e) tau
  else
    cubicProfileResolventEdgeFunction M K e tau

private theorem cubicProfilePatternEdgeFunction_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ (cubicProfilePatternEdgeFunction M K J e)
      tau := by
  classical
  unfold cubicProfilePatternEdgeFunction
  split_ifs
  · exact cubicProfileFixedLengthEdgeFunction_analytic M K e
      (cubicForbiddenPatternLength J e) tau
  · exact cubicProfileResolventEdgeFunction_analytic M hM K e htau

private def cubicProfilePatternIntersectionFunction
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (tau : C(S, ℂ)) : C((Fin (2 * ell) → S), ℂ) :=
  if CubicForbiddenPatternCompatible J then
    cubicProfileBranchFunction ell tau *
      ∏ e : Fin (3 * ell), cubicProfilePatternEdgeFunction M K J e tau
  else 0

private theorem cubicProfilePatternIntersectionFunction_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ (cubicProfilePatternIntersectionFunction M K J)
      tau := by
  classical
  unfold cubicProfilePatternIntersectionFunction
  split_ifs
  · apply (cubicProfileBranchFunction_analytic (S := S) ell tau).mul
    exact (Finset.univ : Finset (Fin (3 * ell))).analyticAt_fun_prod
      (fun e _ ↦ cubicProfilePatternEdgeFunction_analytic M hM K J e htau)
  · exact analyticAt_const

private def cubicProfileKernelForbiddenCorrectionFunction
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (tau : C(S, ℂ)) :
    C((Fin (2 * ell) → S), ℂ) := by
  letI := cubicKernelForbiddenLengthWitnessFintype K.graph
  exact Finset.sum
    ((Finset.univ :
      Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
        Finset.Nonempty)
    (fun J ↦ (-1 : ℂ) ^ (J.card + 1) •
      cubicProfilePatternIntersectionFunction M K J tau)

private theorem cubicProfileKernelForbiddenCorrectionFunction_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ (cubicProfileKernelForbiddenCorrectionFunction M K)
      tau := by
  let _ := cubicKernelForbiddenLengthWitnessFintype K.graph
  unfold cubicProfileKernelForbiddenCorrectionFunction
  let s := (Finset.univ :
    Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
      Finset.Nonempty
  let F : Finset (CubicKernelForbiddenLengthWitness K.graph) →
      (C(S, ℂ) → C((Fin (2 * ell) → S), ℂ)) := fun J tau ↦
    (-1 : ℂ) ^ (J.card + 1) •
      cubicProfilePatternIntersectionFunction M K J tau
  change AnalyticAt ℂ (fun sigma : C(S, ℂ) ↦ ∑ J ∈ s, F J sigma) tau
  have hsum : AnalyticAt ℂ (∑ J ∈ s, F J) tau := by
    apply Finset.analyticAt_sum
    intro J hJ
    have hconst : AnalyticAt ℂ
        (fun _ : C(S, ℂ) ↦ (-1 : ℂ) ^ (J.card + 1)) tau :=
      analyticAt_const
    exact hconst.smul
      (cubicProfilePatternIntersectionFunction_analytic M hM K J htau)
  have hfun : (∑ J ∈ s, F J) =
      (fun sigma : C(S, ℂ) ↦ ∑ J ∈ s, F J sigma) := by
    funext sigma
    exact Finset.sum_apply sigma s F
  rw [← hfun]
  exact hsum

private def cubicProfileKernelUnrestrictedFunction
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (tau : C(S, ℂ)) :
    C((Fin (2 * ell) → S), ℂ) :=
  cubicProfileBranchFunction ell tau *
    ∏ e : Fin (3 * ell), cubicProfileResolventEdgeFunction M K e tau

private theorem cubicProfileKernelUnrestrictedFunction_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ (cubicProfileKernelUnrestrictedFunction M K)
      tau := by
  unfold cubicProfileKernelUnrestrictedFunction
  apply (cubicProfileBranchFunction_analytic (S := S) ell tau).mul
  exact (Finset.univ : Finset (Fin (3 * ell))).analyticAt_fun_prod
    (fun e _ ↦ cubicProfileResolventEdgeFunction_analytic M hM K e htau)

private def cubicProfileKernelAdmissibleIEResolvent
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell) (tau : C(S, ℂ)) : ℂ :=
  cubicKernelIntegralCLM M ell
    (cubicProfileKernelUnrestrictedFunction M K tau -
      cubicProfileKernelForbiddenCorrectionFunction M K tau)

private theorem cubicProfileKernelAdmissibleIEResolvent_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ (cubicProfileKernelAdmissibleIEResolvent M K)
      tau := by
  unfold cubicProfileKernelAdmissibleIEResolvent
  exact (cubicKernelIntegralCLM M ell).analyticAt _ |>.comp
    ((cubicProfileKernelUnrestrictedFunction_analytic M hM K htau).sub
      (cubicProfileKernelForbiddenCorrectionFunction_analytic M hM K htau))

/-- The finite generic-profile inclusion--exclusion resolvent.  It is an
auxiliary analytic realization of the literal profile series. -/
def positiveSurplusCubicProfileIEResolvent
    (M : FiniteIrreducibleModel S) (ell : ℕ) (tau : C(S, ℂ)) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      cubicProfileKernelAdmissibleIEResolvent M K tau

/-- The finite IE resolvent is analytic at every strictly subcritical
profile. -/
theorem positiveSurplusCubicProfileIEResolvent_analyticAt_of_norm_lt_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (ell : ℕ)
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ (positiveSurplusCubicProfileIEResolvent M ell)
      tau := by
  let _ := labelledConnectedCubicKernelFintype ell
  unfold positiveSurplusCubicProfileIEResolvent
  let F : LabelledConnectedCubicKernel ell → (C(S, ℂ) → ℂ) :=
    fun K tau ↦ labelledCubicKernelInverseMultiplicity K *
      cubicProfileKernelAdmissibleIEResolvent M K tau
  change AnalyticAt ℂ (fun sigma : C(S, ℂ) ↦ ∑ K, F K sigma) tau
  have hsum : AnalyticAt ℂ (∑ K, F K) tau := by
    apply Finset.analyticAt_sum Finset.univ
    intro K _
    exact analyticAt_const.mul
      (cubicProfileKernelAdmissibleIEResolvent_analytic M hM K htau)
  have hfun : (∑ K, F K) =
      (fun sigma : C(S, ℂ) ↦ ∑ K, F K sigma) := by
    funext sigma
    exact Fintype.sum_apply sigma F
  rw [← hfun]
  exact hsum

/-- The zero-profile IE germ is the base-point specialization of the
strict-subcritical statement. -/
theorem positiveSurplusCubicProfileIEResolvent_analyticAt_zero
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (ell : ℕ) :
    AnalyticAt ℂ (positiveSurplusCubicProfileIEResolvent M ell)
      (0 : C(S, ℂ)) :=
  positiveSurplusCubicProfileIEResolvent_analyticAt_of_norm_lt_one
    M hM ell (by simp)

/-! ## Literal assignment interpretation -/

private def cubicProfilePatternEdgeCoefficient
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) (tau : C(S, ℂ))
    (x : Fin (2 * ell) → S) (n : ℕ) : ℂ :=
  if CubicForbiddenPatternForcesEdge J e then
    if n = cubicForbiddenPatternLength J e then
      profilePathEdgeCoefficient M.bjrModel tau
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) n
    else 0
  else
    profilePathEdgeCoefficient M.bjrModel tau
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2) n

private theorem cubicProfilePatternEdgeCoefficient_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) (tau : C(S, ℂ))
    (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    Summable (cubicProfilePatternEdgeCoefficient M K J e tau x) := by
  classical
  by_cases he : CubicForbiddenPatternForcesEdge J e
  · let c : ℕ → ℂ := fun n ↦
      profilePathEdgeCoefficient M.bjrModel tau
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) n
    have hs := (hasSum_ite_eq (cubicForbiddenPatternLength J e)
      (c (cubicForbiddenPatternLength J e))).summable
    exact hs.congr (fun n ↦ by
      by_cases hn : n = cubicForbiddenPatternLength J e
      · subst n
        simp [cubicProfilePatternEdgeCoefficient, he, c]
      · simp [cubicProfilePatternEdgeCoefficient, he, hn, c])
  · exact (summable_profilePathEdgeCoefficient M hM tau r hr hr1
      (fun y ↦ (tau.norm_coe_le_norm y).trans htau)
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2)).congr
        (fun n ↦ by simp [cubicProfilePatternEdgeCoefficient, he])

private theorem tsum_cubicProfilePatternEdgeCoefficient
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) (tau : C(S, ℂ))
    (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    (∑' n : ℕ, cubicProfilePatternEdgeCoefficient M K J e tau x n) =
      cubicProfilePatternEdgeFunction M K J e tau x := by
  classical
  by_cases he : CubicForbiddenPatternForcesEdge J e
  · let c : ℕ → ℂ := fun n ↦
      profilePathEdgeCoefficient M.bjrModel tau
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) n
    calc
      (∑' n : ℕ, cubicProfilePatternEdgeCoefficient M K J e tau x n) =
          c (cubicForbiddenPatternLength J e) := by
        calc
          _ = ∑' n : ℕ, if n = cubicForbiddenPatternLength J e then
              c (cubicForbiddenPatternLength J e) else 0 := by
            apply tsum_congr
            intro n
            by_cases hn : n = cubicForbiddenPatternLength J e
            · subst n
              simp [cubicProfilePatternEdgeCoefficient, he, c]
            · simp [cubicProfilePatternEdgeCoefficient, he, hn, c]
          _ = c (cubicForbiddenPatternLength J e) :=
            (hasSum_ite_eq (cubicForbiddenPatternLength J e)
              (c (cubicForbiddenPatternLength J e))).tsum_eq
      _ = cubicProfilePatternEdgeFunction M K J e tau x := by
        simp [cubicProfilePatternEdgeFunction,
          cubicProfileFixedLengthEdgeFunction_apply, he, c]
  · rw [show (∑' n : ℕ,
        cubicProfilePatternEdgeCoefficient M K J e tau x n) =
        ∑' n : ℕ, profilePathEdgeCoefficient M.bjrModel tau
          (x (cubicKernelOrderedEndpoints K.graph e).1)
          (x (cubicKernelOrderedEndpoints K.graph e).2) n by
      apply tsum_congr
      intro n
      simp [cubicProfilePatternEdgeCoefficient, he]]
    rw [tsum_profilePathEdgeCoefficient_eq_profilePathResolventKernel
      M hM tau r hr hr1
      (fun y ↦ (tau.norm_coe_le_norm y).trans htau)]
    simp [cubicProfilePatternEdgeFunction,
      cubicProfileResolventEdgeFunction_apply, he]

private def cubicProfilePatternAssignmentWeight
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S)
    (l : Fin (3 * ell) → ℕ) : ℂ :=
  if CubicForbiddenPatternCompatible J then
    ∏ e : Fin (3 * ell),
      cubicProfilePatternEdgeCoefficient M K J e tau x (l e)
  else 0

private theorem cubicProfilePatternAssignmentWeight_eq_occurrenceIndicator
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S)
    (l : Fin (3 * ell) → ℕ) :
    cubicProfilePatternAssignmentWeight M K J tau x l =
      if ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M.bjrModel tau
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
      else 0 := by
  classical
  by_cases hall : ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l)
  · obtain ⟨hcompat, hlength⟩ :=
      (cubicForbiddenPattern_all_occurs_iff J l).mp hall
    rw [if_pos hall]
    unfold cubicProfilePatternAssignmentWeight
    rw [if_pos hcompat]
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : CubicForbiddenPatternForcesEdge J e
    · simp [cubicProfilePatternEdgeCoefficient, he, hlength e he]
    · simp [cubicProfilePatternEdgeCoefficient, he]
  · rw [if_neg hall]
    unfold cubicProfilePatternAssignmentWeight
    by_cases hcompat : CubicForbiddenPatternCompatible J
    · rw [if_pos hcompat]
      have hnot : ¬ ∀ e, CubicForbiddenPatternForcesEdge J e →
          l e = cubicForbiddenPatternLength J e := by
        intro hlength
        exact hall ((cubicForbiddenPattern_all_occurs_iff J l).mpr
          ⟨hcompat, hlength⟩)
      push Not at hnot
      obtain ⟨e, he, hne⟩ := hnot
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [cubicProfilePatternEdgeCoefficient, he, hne]
    · simp [hcompat]

private theorem cubicProfilePatternAssignmentWeight_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    Summable (cubicProfilePatternAssignmentWeight M K J tau x) := by
  classical
  by_cases hcompat : CubicForbiddenPatternCompatible J
  · exact (summable_finFunction_prod_and_tsum
        (fun e n ↦ cubicProfilePatternEdgeCoefficient M K J e tau x n)
        (fun e ↦ cubicProfilePatternEdgeCoefficient_summable
          M hM K J e tau x r hr hr1 htau)).1.congr
      (fun l ↦ by simp [cubicProfilePatternAssignmentWeight, hcompat])
  · exact summable_zero.congr
      (fun l ↦ by simp [cubicProfilePatternAssignmentWeight, hcompat])

private theorem tsum_cubicProfilePatternAssignmentWeight
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r)
    (hcompat : CubicForbiddenPatternCompatible J) :
    (∑' l : Fin (3 * ell) → ℕ,
        cubicProfilePatternAssignmentWeight M K J tau x l) =
      ∏ e : Fin (3 * ell), cubicProfilePatternEdgeFunction M K J e tau x := by
  classical
  simp only [cubicProfilePatternAssignmentWeight, hcompat, if_true]
  rw [(summable_finFunction_prod_and_tsum
    (fun e n ↦ cubicProfilePatternEdgeCoefficient M K J e tau x n)
    (fun e ↦ cubicProfilePatternEdgeCoefficient_summable
      M hM K J e tau x r hr hr1 htau)).2]
  apply Finset.prod_congr rfl
  intro e _
  exact tsum_cubicProfilePatternEdgeCoefficient
    M hM K J e tau x r hr hr1 htau

private def cubicProfileLiteralForbiddenAssignmentIntegrand
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S) : ℂ :=
  cubicProfileBranchFunction ell tau x *
    ∑' l : Fin (3 * ell) → ℕ,
      if ∃ w : CubicKernelForbiddenLengthWitness K.graph,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M.bjrModel tau
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
      else 0

private theorem cubicProfileKernelForbiddenCorrectionFunction_apply
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    cubicProfileKernelForbiddenCorrectionFunction M K tau x =
      cubicProfileLiteralForbiddenAssignmentIntegrand M K tau x := by
  let _ := cubicKernelForbiddenLengthWitnessFintype K.graph
  classical
  let P := (Finset.univ :
    Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
      Finset.Nonempty
  let B : (Fin (3 * ell) → ℕ) → ℂ := fun l ↦
    ∏ e : Fin (3 * ell),
      profilePathEdgeCoefficient M.bjrModel tau
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
  have hJsum (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
      cubicProfilePatternIntersectionFunction M K J tau x =
        cubicProfileBranchFunction ell tau x *
          ∑' l : Fin (3 * ell) → ℕ,
            cubicProfilePatternAssignmentWeight M K J tau x l := by
    unfold cubicProfilePatternIntersectionFunction
    by_cases hcompat : CubicForbiddenPatternCompatible J
    · rw [if_pos hcompat,
          tsum_cubicProfilePatternAssignmentWeight
            M hM K J tau x r hr hr1 htau hcompat]
      rw [ContinuousMap.mul_apply, ContinuousMap.prod_apply]
    · rw [if_neg hcompat]
      have hzero :
          (∑' l : Fin (3 * ell) → ℕ,
            cubicProfilePatternAssignmentWeight M K J tau x l) = 0 := by
        simp [cubicProfilePatternAssignmentWeight, hcompat]
      rw [hzero, mul_zero]
      rfl
  have hsumJ (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
      Summable (fun l : Fin (3 * ell) → ℕ ↦
        (-1 : ℂ) ^ (J.card + 1) *
          cubicProfilePatternAssignmentWeight M K J tau x l) :=
    (cubicProfilePatternAssignmentWeight_summable
      M hM K J tau x r hr hr1 htau).mul_left _
  unfold cubicProfileKernelForbiddenCorrectionFunction
    cubicProfileLiteralForbiddenAssignmentIntegrand
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [hJsum]
  rw [show (∑ J ∈ P, (-1 : ℂ) ^ (J.card + 1) *
        (cubicProfileBranchFunction ell tau x *
          ∑' l : Fin (3 * ell) → ℕ,
            cubicProfilePatternAssignmentWeight M K J tau x l)) =
      cubicProfileBranchFunction ell tau x *
        ∑ J ∈ P, (-1 : ℂ) ^ (J.card + 1) *
          ∑' l : Fin (3 * ell) → ℕ,
            cubicProfilePatternAssignmentWeight M K J tau x l by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J _
      ring]
  have hswap := Summable.tsum_finsetSum
    (s := P)
    (f := fun J l ↦ (-1 : ℂ) ^ (J.card + 1) *
      cubicProfilePatternAssignmentWeight M K J tau x l)
    (fun J _ ↦ hsumJ J)
  have hscale (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
      (-1 : ℂ) ^ (J.card + 1) *
          ∑' l : Fin (3 * ell) → ℕ,
            cubicProfilePatternAssignmentWeight M K J tau x l =
        ∑' l : Fin (3 * ell) → ℕ,
          (-1 : ℂ) ^ (J.card + 1) *
            cubicProfilePatternAssignmentWeight M K J tau x l :=
    ((cubicProfilePatternAssignmentWeight_summable
      M hM K J tau x r hr hr1 htau).tsum_mul_left _).symm
  simp_rw [hscale]
  rw [← hswap]
  apply congrArg (fun z : ℂ ↦ cubicProfileBranchFunction ell tau x * z)
  apply tsum_congr
  intro l
  simp_rw [cubicProfilePatternAssignmentWeight_eq_occurrenceIndicator]
  have hIE := cubicForbidden_inclusionExclusion_assignment K l (B l)
  convert hIE using 1 <;> simp only [P, B]
  · apply Finset.sum_congr rfl
    intro J _
    congr 1
    by_cases hocc : ∀ w ∈ J,
        w.Occurs (Finsupp.equivFunOnFinite.symm l)
    · simp
    · simp
  · by_cases hex : ∃ w : CubicKernelForbiddenLengthWitness K.graph,
        w.Occurs (Finsupp.equivFunOnFinite.symm l)
    · simp [hex]
    · simp [hex]

private def cubicProfileLiteralUnrestrictedAssignmentIntegrand
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S) : ℂ :=
  cubicProfileBranchFunction ell tau x *
    ∑' l : Fin (3 * ell) → ℕ,
      ∏ e : Fin (3 * ell),
        profilePathEdgeCoefficient M.bjrModel tau
          (x (cubicKernelOrderedEndpoints K.graph e).1)
          (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)

private def cubicProfileLiteralAdmissibleAssignmentIntegrand
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S) : ℂ :=
  cubicProfileBranchFunction ell tau x *
    ∑' l : Fin (3 * ell) → ℕ,
      if CubicKernelLengthAssignment.IsAdmissible K.graph
          (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M.bjrModel tau
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
      else 0

private theorem cubicProfileKernelAssignmentProduct_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    Summable (fun l : Fin (3 * ell) → ℕ ↦
      ∏ e : Fin (3 * ell),
        profilePathEdgeCoefficient M.bjrModel tau
          (x (cubicKernelOrderedEndpoints K.graph e).1)
          (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)) := by
  exact (summable_finFunction_prod_and_tsum
    (fun e n ↦ profilePathEdgeCoefficient M.bjrModel tau
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2) n)
    (fun e ↦ summable_profilePathEdgeCoefficient M hM tau r hr hr1
      (fun y ↦ (tau.norm_coe_le_norm y).trans htau) _ _)).1

private theorem cubicProfileKernelUnrestrictedFunction_apply
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    cubicProfileKernelUnrestrictedFunction M K tau x =
      cubicProfileLiteralUnrestrictedAssignmentIntegrand M K tau x := by
  unfold cubicProfileKernelUnrestrictedFunction
    cubicProfileLiteralUnrestrictedAssignmentIntegrand
  rw [ContinuousMap.mul_apply, ContinuousMap.prod_apply]
  apply congrArg (fun z : ℂ ↦ cubicProfileBranchFunction ell tau x * z)
  rw [(summable_finFunction_prod_and_tsum
    (fun e n ↦ profilePathEdgeCoefficient M.bjrModel tau
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2) n)
    (fun e ↦ summable_profilePathEdgeCoefficient M hM tau r hr hr1
      (fun y ↦ (tau.norm_coe_le_norm y).trans htau) _ _)).2]
  apply Finset.prod_congr rfl
  intro e _
  exact (tsum_profilePathEdgeCoefficient_eq_profilePathResolventKernel
    M hM tau r hr hr1
      (fun y ↦ (tau.norm_coe_le_norm y).trans htau) _ _).symm

private theorem cubicProfileLiteralAdmissible_add_forbidden_eq_unrestricted
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    cubicProfileLiteralAdmissibleAssignmentIntegrand M K tau x +
        cubicProfileLiteralForbiddenAssignmentIntegrand M K tau x =
      cubicProfileLiteralUnrestrictedAssignmentIntegrand M K tau x := by
  classical
  let B : (Fin (3 * ell) → ℕ) → ℂ := fun l ↦
    ∏ e : Fin (3 * ell),
      profilePathEdgeCoefficient M.bjrModel tau
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
  let A : Set (Fin (3 * ell) → ℕ) := {l |
    CubicKernelLengthAssignment.IsAdmissible K.graph
      (Finsupp.equivFunOnFinite.symm l)}
  let F : Set (Fin (3 * ell) → ℕ) := {l |
    ∃ w : CubicKernelForbiddenLengthWitness K.graph,
      w.Occurs (Finsupp.equivFunOnFinite.symm l)}
  have hB : Summable B :=
    cubicProfileKernelAssignmentProduct_summable
      M hM K tau x r hr hr1 htau
  have hA : Summable (A.indicator B) := hB.indicator A
  have hF : Summable (F.indicator B) := hB.indicator F
  have hterm (l : Fin (3 * ell) → ℕ) :
      A.indicator B l + F.indicator B l = B l := by
    have hiff := not_cubicKernelLengthAssignment_admissible_iff K.graph
      (Finsupp.equivFunOnFinite.symm l)
    by_cases ha : CubicKernelLengthAssignment.IsAdmissible K.graph
        (Finsupp.equivFunOnFinite.symm l)
    · have hf : ¬ ∃ w : CubicKernelForbiddenLengthWitness K.graph,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) := by
        exact fun hw ↦ (hiff.mpr hw) ha
      have hAl : l ∈ A := by simpa [A] using ha
      have hFl : l ∉ F := by simpa [F] using hf
      simp [Set.indicator, hAl, hFl]
    · have hf : ∃ w : CubicKernelForbiddenLengthWitness K.graph,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) := hiff.mp ha
      have hAl : l ∉ A := by simpa [A] using ha
      have hFl : l ∈ F := by simpa [F] using hf
      simp [Set.indicator, hAl, hFl]
  unfold cubicProfileLiteralAdmissibleAssignmentIntegrand
    cubicProfileLiteralForbiddenAssignmentIntegrand
    cubicProfileLiteralUnrestrictedAssignmentIntegrand
  rw [← mul_add]
  apply congrArg (fun z : ℂ ↦ cubicProfileBranchFunction ell tau x * z)
  change (∑' l, A.indicator B l) + (∑' l, F.indicator B l) = ∑' l, B l
  rw [← hA.tsum_add hF]
  exact tsum_congr hterm

private theorem cubicProfileKernelAdmissibleIEResolvent_eq_literalIntegral
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    cubicProfileKernelAdmissibleIEResolvent M K tau =
      ∫ x : Fin (2 * ell) → S,
        cubicProfileLiteralAdmissibleAssignmentIntegrand M K tau x
          ∂cubicKernelProductMeasure M ell := by
  unfold cubicProfileKernelAdmissibleIEResolvent
  rw [cubicKernelIntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ContinuousMap.sub_apply]
  rw [cubicProfileKernelUnrestrictedFunction_apply
    M hM K tau x r hr hr1 htau]
  rw [cubicProfileKernelForbiddenCorrectionFunction_apply
    M hM K tau x r hr hr1 htau]
  have hsplit :=
    cubicProfileLiteralAdmissible_add_forbidden_eq_unrestricted
      M hM K tau x r hr hr1 htau
  exact sub_eq_iff_eq_add.mpr hsplit.symm

/-! ## Reindexing the literal assignment sum by total length -/

private def profileFinFunctionEquivSigmaFinsuppAntidiagonal (n : ℕ) :
    (Fin n → ℕ) ≃
      Σ d : ℕ,
        (Finset.univ.finsuppAntidiag d : Finset (Fin n →₀ ℕ)) where
  toFun l := by
    let f : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm l
    refine ⟨∑ i, l i, ⟨f, ?_⟩⟩
    rw [Finset.mem_finsuppAntidiag]
    constructor
    · simp [f]
    · exact Finset.subset_univ _
  invFun Q := Finsupp.equivFunOnFinite Q.2.1
  left_inv l := by
    funext i
    simp
  right_inv Q := by
    rcases Q with ⟨d, ⟨f, hf⟩⟩
    have hsum : (∑ i, Finsupp.equivFunOnFinite f i) = d := by
      simpa using (Finset.mem_finsuppAntidiag.mp hf).1
    apply Sigma.subtype_ext hsum
    ext i
    simp

private def cubicProfileAdmissibleAssignmentFunction
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (l : Fin (3 * ell) → ℕ) :
    C((Fin (2 * ell) → S), ℂ) :=
  if CubicKernelLengthAssignment.IsAdmissible K.graph
      (Finsupp.equivFunOnFinite.symm l) then
    cubicProfileBranchFunction ell tau *
      ∏ e : Fin (3 * ell),
        cubicProfileFixedLengthEdgeFunction M K e (l e) tau
  else 0

@[simp] private theorem cubicProfileAdmissibleAssignmentFunction_apply
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (l : Fin (3 * ell) → ℕ)
    (x : Fin (2 * ell) → S) :
    cubicProfileAdmissibleAssignmentFunction M K tau l x =
      if CubicKernelLengthAssignment.IsAdmissible K.graph
          (Finsupp.equivFunOnFinite.symm l) then
        cubicProfileBranchFunction ell tau x *
          ∏ e : Fin (3 * ell),
            profilePathEdgeCoefficient M.bjrModel tau
              (x (cubicKernelOrderedEndpoints K.graph e).1)
              (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
      else 0 := by
  classical
  by_cases hl : CubicKernelLengthAssignment.IsAdmissible K.graph
      (Finsupp.equivFunOnFinite.symm l)
  · simp [cubicProfileAdmissibleAssignmentFunction, hl,
      ContinuousMap.prod_apply]
  · simp [cubicProfileAdmissibleAssignmentFunction, hl]

private theorem cubicProfileAdmissibleAssignmentFunction_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    Summable (cubicProfileAdmissibleAssignmentFunction M K tau) := by
  classical
  let A : Set (Fin (3 * ell) → ℕ) := {l |
    CubicKernelLengthAssignment.IsAdmissible K.graph
      (Finsupp.equivFunOnFinite.symm l)}
  let P : (Fin (3 * ell) → ℕ) →
      C((Fin (2 * ell) → S), ℂ) := fun l ↦
    ∏ e : Fin (3 * ell),
      cubicProfileFixedLengthEdgeFunction M K e (l e) tau
  have hP : Summable P :=
    (summable_norm_finFunction_prod_and_tsum
      (fun e n ↦ cubicProfileFixedLengthEdgeFunction M K e n tau)
      (fun e ↦ cubicProfileFixedLengthEdgeFunction_norm_summable
        M hM K e tau r hr hr1 htau)).1.of_norm
  have hA : Summable (A.indicator P) := hP.indicator A
  have hmul := hA.mul_left (cubicProfileBranchFunction ell tau)
  exact hmul.congr (fun l ↦ by
    by_cases hl : CubicKernelLengthAssignment.IsAdmissible K.graph
        (Finsupp.equivFunOnFinite.symm l)
    · simp [cubicProfileAdmissibleAssignmentFunction, A, P, hl]
    · simp [cubicProfileAdmissibleAssignmentFunction, A, P, hl])

private def cubicProfileAdmissibleDegreeFunction
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (d : ℕ) : C((Fin (2 * ell) → S), ℂ) :=
  letI := cubicKernelLengthProfileFintype
    (2 * ell + d) ell K.graph
  ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
    cubicProfileBranchFunction ell tau *
      ∏ e : Fin (3 * ell),
        cubicProfileFixedLengthEdgeFunction M K e (L.length e).val tau

@[simp] private theorem cubicProfileAdmissibleDegreeFunction_apply
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (d : ℕ) (x : Fin (2 * ell) → S) :
    cubicProfileAdmissibleDegreeFunction M K tau d x =
      cubicProfileBranchFunction ell tau x *
        cubicKernelAdmissiblePathCoefficient M.bjrModel tau K x d := by
  classical
  unfold cubicProfileAdmissibleDegreeFunction
    cubicKernelAdmissiblePathCoefficient
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.prod_apply, cubicProfileFixedLengthEdgeFunction_apply,
    Finset.mul_sum]

private theorem cubicProfileAdmissibleAssignment_sigma_block
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (d : ℕ) :
    (∑ A : (Finset.univ.finsuppAntidiag d :
          Finset (Fin (3 * ell) →₀ ℕ)),
        cubicProfileAdmissibleAssignmentFunction M K tau
          (Finsupp.equivFunOnFinite A.1)) =
      cubicProfileAdmissibleDegreeFunction M K tau d := by
  classical
  let p : ↥(Finset.univ.finsuppAntidiag d :
      Finset (Fin (3 * ell) →₀ ℕ)) → Prop := fun A ↦
    CubicKernelLengthAssignment.IsAdmissible K.graph A.1
  rw [show (∑ A : (Finset.univ.finsuppAntidiag d :
      Finset (Fin (3 * ell) →₀ ℕ)),
      cubicProfileAdmissibleAssignmentFunction M K tau
        (Finsupp.equivFunOnFinite A.1)) =
      ∑ A, if h : p A then
        cubicProfileBranchFunction ell tau *
          ∏ e : Fin (3 * ell),
            cubicProfileFixedLengthEdgeFunction M K e (A.1 e) tau
        else 0 by
      apply Fintype.sum_congr
      intro A
      have hfun : Finsupp.equivFunOnFinite (A.1) =
          (fun e ↦ A.1 e) := rfl
      have hsymm : Finsupp.equivFunOnFinite.symm (fun e ↦ A.1 e) =
          A.1 := by
        rw [← hfun]
        exact Equiv.symm_apply_apply _ _
      simp only [cubicProfileAdmissibleAssignmentFunction, p,
        hfun, hsymm]
      by_cases hA : CubicKernelLengthAssignment.IsAdmissible K.graph A.1
      <;> simp [hA]]
  rw [PerronWright.FieldRootedTree.sum_dite_eq_sum_subtype p]
  unfold cubicProfileAdmissibleDegreeFunction
  let _ : Fintype
      (CubicKernelLengthProfile (2 * ell + d) ell K.graph) :=
    cubicKernelLengthProfileFintype (2 * ell + d) ell K.graph
  exact (Fintype.sum_equiv
    (cubicKernelLengthProfileEquivAdmissibleAntidiagonal d ell K.graph)
    (fun L : CubicKernelLengthProfile (2 * ell + d) ell K.graph ↦
      cubicProfileBranchFunction ell tau *
        ∏ e : Fin (3 * ell),
          cubicProfileFixedLengthEdgeFunction M K e (L.length e).val tau)
    (fun A : CubicKernelAdmissibleLengthAntidiagonal d ell K.graph ↦
      cubicProfileBranchFunction ell tau *
        ∏ e : Fin (3 * ell),
          cubicProfileFixedLengthEdgeFunction M K e (A.1.1 e) tau)
    (fun L ↦ by rfl)).symm

private theorem tsum_cubicProfileAdmissibleDegreeFunction_eq_assignment
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    (∑' d : ℕ, cubicProfileAdmissibleDegreeFunction M K tau d) =
      ∑' l : Fin (3 * ell) → ℕ,
        cubicProfileAdmissibleAssignmentFunction M K tau l := by
  classical
  let e := profileFinFunctionEquivSigmaFinsuppAntidiagonal (3 * ell)
  let F := cubicProfileAdmissibleAssignmentFunction M K tau
  have hF : Summable F :=
    cubicProfileAdmissibleAssignmentFunction_summable
      M hM K tau r hr hr1 htau
  have hSigma : Summable (fun Q : Σ d : ℕ,
      (Finset.univ.finsuppAntidiag d : Finset (Fin (3 * ell) →₀ ℕ)) ↦
      F (e.symm Q)) := hF.comp_injective e.symm.injective
  calc
    (∑' d : ℕ, cubicProfileAdmissibleDegreeFunction M K tau d) =
        ∑' d : ℕ,
          ∑' A : (Finset.univ.finsuppAntidiag d :
            Finset (Fin (3 * ell) →₀ ℕ)), F (e.symm ⟨d, A⟩) := by
      apply tsum_congr
      intro d
      rw [tsum_fintype]
      change cubicProfileAdmissibleDegreeFunction M K tau d =
        ∑ A : (Finset.univ.finsuppAntidiag d :
          Finset (Fin (3 * ell) →₀ ℕ)),
          cubicProfileAdmissibleAssignmentFunction M K tau
            (Finsupp.equivFunOnFinite A.1)
      exact (cubicProfileAdmissibleAssignment_sigma_block M K tau d).symm
    _ = ∑' Q : Σ d : ℕ,
          (Finset.univ.finsuppAntidiag d :
            Finset (Fin (3 * ell) →₀ ℕ)), F (e.symm Q) := by
      exact hSigma.tsum_sigma.symm
    _ = ∑' l : Fin (3 * ell) → ℕ, F l := by
      exact e.symm.tsum_eq F

private theorem cubicProfileIntegral_admissibleDegreeFunction
    (M : FiniteIrreducibleModel S) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ)) (d : ℕ) :
    cubicKernelIntegralCLM M ell
        (cubicProfileAdmissibleDegreeFunction M K tau d) =
      letI := cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
      ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
        cubicLengthProfileComplexKernelIntegral M.bjrModel tau K L := by
  classical
  let _ : Fintype
      (CubicKernelLengthProfile (2 * ell + d) ell K.graph) :=
    cubicKernelLengthProfileFintype (2 * ell + d) ell K.graph
  unfold cubicProfileAdmissibleDegreeFunction
  rw [map_sum]
  apply Fintype.sum_congr
  intro L
  rw [cubicKernelIntegralCLM_apply]
  unfold cubicLengthProfileComplexKernelIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ContinuousMap.mul_apply, ContinuousMap.prod_apply,
    cubicProfileBranchFunction_apply,
    cubicProfileFixedLengthEdgeFunction_apply]

private theorem tsum_cubicProfileLengthIntegral_eq_literalAdmissibleIntegral
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    (∑' d : ℕ,
      letI := cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
      ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
        cubicLengthProfileComplexKernelIntegral M.bjrModel tau K L) =
      ∫ x : Fin (2 * ell) → S,
        cubicProfileLiteralAdmissibleAssignmentIntegrand M K tau x
          ∂cubicKernelProductMeasure M ell := by
  have hF := cubicProfileAdmissibleAssignmentFunction_summable
    M hM K tau r hr hr1 htau
  have hD : Summable (cubicProfileAdmissibleDegreeFunction M K tau) := by
    let e := profileFinFunctionEquivSigmaFinsuppAntidiagonal (3 * ell)
    let F := cubicProfileAdmissibleAssignmentFunction M K tau
    have hSigma : Summable (fun Q : Σ d : ℕ,
        (Finset.univ.finsuppAntidiag d : Finset (Fin (3 * ell) →₀ ℕ)) ↦
        F (e.symm Q)) := hF.comp_injective e.symm.injective
    exact hSigma.sigma.congr (fun d ↦ by
      rw [tsum_fintype]
      change (∑ A : (Finset.univ.finsuppAntidiag d :
          Finset (Fin (3 * ell) →₀ ℕ)),
          cubicProfileAdmissibleAssignmentFunction M K tau
            (Finsupp.equivFunOnFinite A.1)) =
        cubicProfileAdmissibleDegreeFunction M K tau d
      exact cubicProfileAdmissibleAssignment_sigma_block M K tau d)
  calc
    (∑' d : ℕ,
      letI := cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
      ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
        cubicLengthProfileComplexKernelIntegral M.bjrModel tau K L) =
        ∑' d : ℕ, cubicKernelIntegralCLM M ell
          (cubicProfileAdmissibleDegreeFunction M K tau d) := by
      apply tsum_congr
      intro d
      exact (cubicProfileIntegral_admissibleDegreeFunction M K tau d).symm
    _ = cubicKernelIntegralCLM M ell
          (∑' d : ℕ, cubicProfileAdmissibleDegreeFunction M K tau d) := by
      exact ((cubicKernelIntegralCLM M ell).map_tsum hD).symm
    _ = cubicKernelIntegralCLM M ell
          (∑' l : Fin (3 * ell) → ℕ,
            cubicProfileAdmissibleAssignmentFunction M K tau l) := by
      rw [tsum_cubicProfileAdmissibleDegreeFunction_eq_assignment
        M hM K tau r hr hr1 htau]
    _ = ∫ x : Fin (2 * ell) → S,
        cubicProfileLiteralAdmissibleAssignmentIntegrand M K tau x
          ∂cubicKernelProductMeasure M ell := by
      rw [cubicKernelIntegralCLM_apply]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← ContinuousMap.tsum_apply hF]
      unfold cubicProfileLiteralAdmissibleAssignmentIntegrand
      simp_rw [cubicProfileAdmissibleAssignmentFunction_apply]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro l
      by_cases hl : CubicKernelLengthAssignment.IsAdmissible K.graph
          (Finsupp.equivFunOnFinite.symm l) <;> simp [hl]

/-! ## Identification of the literal series with the finite IE resolvent -/

/-- On every strict-subcritical profile ball, the literal sum over all
admissible cubic length profiles is exactly the finite
inclusion--exclusion resolvent. -/
theorem positiveSurplusCubicProfileSeries_eq_profileIEResolvent
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (htau : ‖tau‖ ≤ r) :
    positiveSurplusCubicProfileSeries M ell tau =
      positiveSurplusCubicProfileIEResolvent M ell tau := by
  let _ : Fintype (LabelledConnectedCubicKernel ell) :=
    labelledConnectedCubicKernelFintype ell
  let f : LabelledConnectedCubicKernel ell → ℕ → ℂ := fun K d ↦
    labelledCubicKernelInverseMultiplicity K *
      letI := cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
      ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
        cubicLengthProfileComplexKernelIntegral M.bjrModel tau K L
  have hf (K : LabelledConnectedCubicKernel ell) : Summable (f K) := by
    have hAssign := cubicProfileAdmissibleAssignmentFunction_summable
      M hM K tau r hr hr1 htau
    have hD : Summable
        (cubicProfileAdmissibleDegreeFunction M K tau) := by
      let e := profileFinFunctionEquivSigmaFinsuppAntidiagonal (3 * ell)
      let F := cubicProfileAdmissibleAssignmentFunction M K tau
      have hSigma : Summable (fun Q : Σ d : ℕ,
          (Finset.univ.finsuppAntidiag d :
            Finset (Fin (3 * ell) →₀ ℕ)) ↦ F (e.symm Q)) :=
        hAssign.comp_injective e.symm.injective
      exact hSigma.sigma.congr (fun d ↦ by
        rw [tsum_fintype]
        change (∑ A : (Finset.univ.finsuppAntidiag d :
            Finset (Fin (3 * ell) →₀ ℕ)),
            cubicProfileAdmissibleAssignmentFunction M K tau
              (Finsupp.equivFunOnFinite A.1)) =
          cubicProfileAdmissibleDegreeFunction M K tau d
        exact cubicProfileAdmissibleAssignment_sigma_block M K tau d)
    have hInt : Summable (fun d ↦
        cubicKernelIntegralCLM M ell
          (cubicProfileAdmissibleDegreeFunction M K tau d)) :=
      hD.map (cubicKernelIntegralCLM M ell)
        (cubicKernelIntegralCLM M ell).continuous
    exact (hInt.congr (fun d ↦
      cubicProfileIntegral_admissibleDegreeFunction M K tau d)).mul_left _
  unfold positiveSurplusCubicProfileSeries
    positiveSurplusCubicAdmissibleProfileCoefficient
    positiveSurplusCubicProfileIEResolvent
  rw [Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun K d ↦ f K d) (fun K _ ↦ hf K)]
  apply Finset.sum_congr rfl
  intro K _
  rw [tsum_mul_left]
  apply congrArg (fun z : ℂ ↦ labelledCubicKernelInverseMultiplicity K * z)
  calc
    (∑' d : ℕ,
      letI := cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
      ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
        cubicLengthProfileComplexKernelIntegral M.bjrModel tau K L) =
        ∫ x : Fin (2 * ell) → S,
          cubicProfileLiteralAdmissibleAssignmentIntegrand M K tau x
            ∂cubicKernelProductMeasure M ell :=
      tsum_cubicProfileLengthIntegral_eq_literalAdmissibleIntegral
        M hM K tau r hr hr1 htau
    _ = cubicProfileKernelAdmissibleIEResolvent M K tau :=
      (cubicProfileKernelAdmissibleIEResolvent_eq_literalIntegral
        M hM K tau r hr hr1 htau).symm

/-- The genuine literal admissible-profile series is analytic at every
strictly subcritical profile.  The finite IE resolvent is used only on a
neighborhood contained in the open unit ball, so the public function remains
the literal `tsum`. -/
theorem positiveSurplusCubicProfileSeries_analyticAt_of_norm_lt_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (ell : ℕ)
    {tau : C(S, ℂ)} (htau : ‖tau‖ < 1) :
    AnalyticAt ℂ (positiveSurplusCubicProfileSeries M ell) tau := by
  apply
    (positiveSurplusCubicProfileIEResolvent_analyticAt_of_norm_lt_one
      M hM ell htau).congr
  have htauBall : tau ∈ Metric.ball (0 : C(S, ℂ)) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using htau
  filter_upwards [Metric.isOpen_ball.mem_nhds htauBall] with sigma hsigma
  have hsigmaNorm : ‖sigma‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hsigma
  let r : ℝ := (‖sigma‖ + 1) / 2
  have hr : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hsigmaR : ‖sigma‖ ≤ r := by
    dsimp only [r]
    linarith
  have hr1 : r < 1 := by
    dsimp only [r]
    linarith
  exact (positiveSurplusCubicProfileSeries_eq_profileIEResolvent
    M hM ell sigma r hr hr1 hsigmaR).symm

/-- The literal admissible cubic profile functional is analytic throughout
the open strict-subcritical unit ball. -/
theorem positiveSurplusCubicProfileSeries_analyticOnNhd_unitBall
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (ell : ℕ) :
    AnalyticOnNhd ℂ (positiveSurplusCubicProfileSeries M ell)
      (Metric.ball (0 : C(S, ℂ)) 1) := by
  intro tau htau
  apply positiveSurplusCubicProfileSeries_analyticAt_of_norm_lt_one
    M hM ell
  simpa only [Metric.mem_ball, dist_zero_right] using htau

/-- The zero-profile literal germ is the base-point specialization of
analyticity on the strict-subcritical unit ball. -/
theorem positiveSurplusCubicProfileSeries_analyticAt_zero
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (ell : ℕ) :
    AnalyticAt ℂ (positiveSurplusCubicProfileSeries M ell)
      (0 : C(S, ℂ)) :=
  positiveSurplusCubicProfileSeries_analyticAt_of_norm_lt_one
    M hM ell (by simp)

end PerronWright.FiniteIrreducibleKernelAmplitude


