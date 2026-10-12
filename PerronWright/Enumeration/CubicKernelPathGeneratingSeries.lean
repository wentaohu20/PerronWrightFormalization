import PerronWright.Enumeration.CubicPresentationProfileRegroup
import PerronWright.Enumeration.JointSimpleCycleEGF
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Fixed cubic kernels as finite products of marked-path series

This file is the exact bridge between the finite length-profile regrouping
and the marked-path resolvent.  For one oriented kernel edge, the coefficient
of degree `n` is the matrix coefficient of

`(K M_tau)^n K`.

The product over the `3 * ell` labelled kernel edges therefore records every
length assignment, and `PowerSeries.coeff_prod` identifies its degree-`d`
coefficient with the literal finite antidiagonal of assignments whose total
internal length is `d`.  Separately, admissible cubic length profiles are
identified exactly with the part of that antidiagonal satisfying the loop and
zero-length parallel-edge restrictions.

On a strict subcritical profile ball, the sum of the one-edge coefficients is
the already constructed path-resolvent kernel.  Thus the finite product of
their sums is literally the finite product of path-resolvent kernels.  No
interchange of an integral with an infinite sum, and no asymptotic claim, is
made here.
-/

open MeasureTheory PerronWright
open scoped Classical BigOperators

noncomputable section

namespace PerronWright.GraphCore

namespace MPR

export PerronWright.MarkedPathResolvent
  (profile pathOperatorParameterCLM operatorKernelize operatorKernelize_apply
   pathResolventKernel)

end MPR

namespace JS

export PerronWright.JointSimpleCycleEGF
  (profilePathOperator_pow_summable profilePathOperator_tsum_eq_inverse)

end JS

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private abbrev PathEnd (S : Type*) [MetricSpace S] [CompactSpace S] :=
  C(S, ℂ) →L[ℂ] C(S, ℂ)

/- The operator resolvent modules deliberately use the normed-algebra
structures on the endomorphism space.  Repeating those local choices here
keeps the summability statements definitionally aligned with their source. -/
local instance pathEndNormedRing : NormedRing (PathEnd S) := inferInstance
local instance pathEndSeminormedRing : SeminormedRing (PathEnd S) :=
  NormedRing.toSeminormedRing
@[reducible] local instance pathEndNormedAddCommGroup :
    NormedAddCommGroup (PathEnd S) :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance pathEndNormedAlgebra : NormedAlgebra ℂ (PathEnd S) := inferInstance
@[reducible] local instance pathEndNormedSpace : NormedSpace ℂ (PathEnd S) :=
  NormedAlgebra.toNormedSpace (PathEnd S)
local instance pathEndNormTopology : TopologicalSpace (PathEnd S) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-! ## Admissible profiles as a finite antidiagonal -/

/-- The two local simplicity restrictions on a finitely supported assignment
of internal lengths to the labelled edges of a cubic kernel. -/
def CubicKernelLengthAssignment.IsAdmissible
    {ell : ℕ} (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (l : Fin (3 * ell) →₀ ℕ) : Prop :=
  (∀ e, (H.endpoints e).IsDiag → 2 ≤ l e) ∧
    Function.Injective
      (fun e : {e : Fin (3 * ell) // l e = 0} ↦ H.endpoints e.1)

/-- The finite antidiagonal of total internal length `d`, restricted by the
two local simplicity conditions. -/
abbrev CubicKernelAdmissibleLengthAntidiagonal
    (d ell : ℕ) (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :=
  {l : (Finset.univ.finsuppAntidiag d :
      Finset (Fin (3 * ell) →₀ ℕ)) //
    CubicKernelLengthAssignment.IsAdmissible H l.1}

/-- Forget the `Fin (k+1)` bounds in an admissible length profile. -/
def CubicKernelLengthProfile.toFinsupp
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H) : Fin (3 * ell) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun e ↦ (L.length e).val)

@[simp]
theorem CubicKernelLengthProfile.toFinsupp_apply
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile k ell H) (e : Fin (3 * ell)) :
    L.toFinsupp e = (L.length e).val :=
  rfl

private theorem CubicKernelLengthProfile.toFinsupp_mem_antidiagonal
    {d ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile (2 * ell + d) ell H) :
    L.toFinsupp ∈ (Finset.univ.finsuppAntidiag d :
      Finset (Fin (3 * ell) →₀ ℕ)) := by
  rw [Finset.mem_finsuppAntidiag]
  constructor
  · have hsum : ∑ e, (L.length e).val = d := by
      have htotal := L.totalLength
      omega
    calc
      Finset.univ.sum ⇑L.toFinsupp =
          ∑ e : Fin (3 * ell), (L.length e).val := by
        apply Finset.sum_congr rfl
        intro e _
        exact CubicKernelLengthProfile.toFinsupp_apply L e
      _ = d := hsum
  · exact Finset.subset_univ _

private theorem CubicKernelLengthProfile.toFinsupp_admissible
    {d ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (L : CubicKernelLengthProfile (2 * ell + d) ell H) :
    CubicKernelLengthAssignment.IsAdmissible H L.toFinsupp := by
  constructor
  · intro e he
    simpa only [CubicKernelLengthProfile.toFinsupp_apply] using
      L.loopLength e he
  · intro e f hef
    let e' : {a : Fin (3 * ell) // (L.length a).val = 0} :=
      ⟨e.1, by simpa only [CubicKernelLengthProfile.toFinsupp_apply] using e.2⟩
    let f' : {a : Fin (3 * ell) // (L.length a).val = 0} :=
      ⟨f.1, by simpa only [CubicKernelLengthProfile.toFinsupp_apply] using f.2⟩
    have hef' : H.endpoints e'.1 = H.endpoints f'.1 := by
      simpa only [e', f'] using hef
    have heq := L.directEndpointsInjective hef'
    exact Subtype.ext (congrArg Subtype.val heq)

/-- An admissible profile on `2 * ell + d` vertices is exactly an admissible
edge-length assignment of total internal length `d`. -/
def cubicKernelLengthProfileEquivAdmissibleAntidiagonal
    (d ell : ℕ) (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)) :
    CubicKernelLengthProfile (2 * ell + d) ell H ≃
      CubicKernelAdmissibleLengthAntidiagonal d ell H where
  toFun L :=
    ⟨⟨L.toFinsupp, L.toFinsupp_mem_antidiagonal⟩,
      L.toFinsupp_admissible⟩
  invFun A := by
    let l : Fin (3 * ell) →₀ ℕ := A.1.1
    have hsum : ∑ e, l e = d :=
      (Finset.mem_finsuppAntidiag.mp A.1.2).1
    have hle (e : Fin (3 * ell)) : l e ≤ d := by
      rw [← hsum]
      exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le (l i))
        (Finset.mem_univ e)
    exact
      { length := fun e ↦
          ⟨l e, lt_of_le_of_lt (hle e)
            (Nat.lt_succ_of_le (Nat.le_add_left d (2 * ell)))⟩
        totalLength := by
          simpa only using congrArg (fun n ↦ 2 * ell + n) hsum
        loopLength := by
          intro e he
          exact A.2.1 e he
        directEndpointsInjective := by
          exact A.2.2 }
  left_inv L := by
    cases L with
    | mk length totalLength loopLength directEndpointsInjective =>
        congr 1
  right_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.ext
    intro e
    rfl

/-- Generic finite regrouping along the preceding equivalence. -/
theorem sum_cubicKernelLengthProfile_eq_admissibleAntidiagonal
    {R : Type*} [AddCommMonoid R]
    {d ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (F : (Fin (3 * ell) →₀ ℕ) → R) :
    letI := cubicKernelLengthProfileFintype
      (2 * ell + d) ell K.graph
    (∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
        F L.toFinsupp) =
      ∑ A : CubicKernelAdmissibleLengthAntidiagonal d ell K.graph,
        F A.1.1 := by
  classical
  let _ : Fintype
      (CubicKernelLengthProfile (2 * ell + d) ell K.graph) :=
    cubicKernelLengthProfileFintype (2 * ell + d) ell K.graph
  exact Fintype.sum_equiv
    (cubicKernelLengthProfileEquivAdmissibleAntidiagonal d ell K.graph)
    (fun L : CubicKernelLengthProfile (2 * ell + d) ell K.graph ↦
      F L.toFinsupp)
    (fun A : CubicKernelAdmissibleLengthAntidiagonal d ell K.graph ↦
      F A.1.1)
    (fun _ ↦ rfl)

/-! ## One-edge series and the unrestricted finite product -/

/-- The degree-`n` coefficient carried by one oriented kernel edge for a
complex internal-vertex profile `tau`. -/
def profilePathEdgeCoefficient (M : CompactBJRModel S)
    (tau : C(S, ℂ)) (a b : S) (n : ℕ) : ℂ :=
  (((MPR.pathOperatorParameterCLM M tau) ^ n)
    (M.kernel.complexColumns b)) a

/-- The whole continuous endpoint kernel underlying the degree-`n`
one-edge coefficient.  Keeping this Banach-valued form makes summation
commute with later branch-coordinate pullback and integration. -/
def profilePathEdgeCoefficientKernel (M : CompactBJRModel S)
    (tau : C(S, ℂ)) (n : ℕ) : C(S × S, ℂ) :=
  MPR.operatorKernelize M ((MPR.pathOperatorParameterCLM M tau) ^ n)

@[simp] theorem profilePathEdgeCoefficientKernel_apply
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (n : ℕ) (a b : S) :
    profilePathEdgeCoefficientKernel M tau n (a, b) =
      profilePathEdgeCoefficient M tau a b n :=
  rfl

/-- Formal generating series of the preceding one-edge coefficients. -/
def profilePathEdgeSeries (M : CompactBJRModel S)
    (tau : C(S, ℂ)) (a b : S) : PowerSeries ℂ :=
  PowerSeries.mk (profilePathEdgeCoefficient M tau a b)

@[simp]
theorem profilePathEdgeSeries_coeff (M : CompactBJRModel S)
    (tau : C(S, ℂ)) (a b : S) (n : ℕ) :
    PowerSeries.coeff n (profilePathEdgeSeries M tau a b) =
      profilePathEdgeCoefficient M tau a b n := by
  simp [profilePathEdgeSeries]

/-- Product of the one-edge formal series for a fixed labelled cubic kernel
and fixed branch coordinates.  The canonical endpoint order is auxiliary;
it is fixed once and for all by the labelled kernel. -/
def cubicKernelPathProductSeries (M : CompactBJRModel S)
    (tau : C(S, ℂ)) {ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) : PowerSeries ℂ :=
  ∏ e : Fin (3 * ell),
    profilePathEdgeSeries M tau
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2)

/-- Exact coefficient formula for the unrestricted fixed-kernel product.
The right side is finite and ranges over all length assignments of total
internal length `d`. -/
theorem cubicKernelPathProductSeries_coeff
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) (d : ℕ) :
    PowerSeries.coeff d (cubicKernelPathProductSeries M tau K x) =
      ∑ l ∈ (Finset.univ.finsuppAntidiag d :
          Finset (Fin (3 * ell) →₀ ℕ)),
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M tau
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (l e) := by
  classical
  unfold cubicKernelPathProductSeries
  simpa only [profilePathEdgeSeries_coeff] using
    (PowerSeries.coeff_prod
      (fun e : Fin (3 * ell) ↦
        profilePathEdgeSeries M tau
          (x (cubicKernelOrderedEndpoints K.graph e).1)
          (x (cubicKernelOrderedEndpoints K.graph e).2))
      d Finset.univ)

/-- The admissible part of the preceding coefficient, expressed directly
with the existing cubic length-profile type. -/
def cubicKernelAdmissiblePathCoefficient
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) (d : ℕ) : ℂ :=
  letI := cubicKernelLengthProfileFintype
    (2 * ell + d) ell K.graph
  ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
    ∏ e : Fin (3 * ell),
      profilePathEdgeCoefficient M tau
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) (L.length e).val

/-- The admissible fixed-kernel coefficient is precisely the admissible part
of the finite antidiagonal in `cubicKernelPathProductSeries_coeff`. -/
theorem cubicKernelAdmissiblePathCoefficient_eq_antidiagonal
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S) (d : ℕ) :
    cubicKernelAdmissiblePathCoefficient M tau K x d =
      ∑ A : CubicKernelAdmissibleLengthAntidiagonal d ell K.graph,
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M tau
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (A.1.1 e) := by
  classical
  unfold cubicKernelAdmissiblePathCoefficient
  simpa only [CubicKernelLengthProfile.toFinsupp_apply] using
    (sum_cubicKernelLengthProfile_eq_admissibleAntidiagonal
      (K := K)
      (F := fun l ↦
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M tau
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)))

/-! ## Evaluation on the strict subcritical ball -/

/-- Generic profile-resolvent kernel, before specializing the profile to the
actual joint fold chart. -/
def profilePathResolventKernel (M : CompactBJRModel S)
    (tau : C(S, ℂ)) : C(S × S, ℂ) :=
  MPR.operatorKernelize M
    (Ring.inverse (1 - MPR.pathOperatorParameterCLM M tau))

/-- On a strict subcritical profile ball, summing the formal one-edge
coefficients gives the genuine operator resolvent kernel. -/
theorem summable_profilePathEdgeCoefficientKernel
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖tau x‖ ≤ q) :
    Summable (profilePathEdgeCoefficientKernel M tau) := by
  let L : PathEnd S := MPR.pathOperatorParameterCLM M tau
  have hs : Summable (fun n : ℕ ↦ L ^ n) :=
    JS.profilePathOperator_pow_summable M hM tau q hq hq1 ha
  change Summable (fun n : ℕ ↦ MPR.operatorKernelize M (L ^ n))
  refine (hs.map (MPR.operatorKernelize M)
    (MPR.operatorKernelize M).continuous).congr ?_
  intro n
  rfl

theorem summable_profilePathEdgeCoefficient
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖tau x‖ ≤ q) (a b : S) :
    Summable (fun n : ℕ ↦ profilePathEdgeCoefficient M tau a b n) := by
  let L : PathEnd S := MPR.pathOperatorParameterCLM M tau
  have hs : Summable (fun n : ℕ ↦ L ^ n) :=
    JS.profilePathOperator_pow_summable M hM tau q hq hq1 ha
  have hks : Summable (fun n : ℕ ↦ MPR.operatorKernelize M (L ^ n)) :=
    hs.map (MPR.operatorKernelize M) (MPR.operatorKernelize M).continuous
  simpa only [profilePathEdgeCoefficient, L, MPR.operatorKernelize_apply] using
    (ContinuousMap.summable_apply hks (a, b))

theorem tsum_profilePathEdgeCoefficient_eq_profilePathResolventKernel
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (tau : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖tau x‖ ≤ q) (a b : S) :
    (∑' n : ℕ, profilePathEdgeCoefficient M tau a b n) =
      profilePathResolventKernel M tau (a, b) := by
  let L : PathEnd S := MPR.pathOperatorParameterCLM M tau
  have hs : Summable (fun n : ℕ ↦ L ^ n) :=
    JS.profilePathOperator_pow_summable M hM tau q hq hq1 ha
  have hks : Summable (fun n : ℕ ↦ MPR.operatorKernelize M (L ^ n)) :=
    hs.map (MPR.operatorKernelize M) (MPR.operatorKernelize M).continuous
  calc
    (∑' n : ℕ, profilePathEdgeCoefficient M tau a b n) =
        (∑' n : ℕ, MPR.operatorKernelize M (L ^ n)) (a, b) := by
      rw [← ContinuousMap.tsum_apply hks]
      rfl
    _ = MPR.operatorKernelize M (∑' n : ℕ, L ^ n) (a, b) := by
      rw [(MPR.operatorKernelize M).map_tsum hs]
    _ = profilePathResolventKernel M tau (a, b) := by
      rw [JS.profilePathOperator_tsum_eq_inverse M hM tau q hq hq1 ha]
      rfl

/-- Specialization of the generic identity to the actual joint fold profile
and the path-resolvent kernel already used by the singular analysis. -/
theorem tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (p : C(S, ℂ) × ℂ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖MPR.profile M hM p x‖ ≤ q) (a b : S) :
    (∑' n : ℕ,
        profilePathEdgeCoefficient M (MPR.profile M hM p) a b n) =
      MPR.pathResolventKernel M hM p (a, b) := by
  simpa only [profilePathResolventKernel,
    MarkedPathResolvent.pathResolventKernel,
    MarkedPathResolvent.pathOperator] using
    (tsum_profilePathEdgeCoefficient_eq_profilePathResolventKernel
      M hM (MPR.profile M hM p) q hq hq1 ha a b)

/-- Consequently the product over the labelled edges of one cubic kernel is
the literal finite product of the marked-path resolvent kernels. -/
theorem prod_tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (x : Fin (2 * ell) → S)
    (p : C(S, ℂ) × ℂ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ y, ‖MPR.profile M hM p y‖ ≤ q) :
    (∏ e : Fin (3 * ell),
        ∑' n : ℕ,
          profilePathEdgeCoefficient M (MPR.profile M hM p)
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) n) =
      ∏ e : Fin (3 * ell),
        MPR.pathResolventKernel M hM p
          (x (cubicKernelOrderedEndpoints K.graph e).1,
            x (cubicKernelOrderedEndpoints K.graph e).2) := by
  apply Finset.prod_congr rfl
  intro e _
  exact tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
    M hM p q hq hq1 ha _ _

end PerronWright.GraphCore
