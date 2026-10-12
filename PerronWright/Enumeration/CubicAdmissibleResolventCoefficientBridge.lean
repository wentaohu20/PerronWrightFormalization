import PerronWright.Enumeration.CubicActualAdmissibleCoefficientBridge
import PerronWright.Enumeration.CubicForbiddenCorrectionBridge
import PerronWright.Enumeration.CubicProfileCoefficientBounds

/-!
# From exact cubic coefficients to the literal admissible resolvent

On a strict-subcritical profile ball, the finite-degree admissible profile
coefficients form an absolutely summable series in the Banach algebra of
continuous branch-coordinate functions.  Reindexing all edge-length tables
by their total length identifies that series with the literal admissible
assignment `tsum` from `CubicForbiddenCorrectionBridge`.  Since integration
is a continuous linear functional, the identity survives integration.
-/

open MeasureTheory PerronWright
open scoped Classical BigOperators Topology

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem sum_dite_eq_sum_subtype
    {A R : Type*} [Fintype A] [DecidableEq A] [AddCommMonoid R]
    (p : A → Prop) [DecidablePred p] (f : ∀ a, p a → R) :
    (∑ a : A, if h : p a then f a h else 0) =
      ∑ a : {a // p a}, f a.1 a.2 := by
  classical
  let F : A → R := fun a ↦ if h : p a then f a h else 0
  calc
    (∑ a : A, if h : p a then f a h else 0) = ∑ a : A, F a := rfl
    _ = ∑ a ∈ (Finset.univ.filter p), F a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : p a <;> simp [F, ha]
    _ = ∑ a : {a // p a}, F a.1 := by
      exact Finset.sum_subtype (Finset.univ.filter p) (by simp) F
    _ = ∑ a : {a // p a}, f a.1 a.2 := by
      apply Fintype.sum_congr
      intro a
      simp [F, a.2]

/-- Every finite table of natural lengths belongs to the unique finite
antidiagonal indexed by its total length. -/
private def finFunctionEquivSigmaFinsuppAntidiagonal (n : ℕ) :
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
    change Finsupp.equivFunOnFinite.symm
        (Finsupp.equivFunOnFinite f) = f
    exact Equiv.symm_apply_apply Finsupp.equivFunOnFinite f

/-- One literal admissible length table, as a continuous function of all
branch coordinates. -/
def cubicKernelAdmissibleAssignmentFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (l : Fin (3 * ell) → ℕ) :
    C((Fin (2 * ell) → S), ℂ) :=
  if CubicKernelLengthAssignment.IsAdmissible K.graph
      (Finsupp.equivFunOnFinite.symm l) then
    cubicKernelBranchProfileFunction M hM (ell := ell) q *
      ∏ e : Fin (3 * ell),
        cubicFixedLengthEdgeFunction M hM K e (l e) q
  else 0

@[simp] theorem cubicKernelAdmissibleAssignmentFunction_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (l : Fin (3 * ell) → ℕ)
    (x : Fin (2 * ell) → S) :
    cubicKernelAdmissibleAssignmentFunction M hM K q l x =
      if CubicKernelLengthAssignment.IsAdmissible K.graph
          (Finsupp.equivFunOnFinite.symm l) then
        cubicKernelBranchProfileFunction M hM (ell := ell) q x *
          ∏ e : Fin (3 * ell),
            profilePathEdgeCoefficient M (MPR.profile M hM q)
              (x (cubicKernelOrderedEndpoints K.graph e).1)
              (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
      else 0 := by
  classical
  by_cases hl : CubicKernelLengthAssignment.IsAdmissible K.graph
      (Finsupp.equivFunOnFinite.symm l)
  · simp [cubicKernelAdmissibleAssignmentFunction, hl,
      ContinuousMap.prod_apply]
  · simp [cubicKernelAdmissibleAssignmentFunction, hl]

private theorem cubicFixedLengthEdgeFunction_norm_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    Summable (fun n : ℕ ↦
      ‖cubicFixedLengthEdgeFunction M hM K e n q‖) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_profilePathEdgeCoefficient_geometric_bound M hM
  have hgeom : Summable (fun n : ℕ ↦ B * r ^ n) :=
    (summable_geometric_of_lt_one hr hr1).mul_left B
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hgeom
  intro n
  apply (ContinuousMap.norm_le _
    (mul_nonneg hB (pow_nonneg hr n))).2
  intro x
  simpa only [cubicFixedLengthEdgeFunction_apply] using
    hbound (MPR.profile M hM q) r hr hprofile
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2) n

theorem cubicKernelAdmissibleAssignmentFunction_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    Summable (cubicKernelAdmissibleAssignmentFunction M hM K q) := by
  classical
  let A : Set (Fin (3 * ell) → ℕ) := {l |
    CubicKernelLengthAssignment.IsAdmissible K.graph
      (Finsupp.equivFunOnFinite.symm l)}
  let P : (Fin (3 * ell) → ℕ) →
      C((Fin (2 * ell) → S), ℂ) := fun l ↦
    ∏ e : Fin (3 * ell),
      cubicFixedLengthEdgeFunction M hM K e (l e) q
  have hP : Summable P := by
    simpa only [P] using
      (summable_norm_finFunction_prod_and_tsum
        (fun e n ↦ cubicFixedLengthEdgeFunction M hM K e n q)
        (fun e ↦ cubicFixedLengthEdgeFunction_norm_summable
          M hM K e q r hr hr1 hprofile)).1.of_norm
  have hA : Summable (A.indicator P) := hP.indicator A
  have hmul := hA.mul_left
    (cubicKernelBranchProfileFunction M hM (ell := ell) q)
  exact hmul.congr (fun l ↦ by
    by_cases hl : CubicKernelLengthAssignment.IsAdmissible K.graph
        (Finsupp.equivFunOnFinite.symm l)
    · simp [cubicKernelAdmissibleAssignmentFunction, A, P, hl]
    · simp [cubicKernelAdmissibleAssignmentFunction, A, P, hl])

/-- The finite total-length `d` block as one continuous branch-coordinate
function. -/
def cubicKernelAdmissibleDegreeFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (d : ℕ) :
    C((Fin (2 * ell) → S), ℂ) :=
  letI := cubicKernelLengthProfileFintype
    (2 * ell + d) ell K.graph
  ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
    cubicKernelBranchProfileFunction M hM (ell := ell) q *
      ∏ e : Fin (3 * ell),
        cubicFixedLengthEdgeFunction M hM K e (L.length e).val q

@[simp] theorem cubicKernelAdmissibleDegreeFunction_apply
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (d : ℕ)
    (x : Fin (2 * ell) → S) :
    cubicKernelAdmissibleDegreeFunction M hM K q d x =
      cubicKernelBranchProfileFunction M hM (ell := ell) q x *
        cubicKernelAdmissiblePathCoefficient M (MPR.profile M hM q)
          K x d := by
  classical
  unfold cubicKernelAdmissibleDegreeFunction
    cubicKernelAdmissiblePathCoefficient
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.prod_apply, cubicFixedLengthEdgeFunction_apply,
    Finset.mul_sum]

private theorem cubicKernelAdmissibleAssignment_sigma_block
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (d : ℕ) :
    (∑ A : (Finset.univ.finsuppAntidiag d :
          Finset (Fin (3 * ell) →₀ ℕ)),
        cubicKernelAdmissibleAssignmentFunction M hM K q
          (Finsupp.equivFunOnFinite A.1)) =
      cubicKernelAdmissibleDegreeFunction M hM K q d := by
  classical
  let p : ↥(Finset.univ.finsuppAntidiag d :
      Finset (Fin (3 * ell) →₀ ℕ)) → Prop := fun A ↦
    CubicKernelLengthAssignment.IsAdmissible K.graph A.1
  rw [show (∑ A : (Finset.univ.finsuppAntidiag d :
      Finset (Fin (3 * ell) →₀ ℕ)),
      cubicKernelAdmissibleAssignmentFunction M hM K q
        (Finsupp.equivFunOnFinite A.1)) =
      ∑ A, if h : p A then
        cubicKernelBranchProfileFunction M hM (ell := ell) q *
          ∏ e : Fin (3 * ell),
            cubicFixedLengthEdgeFunction M hM K e (A.1 e) q
        else 0 by
      apply Fintype.sum_congr
      intro A
      by_cases hA : CubicKernelLengthAssignment.IsAdmissible K.graph A.1
      · simp [cubicKernelAdmissibleAssignmentFunction, p, hA]
      · simp [cubicKernelAdmissibleAssignmentFunction, p, hA]]
  rw [sum_dite_eq_sum_subtype p]
  unfold cubicKernelAdmissibleDegreeFunction
  simpa only [CubicKernelLengthProfile.toFinsupp_apply] using
    (sum_cubicKernelLengthProfile_eq_admissibleAntidiagonal
      (d := d) K
      (fun l ↦
        cubicKernelBranchProfileFunction M hM (ell := ell) q *
          ∏ e : Fin (3 * ell),
            cubicFixedLengthEdgeFunction M hM K e (l e) q)).symm

/-- Reindexing by total length is an equality of absolutely convergent
continuous-function series. -/
theorem tsum_cubicKernelAdmissibleDegreeFunction_eq_assignment
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    (∑' d : ℕ, cubicKernelAdmissibleDegreeFunction M hM K q d) =
      ∑' l : Fin (3 * ell) → ℕ,
        cubicKernelAdmissibleAssignmentFunction M hM K q l := by
  classical
  let e := finFunctionEquivSigmaFinsuppAntidiagonal (3 * ell)
  let F := cubicKernelAdmissibleAssignmentFunction M hM K q
  have hF : Summable F :=
    cubicKernelAdmissibleAssignmentFunction_summable
      M hM K q r hr hr1 hprofile
  have hSigma : Summable (fun Q : Σ d : ℕ,
      (Finset.univ.finsuppAntidiag d : Finset (Fin (3 * ell) →₀ ℕ)) ↦
      F (e.symm Q)) := hF.comp_injective e.symm.injective
  calc
    (∑' d : ℕ, cubicKernelAdmissibleDegreeFunction M hM K q d) =
        ∑' d : ℕ,
          ∑' A : (Finset.univ.finsuppAntidiag d :
            Finset (Fin (3 * ell) →₀ ℕ)), F (e.symm ⟨d, A⟩) := by
      apply tsum_congr
      intro d
      rw [tsum_fintype]
      change cubicKernelAdmissibleDegreeFunction M hM K q d =
        ∑ A : (Finset.univ.finsuppAntidiag d :
            Finset (Fin (3 * ell) →₀ ℕ)),
          cubicKernelAdmissibleAssignmentFunction M hM K q
            (Finsupp.equivFunOnFinite A.1)
      exact (cubicKernelAdmissibleAssignment_sigma_block M hM K q d).symm
    _ = ∑' Q : Σ d : ℕ,
          (Finset.univ.finsuppAntidiag d :
            Finset (Fin (3 * ell) →₀ ℕ)), F (e.symm Q) := by
      exact hSigma.tsum_sigma.symm
    _ = ∑' l : Fin (3 * ell) → ℕ, F l := by
      exact e.symm.tsum_eq F

/-- The `d`-th integrated degree block is the finite sum of the exact
length-profile integrals. -/
theorem cubicKernelIntegral_admissibleDegreeFunction
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (d : ℕ) :
    cubicKernelIntegralCLM M ell
        (cubicKernelAdmissibleDegreeFunction M hM K q d) =
      letI := cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
      ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
        cubicLengthProfileComplexKernelIntegral M (MPR.profile M hM q) K L := by
  classical
  let _ := cubicKernelLengthProfileFintype
    (2 * ell + d) ell K.graph
  unfold cubicKernelAdmissibleDegreeFunction
  rw [map_sum]
  apply Fintype.sum_congr
  intro L
  rw [cubicKernelIntegralCLM_apply]
  unfold cubicLengthProfileComplexKernelIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ContinuousMap.mul_apply, ContinuousMap.prod_apply,
    cubicKernelBranchProfileFunction_apply,
    cubicFixedLengthEdgeFunction_apply]
  rfl

/-- Fixed kernel: summing all exact finite-degree profile integrals gives
the integral of the literal admissible assignment `tsum`. -/
theorem tsum_cubicLengthProfileIntegral_eq_literalAdmissibleIntegral
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    (∑' d : ℕ,
      letI := cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
      ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
        cubicLengthProfileComplexKernelIntegral M (MPR.profile M hM q) K L) =
      ∫ x : Fin (2 * ell) → S,
        cubicKernelLiteralAdmissibleAssignmentIntegrand M hM K q x
          ∂cubicKernelProductMeasure M ell := by
  have hF := cubicKernelAdmissibleAssignmentFunction_summable
    M hM K q r hr hr1 hprofile
  have hD : Summable
      (cubicKernelAdmissibleDegreeFunction M hM K q) := by
    let e := finFunctionEquivSigmaFinsuppAntidiagonal (3 * ell)
    let F := cubicKernelAdmissibleAssignmentFunction M hM K q
    have hSigma : Summable (fun Q : Σ d : ℕ,
        (Finset.univ.finsuppAntidiag d : Finset (Fin (3 * ell) →₀ ℕ)) ↦
        F (e.symm Q)) := hF.comp_injective e.symm.injective
    have houter := hSigma.sigma
    exact houter.congr (fun d ↦ by
      rw [tsum_fintype]
      change (∑ A : (Finset.univ.finsuppAntidiag d :
            Finset (Fin (3 * ell) →₀ ℕ)),
          cubicKernelAdmissibleAssignmentFunction M hM K q
            (Finsupp.equivFunOnFinite A.1)) =
        cubicKernelAdmissibleDegreeFunction M hM K q d
      exact cubicKernelAdmissibleAssignment_sigma_block M hM K q d)
  calc
    (∑' d : ℕ,
      letI := cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
      ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
        cubicLengthProfileComplexKernelIntegral M (MPR.profile M hM q) K L) =
        ∑' d : ℕ, cubicKernelIntegralCLM M ell
          (cubicKernelAdmissibleDegreeFunction M hM K q d) := by
      apply tsum_congr
      intro d
      exact (cubicKernelIntegral_admissibleDegreeFunction
        M hM K q d).symm
    _ = cubicKernelIntegralCLM M ell
          (∑' d : ℕ, cubicKernelAdmissibleDegreeFunction M hM K q d) := by
      exact ((cubicKernelIntegralCLM M ell).map_tsum hD).symm
    _ = cubicKernelIntegralCLM M ell
          (∑' l : Fin (3 * ell) → ℕ,
            cubicKernelAdmissibleAssignmentFunction M hM K q l) := by
      rw [tsum_cubicKernelAdmissibleDegreeFunction_eq_assignment
        M hM K q r hr hr1 hprofile]
    _ = ∫ x : Fin (2 * ell) → S,
        cubicKernelLiteralAdmissibleAssignmentIntegrand M hM K q x
          ∂cubicKernelProductMeasure M ell := by
      rw [cubicKernelIntegralCLM_apply]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← ContinuousMap.tsum_apply hF]
      unfold cubicKernelLiteralAdmissibleAssignmentIntegrand
      simp_rw [cubicKernelAdmissibleAssignmentFunction_apply]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro l
      by_cases hl : CubicKernelLengthAssignment.IsAdmissible K.graph
          (Finsupp.equivFunOnFinite.symm l) <;> simp [hl]

/-- After the finite labelled-kernel sum, the full exact finite-degree
profile series is the literal admissible resolvent sum. -/
theorem tsum_positiveSurplusCubicAdmissibleProfileCoefficient_eq_literal
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    (∑' d : ℕ,
        positiveSurplusCubicAdmissibleProfileCoefficient M
          (MPR.profile M hM q) ell d) =
      positiveSurplusCubicLiteralAdmissibleResolventSum M hM ell q := by
  let _ := labelledConnectedCubicKernelFintype ell
  let f : LabelledConnectedCubicKernel ell → ℕ → ℂ := fun K d ↦
    labelledCubicKernelInverseMultiplicity K *
      letI := cubicKernelLengthProfileFintype
        (2 * ell + d) ell K.graph
      ∑ L : CubicKernelLengthProfile (2 * ell + d) ell K.graph,
        cubicLengthProfileComplexKernelIntegral M (MPR.profile M hM q) K L
  have hf (K : LabelledConnectedCubicKernel ell) : Summable (f K) := by
    have hAssign := cubicKernelAdmissibleAssignmentFunction_summable
      M hM K q r hr hr1 hprofile
    have hD : Summable
        (cubicKernelAdmissibleDegreeFunction M hM K q) := by
      let e := finFunctionEquivSigmaFinsuppAntidiagonal (3 * ell)
      let F := cubicKernelAdmissibleAssignmentFunction M hM K q
      have hSigma : Summable (fun Q : Σ d : ℕ,
          (Finset.univ.finsuppAntidiag d :
            Finset (Fin (3 * ell) →₀ ℕ)) ↦ F (e.symm Q)) :=
        hAssign.comp_injective e.symm.injective
      exact hSigma.sigma.congr (fun d ↦ by
        rw [tsum_fintype]
        change (∑ A : (Finset.univ.finsuppAntidiag d :
              Finset (Fin (3 * ell) →₀ ℕ)),
            cubicKernelAdmissibleAssignmentFunction M hM K q
              (Finsupp.equivFunOnFinite A.1)) =
          cubicKernelAdmissibleDegreeFunction M hM K q d
        exact cubicKernelAdmissibleAssignment_sigma_block M hM K q d)
    have hInt : Summable (fun d ↦
        cubicKernelIntegralCLM M ell
          (cubicKernelAdmissibleDegreeFunction M hM K q d)) :=
      hD.map (cubicKernelIntegralCLM M ell)
        (cubicKernelIntegralCLM M ell).continuous
    exact (hInt.congr (fun d ↦
      (cubicKernelIntegral_admissibleDegreeFunction M hM K q d))).mul_left _
  unfold positiveSurplusCubicAdmissibleProfileCoefficient
    positiveSurplusCubicLiteralAdmissibleResolventSum
  rw [Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun K d ↦ f K d) (fun K _ ↦ hf K)]
  apply Finset.sum_congr rfl
  intro K _
  rw [tsum_mul_left]
  apply congrArg (fun z : ℂ ↦ labelledCubicKernelInverseMultiplicity K * z)
  exact tsum_cubicLengthProfileIntegral_eq_literalAdmissibleIntegral
    M hM K q r hr hr1 hprofile

/-- Therefore the inclusion--exclusion admissible resolvent used by the
analytic fold construction is the sum of the genuine exact finite-degree
cubic profile coefficients on every strict-subcritical profile ball. -/
theorem tsum_positiveSurplusCubicAdmissibleProfileCoefficient_eq_resolvent
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    (∑' d : ℕ,
        positiveSurplusCubicAdmissibleProfileCoefficient M
          (MPR.profile M hM q) ell d) =
      positiveSurplusCubicAdmissibleResolventSum M hM ell q := by
  rw [tsum_positiveSurplusCubicAdmissibleProfileCoefficient_eq_literal
    M hM ell q r hr hr1 hprofile]
  exact (positiveSurplusCubicAdmissibleResolventSum_eq_literal
    M hM ell q r hr hr1 hprofile).symm

/-- On the strict-subcritical profile ball, the genuine cubic part of the
fixed-surplus composition series sums directly to the admissible resolvent
constructed by inclusion--exclusion. -/
theorem tsum_cubicFixedSurplusProfileCompositionCoeff_X_mul_C_eq_resolvent
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (hell : 0 < ell) (s₀ : S)
    (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    (∑' d : ℕ,
        cubicFixedSurplusProfileCompositionCoeff M
          (PowerSeries.X * PowerSeries.C (MPR.profile M hM q))
          ell (2 * ell + d)) =
      positiveSurplusCubicAdmissibleResolventSum M hM ell q := by
  calc
    (∑' d : ℕ,
        cubicFixedSurplusProfileCompositionCoeff M
          (PowerSeries.X * PowerSeries.C (MPR.profile M hM q))
          ell (2 * ell + d)) =
        ∑' d : ℕ,
          positiveSurplusCubicAdmissibleProfileCoefficient M
            (MPR.profile M hM q) ell d := by
      apply tsum_congr
      intro d
      exact cubicFixedSurplusProfileCompositionCoeff_X_mul_C_eq_admissibleProfile
        M (MPR.profile M hM q) hell s₀
    _ = positiveSurplusCubicAdmissibleResolventSum M hM ell q :=
      tsum_positiveSurplusCubicAdmissibleProfileCoefficient_eq_resolvent
        M hM ell q r hr hr1 hprofile

end PerronWright.GraphCore
