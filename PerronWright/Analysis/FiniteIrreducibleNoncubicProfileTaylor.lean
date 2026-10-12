import PerronWright.Analysis.FiniteIrreducibleNoncubicProfileChartBridge
import PerronWright.Enumeration.PositiveSurplusNoncubicProfileTaylor

/-! Exact genuine size coefficients and full Taylor series of the finite
noncubic profile functional. Pure fixed-size subdivision/composition
coefficients are reused through the literal data-only BJR model; all
absolute convergence, geometric majorants and analytic tail orders are
proved for the actual finite critical operator. -/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators
noncomputable section
namespace PerronWright.FiniteIrreducibleKernelAmplitude
open GraphCore
variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## Exact all-size reindexing -/

private def noncubicProfileFinFunctionEquivSigmaAntidiagonal (n : ℕ) :
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

private def boundedKernelAdmissibleInternalDegreeFunction
    (M : FiniteIrreducibleModel S) {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (d : ℕ) :
    C((Fin K.shape.1.val → S), ℂ) :=
  ∑ A : BoundedKernelAdmissibleLengthAntidiagonal d K,
    boundedKernelAdmissibleProfileAssignmentFunction M K tau
      (Finsupp.equivFunOnFinite A.1.1)

private theorem boundedKernelAdmissibleAssignment_sigma_block
    (M : FiniteIrreducibleModel S) {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (d : ℕ) :
    (∑ A : (Finset.univ.finsuppAntidiag d :
        Finset (Fin K.shape.2.1.val →₀ ℕ)),
      boundedKernelAdmissibleProfileAssignmentFunction M K tau
        (Finsupp.equivFunOnFinite A.1)) =
      boundedKernelAdmissibleInternalDegreeFunction M K tau d := by
  classical
  let p : ↥(Finset.univ.finsuppAntidiag d :
      Finset (Fin K.shape.2.1.val →₀ ℕ)) → Prop := fun A ↦
    BoundedKernelLengthAssignment.IsAdmissible K A.1
  rw [show (∑ A : (Finset.univ.finsuppAntidiag d :
      Finset (Fin K.shape.2.1.val →₀ ℕ)),
      boundedKernelAdmissibleProfileAssignmentFunction M K tau
        (Finsupp.equivFunOnFinite A.1)) =
      ∑ A, if _h : p A then
        boundedKernelAdmissibleProfileAssignmentFunction M K tau
          (Finsupp.equivFunOnFinite A.1) else 0 by
      apply Fintype.sum_congr
      intro A
      by_cases hA : BoundedKernelLengthAssignment.IsAdmissible K A.1
      · simp [p, hA]
      · simp [p, hA,
          boundedKernelAdmissibleProfileAssignmentFunction]]
  rw [PerronWright.FieldRootedTree.sum_dite_eq_sum_subtype p]
  unfold boundedKernelAdmissibleInternalDegreeFunction
  rfl

private theorem
    tsum_boundedKernelAdmissibleInternalDegreeFunction_eq_assignment
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    (∑' d : ℕ,
      boundedKernelAdmissibleInternalDegreeFunction M K tau d) =
      ∑' l : Fin K.shape.2.1.val → ℕ,
        boundedKernelAdmissibleProfileAssignmentFunction M K tau l := by
  classical
  let e := noncubicProfileFinFunctionEquivSigmaAntidiagonal
    K.shape.2.1.val
  let F := boundedKernelAdmissibleProfileAssignmentFunction M K tau
  have hF : Summable F :=
    boundedKernelAdmissibleProfileAssignmentFunction_summable
      M hM K tau r hr hr1 htau
  have hSigma : Summable (fun Q : Σ d : ℕ,
      (Finset.univ.finsuppAntidiag d :
        Finset (Fin K.shape.2.1.val →₀ ℕ)) ↦ F (e.symm Q)) :=
    hF.comp_injective e.symm.injective
  calc
    (∑' d : ℕ,
      boundedKernelAdmissibleInternalDegreeFunction M K tau d) =
        ∑' d : ℕ,
          ∑' A : (Finset.univ.finsuppAntidiag d :
            Finset (Fin K.shape.2.1.val →₀ ℕ)), F (e.symm ⟨d, A⟩) := by
      apply tsum_congr
      intro d
      rw [tsum_fintype]
      change boundedKernelAdmissibleInternalDegreeFunction M K tau d =
        ∑ A : (Finset.univ.finsuppAntidiag d :
          Finset (Fin K.shape.2.1.val →₀ ℕ)),
          boundedKernelAdmissibleProfileAssignmentFunction M K tau
            (Finsupp.equivFunOnFinite A.1)
      exact (boundedKernelAdmissibleAssignment_sigma_block M K tau d).symm
    _ = ∑' Q : Σ d : ℕ,
          (Finset.univ.finsuppAntidiag d :
            Finset (Fin K.shape.2.1.val →₀ ℕ)), F (e.symm Q) := by
      exact hSigma.tsum_sigma.symm
    _ = ∑' l : Fin K.shape.2.1.val → ℕ, F l :=
      e.symm.tsum_eq F

private theorem boundedKernelBranchIntegral_internalDegreeFunction
    (M : FiniteIrreducibleModel S) {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ)) (d : ℕ) :
    boundedKernelBranchIntegralCLM M K
        (boundedKernelAdmissibleInternalDegreeFunction M K tau d) =
      letI := boundedKernelLengthProfileFintype
        (K.shape.1.val + d) K
      ∑ L : BoundedKernelLengthProfile (K.shape.1.val + d) K,
        boundedKernelLengthProfileIntegral M.bjrModel tau K L := by
  classical
  let _ := boundedKernelLengthProfileFintype
    (K.shape.1.val + d) K
  unfold boundedKernelAdmissibleInternalDegreeFunction
  rw [map_sum]
  exact Fintype.sum_equiv
    (boundedKernelLengthProfileEquivAdmissibleAntidiagonal d K).symm
    (fun A : BoundedKernelAdmissibleLengthAntidiagonal d K ↦
      boundedKernelBranchIntegralCLM M K
        (boundedKernelAdmissibleProfileAssignmentFunction M K tau
          (Finsupp.equivFunOnFinite A.1.1)))
    (fun L : BoundedKernelLengthProfile (K.shape.1.val + d) K ↦
      boundedKernelLengthProfileIntegral M.bjrModel tau K L)
    (fun A ↦ by
      let L := (boundedKernelLengthProfileEquivAdmissibleAntidiagonal
        d K).symm A
      rw [boundedKernelBranchIntegralCLM_apply]
      unfold boundedKernelLengthProfileIntegral
        boundedKernelProfileLengthIntegral boundedKernelLengthDatumOfProfile
      apply integral_congr_ae
      filter_upwards [] with x
      have hadm : BoundedKernelLengthAssignment.IsAdmissible K
          (Finsupp.equivFunOnFinite.symm
            (Finsupp.equivFunOnFinite A.1.1)) := by
        simpa only [Equiv.symm_apply_apply] using A.2
      simp only [boundedKernelAdmissibleProfileAssignmentFunction_apply,
        hadm, if_true]
      have hlength (e : Fin K.shape.2.1.val) :
          (L.length e).val = A.1.1 e := by
        rfl
      apply congrArg (fun z : ℂ ↦
        (∏ v : Fin K.shape.1.val, tau (x v)) * z)
      apply Finset.prod_congr rfl
      intro e _he
      rw [← boundedKernelOrderedEndpoints_mk K e,
        profilePathEdgeFactor_mk, hlength e]
      rfl)

private theorem boundedKernelInternalDegreeFunction_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    Summable (boundedKernelAdmissibleInternalDegreeFunction M K tau) := by
  let e := noncubicProfileFinFunctionEquivSigmaAntidiagonal
    K.shape.2.1.val
  let F := boundedKernelAdmissibleProfileAssignmentFunction M K tau
  have hF : Summable F :=
    boundedKernelAdmissibleProfileAssignmentFunction_summable
      M hM K tau r hr hr1 htau
  have hSigma : Summable (fun Q : Σ d : ℕ,
      (Finset.univ.finsuppAntidiag d :
        Finset (Fin K.shape.2.1.val →₀ ℕ)) ↦ F (e.symm Q)) :=
    hF.comp_injective e.symm.injective
  exact hSigma.sigma.congr (fun d ↦ by
    rw [tsum_fintype]
    change (∑ A : (Finset.univ.finsuppAntidiag d :
        Finset (Fin K.shape.2.1.val →₀ ℕ)),
      boundedKernelAdmissibleProfileAssignmentFunction M K tau
        (Finsupp.equivFunOnFinite A.1)) =
      boundedKernelAdmissibleInternalDegreeFunction M K tau d
    exact boundedKernelAdmissibleAssignment_sigma_block M K tau d)

private theorem connectedNoncubicKernelAdmissibleProfileFunctional_eq_tsum
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    connectedNoncubicKernelAdmissibleProfileFunctional M K tau =
      ∑' d : ℕ,
        letI := boundedKernelLengthProfileFintype
          (K.1.toLabelledBoundedKernel.shape.1.val + d)
          K.1.toLabelledBoundedKernel
        ∑ L : BoundedKernelLengthProfile
            (K.1.toLabelledBoundedKernel.shape.1.val + d)
            K.1.toLabelledBoundedKernel,
          boundedKernelLengthProfileIntegral M.bjrModel tau
            K.1.toLabelledBoundedKernel L := by
  let B := K.1.toLabelledBoundedKernel
  have hD : Summable
      (boundedKernelAdmissibleInternalDegreeFunction M B tau) :=
    boundedKernelInternalDegreeFunction_summable
      M hM B tau r hr hr1 htau
  have hfun :
      boundedKernelAdmissibleProfileIntegrandFunction M B tau =
        ∑' d : ℕ,
          boundedKernelAdmissibleInternalDegreeFunction M B tau d := by
    ext x
    rw [boundedKernelAdmissibleProfileIntegrandFunction_eq_literal
      M hM B tau x r hr hr1 htau]
    rw [tsum_boundedKernelAdmissibleInternalDegreeFunction_eq_assignment
      M hM B tau r hr hr1 htau]
    exact (tsum_boundedKernelAdmissibleProfileAssignmentFunction_apply
      M hM B tau x r hr hr1 htau).symm
  unfold connectedNoncubicKernelAdmissibleProfileFunctional
  rw [hfun, (boundedKernelBranchIntegralCLM M B).map_tsum hD]
  apply tsum_congr
  intro d
  exact boundedKernelBranchIntegral_internalDegreeFunction M B tau d

private def connectedNoncubicKernelAdmissibleProfileSizeCoefficient
    (M : FiniteIrreducibleModel S) (tau : C(S, ℂ))
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (k : ℕ) : ℂ :=
  letI := boundedKernelLengthProfileFintype k
    K.1.toLabelledBoundedKernel
  ∑ L : BoundedKernelLengthProfile k K.1.toLabelledBoundedKernel,
    boundedKernelLengthProfileIntegral M.bjrModel tau
      K.1.toLabelledBoundedKernel L

private theorem connectedNoncubicKernelSizeCoefficient_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    Summable (connectedNoncubicKernelAdmissibleProfileSizeCoefficient
      M tau K) := by
  let B := K.1.toLabelledBoundedKernel
  have hD : Summable
      (boundedKernelAdmissibleInternalDegreeFunction M B tau) :=
    boundedKernelInternalDegreeFunction_summable
      M hM B tau r hr hr1 htau
  have hInt : Summable (fun d ↦
      boundedKernelBranchIntegralCLM M B
        (boundedKernelAdmissibleInternalDegreeFunction M B tau d)) :=
    hD.map (boundedKernelBranchIntegralCLM M B)
      (boundedKernelBranchIntegralCLM M B).continuous
  have htail : Summable (fun d ↦
      connectedNoncubicKernelAdmissibleProfileSizeCoefficient
        M tau K (d + B.shape.1.val)) := by
    refine hInt.congr (fun d ↦ ?_)
    calc
      boundedKernelBranchIntegralCLM M B
          (boundedKernelAdmissibleInternalDegreeFunction M B tau d) =
          connectedNoncubicKernelAdmissibleProfileSizeCoefficient
            M tau K (B.shape.1.val + d) := by
        simpa only [connectedNoncubicKernelAdmissibleProfileSizeCoefficient] using
          (boundedKernelBranchIntegral_internalDegreeFunction M B tau d)
      _ = connectedNoncubicKernelAdmissibleProfileSizeCoefficient
            M tau K (d + B.shape.1.val) :=
        congrArg (connectedNoncubicKernelAdmissibleProfileSizeCoefficient
          M tau K) (Nat.add_comm B.shape.1.val d)
  exact (summable_nat_add_iff B.shape.1.val).mp htail

/-- The finite weighted away-chart functional is exactly the absolutely
convergent `tsum` of its literal genuine size coefficients. -/
theorem positiveSurplusNoncubicAdmissibleProfileFunctional_eq_tsum
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) (tau : C(S, ℂ))
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (htau : ∀ y, ‖tau y‖ ≤ r) :
    positiveSurplusNoncubicAdmissibleProfileFunctional M ell tau =
      ∑' k : ℕ,
        positiveSurplusNoncubicAdmissibleProfileCoefficient M.bjrModel tau ell k := by
  let _ := labelledConnectedNoncubicKernelFintype ell
  let _ (K : LabelledConnectedNoncubicKernel ell) (k : ℕ) :
      Fintype (BoundedKernelLengthProfile k
        K.1.toLabelledBoundedKernel) :=
    boundedKernelLengthProfileFintype k K.1.toLabelledBoundedKernel
  let W : LabelledConnectedNoncubicKernel ell → ℂ :=
    labelledConnectedNoncubicKernelInverseCoordinateMultiplicity
  let a : LabelledConnectedNoncubicKernel ell → ℕ → ℂ := fun K k ↦
    W K * connectedNoncubicKernelAdmissibleProfileSizeCoefficient
      M tau K k
  have ha (K : LabelledConnectedNoncubicKernel ell) : Summable (a K) :=
    (connectedNoncubicKernelSizeCoefficient_summable
      M hM K tau r hr hr1 htau).mul_left (W K)
  unfold positiveSurplusNoncubicAdmissibleProfileFunctional
    positiveSurplusNoncubicAdmissibleProfileCoefficient
  change (∑ K : LabelledConnectedNoncubicKernel ell,
      W K * connectedNoncubicKernelAdmissibleProfileFunctional M K tau) =
    ∑' k : ℕ, ∑ K : LabelledConnectedNoncubicKernel ell, a K k
  rw [Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun K k ↦ a K k) (fun K _ ↦ ha K)]
  apply Finset.sum_congr rfl
  intro K _
  rw [tsum_mul_left]
  apply congrArg (fun z : ℂ ↦ W K * z)
  rw [connectedNoncubicKernelAdmissibleProfileFunctional_eq_tsum
    M hM K tau r hr hr1 htau]
  have hsum :=
    (connectedNoncubicKernelSizeCoefficient_summable
      M hM K tau r hr hr1 htau).sum_add_tsum_nat_add
        K.1.toLabelledBoundedKernel.shape.1.val
  have hprefix :
      ∑ k ∈ Finset.range K.1.toLabelledBoundedKernel.shape.1.val,
        connectedNoncubicKernelAdmissibleProfileSizeCoefficient
          M tau K k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    unfold connectedNoncubicKernelAdmissibleProfileSizeCoefficient
    apply Fintype.sum_eq_zero
    intro L
    have htotal := L.totalLength
    have hklt := Finset.mem_range.mp hk
    omega
  rw [hprefix, zero_add] at hsum
  rw [← hsum]
  apply tsum_congr
  intro d
  rw [Nat.add_comm]
  rfl

/-! ## A uniform homogeneous majorant -/

private theorem norm_boundedKernelLengthProfileIntegral_le
    (M : FiniteIrreducibleModel S) (tau : C(S, ℂ))
    {ell k : ℕ} (K : LabelledBoundedKernel ell)
    (L : BoundedKernelLengthProfile k K)
    (q B : ℝ) (hq : 0 ≤ q) (_hB : 0 ≤ B)
    (htau : ∀ x, ‖tau x‖ ≤ q)
    (hedge : ∀ (a b : S) (n : ℕ),
      ‖profilePathEdgeCoefficient M.bjrModel tau a b n‖ ≤ B * q ^ n) :
    ‖boundedKernelLengthProfileIntegral M.bjrModel tau K L‖ ≤
      B ^ K.shape.2.1.val * q ^ k := by
  have hsum :
      K.shape.1.val + ∑ e : Fin K.shape.2.1.val, (L.length e).val = k :=
    L.totalLength
  have hpoint (x : Fin K.shape.1.val → S) :
      ‖(∏ v : Fin K.shape.1.val, tau (x v)) *
          ∏ e : Fin K.shape.2.1.val,
            profilePathEdgeCoefficient M.bjrModel tau
              (x (boundedKernelOrderedEndpoints K.shape e).1)
              (x (boundedKernelOrderedEndpoints K.shape e).2)
              (L.length e).val‖ ≤
        B ^ K.shape.2.1.val * q ^ k := by
    have hbranch :
        ‖∏ v : Fin K.shape.1.val, tau (x v)‖ ≤
          q ^ K.shape.1.val := by
      calc
        ‖∏ v : Fin K.shape.1.val, tau (x v)‖ =
            ∏ v : Fin K.shape.1.val, ‖tau (x v)‖ := by
          simp only [norm_prod]
        _ ≤ ∏ _v : Fin K.shape.1.val, q := by
          apply Finset.prod_le_prod
          · intro v hv
            exact norm_nonneg _
          · intro v hv
            exact htau (x v)
        _ = q ^ K.shape.1.val := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hedges :
        ‖∏ e : Fin K.shape.2.1.val,
            profilePathEdgeCoefficient M.bjrModel tau
              (x (boundedKernelOrderedEndpoints K.shape e).1)
              (x (boundedKernelOrderedEndpoints K.shape e).2)
              (L.length e).val‖ ≤
          B ^ K.shape.2.1.val *
            q ^ (∑ e : Fin K.shape.2.1.val, (L.length e).val) := by
      calc
        ‖∏ e : Fin K.shape.2.1.val,
            profilePathEdgeCoefficient M.bjrModel tau
              (x (boundedKernelOrderedEndpoints K.shape e).1)
              (x (boundedKernelOrderedEndpoints K.shape e).2)
              (L.length e).val‖ =
            ∏ e : Fin K.shape.2.1.val,
              ‖profilePathEdgeCoefficient M.bjrModel tau
                (x (boundedKernelOrderedEndpoints K.shape e).1)
                (x (boundedKernelOrderedEndpoints K.shape e).2)
                (L.length e).val‖ := by
          simp only [norm_prod]
        _ ≤ ∏ e : Fin K.shape.2.1.val,
              (B * q ^ (L.length e).val) := by
          apply Finset.prod_le_prod
          · intro e he
            exact norm_nonneg _
          · intro e he
            exact hedge _ _ _
        _ = B ^ K.shape.2.1.val *
            q ^ (∑ e : Fin K.shape.2.1.val, (L.length e).val) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin,
            Finset.prod_pow_eq_pow_sum]
    rw [norm_mul]
    calc
      ‖∏ v : Fin K.shape.1.val, tau (x v)‖ *
          ‖∏ e : Fin K.shape.2.1.val,
            profilePathEdgeCoefficient M.bjrModel tau
              (x (boundedKernelOrderedEndpoints K.shape e).1)
              (x (boundedKernelOrderedEndpoints K.shape e).2)
              (L.length e).val‖ ≤
          q ^ K.shape.1.val *
            (B ^ K.shape.2.1.val *
              q ^ (∑ e : Fin K.shape.2.1.val, (L.length e).val)) :=
        mul_le_mul hbranch hedges (norm_nonneg _)
          (pow_nonneg hq _)
      _ = B ^ K.shape.2.1.val * q ^ k := by
        calc
          q ^ K.shape.1.val *
                (B ^ K.shape.2.1.val *
                  q ^ (∑ e : Fin K.shape.2.1.val, (L.length e).val)) =
              B ^ K.shape.2.1.val *
                q ^ (K.shape.1.val +
                  ∑ e : Fin K.shape.2.1.val, (L.length e).val) := by
            rw [pow_add]
            ring
          _ = B ^ K.shape.2.1.val * q ^ k := by rw [hsum]
  have hedgeFactor (x : Fin K.shape.1.val → S)
      (e : Fin K.shape.2.1.val) :
      profilePathEdgeFactor M.bjrModel tau x (L.length e).val (K.shape.2.2 e) =
        profilePathEdgeCoefficient M.bjrModel tau
          (x (boundedKernelOrderedEndpoints K.shape e).1)
          (x (boundedKernelOrderedEndpoints K.shape e).2)
          (L.length e).val := by
    rw [← boundedKernelOrderedEndpoints_mk K e, profilePathEdgeFactor_mk]
  unfold boundedKernelLengthProfileIntegral
    boundedKernelProfileLengthIntegral boundedKernelLengthDatumOfProfile
  simp_rw [hedgeFactor]
  calc
    ‖∫ x : Fin K.shape.1.val → S,
        (∏ v : Fin K.shape.1.val, tau (x v)) *
          ∏ e : Fin K.shape.2.1.val,
            profilePathEdgeCoefficient M.bjrModel tau
              (x (boundedKernelOrderedEndpoints K.shape e).1)
              (x (boundedKernelOrderedEndpoints K.shape e).2)
              (L.length e).val
        ∂Measure.pi (fun _ : Fin K.shape.1.val ↦ M.bjrModel.mu)‖ ≤
      (B ^ K.shape.2.1.val * q ^ k) *
        (Measure.pi (fun _ : Fin K.shape.1.val ↦ M.bjrModel.mu)).real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [] with x
      exact hpoint x
    _ = B ^ K.shape.2.1.val * q ^ k := by simp

private theorem card_boundedKernelLengthProfile_le_pow
    {ell k : ℕ} (K : LabelledBoundedKernel ell) :
    letI := boundedKernelLengthProfileFintype k K
    Fintype.card (BoundedKernelLengthProfile k K) ≤
      (k + 1) ^ K.shape.2.1.val := by
  let _ := boundedKernelLengthProfileFintype k K
  let f : BoundedKernelLengthProfile k K →
      (Fin K.shape.2.1.val → Fin (k + 1)) := fun L ↦ L.length
  have hf : Function.Injective f := by
    intro L L' h
    cases L
    cases L'
    cases h
    rfl
  calc
    Fintype.card (BoundedKernelLengthProfile k K) ≤
        Fintype.card (Fin K.shape.2.1.val → Fin (k + 1)) :=
      Fintype.card_le_of_injective f hf
    _ = (k + 1) ^ K.shape.2.1.val := by
      simp only [Fintype.card_fun, Fintype.card_fin]

/-- A single polynomial-geometric majorant controls all literal noncubic
size coefficients.  The exponent `3 * ell` is deliberately coarse; the
strict noncubic edge inequality gives the required uniform finite bound. -/
theorem
    exists_positiveSurplusNoncubicAdmissibleProfileCoefficient_norm_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (ell : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (tau : C(S, ℂ)) (q : ℝ), 0 ≤ q → ‖tau‖ ≤ q →
        ∀ k : ℕ,
          ‖positiveSurplusNoncubicAdmissibleProfileCoefficient M.bjrModel tau ell k‖ ≤
            C * ((k + 1 : ℕ) : ℝ) ^ (3 * ell) * q ^ k := by
  classical
  obtain ⟨B, hB, hedge⟩ :=
    exists_profilePathEdgeCoefficient_geometric_bound M hM
  let _ := labelledConnectedNoncubicKernelFintype ell
  let W : ℝ := ∑ K : LabelledConnectedNoncubicKernel ell,
    ‖labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K‖
  let D : ℝ := max 1 (B ^ (3 * ell))
  let C : ℝ := W * D
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C, W, D]
    positivity
  · intro tau q hq htau k
    let _ (K : LabelledConnectedNoncubicKernel ell) :=
      boundedKernelLengthProfileFintype k K.1.toLabelledBoundedKernel
    have htau' : ∀ x, ‖tau x‖ ≤ q := fun x ↦
      (tau.norm_coe_le_norm x).trans htau
    have hedge' : ∀ (a b : S) (n : ℕ),
        ‖profilePathEdgeCoefficient M.bjrModel tau a b n‖ ≤ B * q ^ n :=
      hedge tau q hq htau'
    have hkernel (K : LabelledConnectedNoncubicKernel ell) :
        ‖∑ L : BoundedKernelLengthProfile k
            K.1.toLabelledBoundedKernel,
          boundedKernelLengthProfileIntegral M.bjrModel tau
            K.1.toLabelledBoundedKernel L‖ ≤
          (((k + 1 : ℕ) : ℝ) ^ (3 * ell)) * (D * q ^ k) := by
      let BK := K.1.toLabelledBoundedKernel
      have hne : BK.shape.2.1.val ≤ 3 * ell :=
        Nat.le_of_lt K.2
      have hBpow : B ^ BK.shape.2.1.val ≤ D := by
        dsimp only [D]
        by_cases hB1 : B ≤ 1
        · exact (pow_le_one₀ hB hB1).trans (le_max_left _ _)
        · have h1B : 1 ≤ B := le_of_not_ge hB1
          exact (pow_le_pow_right₀ h1B hne).trans (le_max_right _ _)
      have hcard :
          (Fintype.card (BoundedKernelLengthProfile k BK) : ℝ) ≤
            ((k + 1 : ℕ) : ℝ) ^ (3 * ell) := by
        calc
          (Fintype.card (BoundedKernelLengthProfile k BK) : ℝ) ≤
              (((k + 1) ^ BK.shape.2.1.val : ℕ) : ℝ) := by
            exact_mod_cast card_boundedKernelLengthProfile_le_pow BK
          _ = ((k + 1 : ℕ) : ℝ) ^ BK.shape.2.1.val := by
            norm_cast
          _ ≤ ((k + 1 : ℕ) : ℝ) ^ (3 * ell) := by
            have hkbase : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
            exact pow_le_pow_right₀ hkbase hne
      calc
        ‖∑ L : BoundedKernelLengthProfile k BK,
            boundedKernelLengthProfileIntegral M.bjrModel tau BK L‖ ≤
            ∑ L : BoundedKernelLengthProfile k BK,
              ‖boundedKernelLengthProfileIntegral M.bjrModel tau BK L‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _L : BoundedKernelLengthProfile k BK,
              (B ^ BK.shape.2.1.val * q ^ k) := by
          apply Finset.sum_le_sum
          intro L hL
          exact norm_boundedKernelLengthProfileIntegral_le
            M tau BK L q B hq hB htau' hedge'
        _ = (Fintype.card (BoundedKernelLengthProfile k BK) : ℝ) *
              (B ^ BK.shape.2.1.val * q ^ k) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ (((k + 1 : ℕ) : ℝ) ^ (3 * ell)) * (D * q ^ k) := by
          exact mul_le_mul hcard
            (mul_le_mul_of_nonneg_right hBpow (pow_nonneg hq _))
            (mul_nonneg (pow_nonneg hB _) (pow_nonneg hq _))
            (by positivity)
    unfold positiveSurplusNoncubicAdmissibleProfileCoefficient
    calc
      ‖∑ K : LabelledConnectedNoncubicKernel ell,
          labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K *
            ∑ L : BoundedKernelLengthProfile k
                K.1.toLabelledBoundedKernel,
              boundedKernelLengthProfileIntegral M.bjrModel tau
                K.1.toLabelledBoundedKernel L‖ ≤
          ∑ K : LabelledConnectedNoncubicKernel ell,
            ‖labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K *
              ∑ L : BoundedKernelLengthProfile k
                  K.1.toLabelledBoundedKernel,
                boundedKernelLengthProfileIntegral M.bjrModel tau
                  K.1.toLabelledBoundedKernel L‖ :=
        norm_sum_le _ _
      _ ≤ ∑ K : LabelledConnectedNoncubicKernel ell,
            ‖labelledConnectedNoncubicKernelInverseCoordinateMultiplicity K‖ *
              ((((k + 1 : ℕ) : ℝ) ^ (3 * ell)) * (D * q ^ k)) := by
        apply Finset.sum_le_sum
        intro K hK
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hkernel K) (norm_nonneg _)
      _ = C * ((k + 1 : ℕ) : ℝ) ^ (3 * ell) * q ^ k := by
        dsimp only [C, W]
        rw [← Finset.sum_mul]
        ring

private theorem nat_succ_le_two_pow_succ (k : ℕ) :
    k + 1 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        k + 1 + 1 ≤ 2 * (k + 1) := by omega
        _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1 + 1) := by rw [pow_succ]; ring

private theorem noncubicPolynomialFactor_le_geometric
    (ell k : ℕ) :
    (((k + 1 : ℕ) : ℝ) ^ (3 * ell)) ≤
      ((2 : ℝ) ^ (3 * ell)) ^ (k + 1) := by
  have hbase : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast nat_succ_le_two_pow_succ k
  calc
    (((k + 1 : ℕ) : ℝ) ^ (3 * ell)) ≤
        (((2 : ℝ) ^ (k + 1)) ^ (3 * ell)) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = ((2 : ℝ) ^ (3 * ell)) ^ (k + 1) := by
      simp only [← pow_mul]
      congr 1
      exact Nat.mul_comm _ _

private theorem noncubicProfile_isBigO_norm_of_coeff_zero
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    {tau : ℂ → A}
    {p : FormalMultilinearSeries ℂ ℂ A}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    tau =O[𝓝 (0 : ℂ)] (fun w : ℂ ↦ ‖w‖) := by
  have hpartial (w : ℂ) : p.partialSum 1 w = 0 := by
    change (∑ k ∈ Finset.range 1, p k (fun _ : Fin k ↦ w)) = 0
    rw [Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [zero_add,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff, hp0, smul_zero]
  have h := hp.isBigO_sub_partialSum_pow 1
  simpa only [zero_add, hpartial, sub_zero, pow_one, norm_norm] using h

/-- Deleting the first `N` literal size coefficients leaves a remainder of
order `N` along every linearly bounded profile germ. -/
theorem
    positiveSurplusNoncubicProfileFunctional_sub_partialSum_isBigO_of_isBigO
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell N : ℕ) {tau : ℂ → C(S, ℂ)}
    (htau : tau =O[𝓝 (0 : ℂ)] (fun w : ℂ ↦ ‖w‖)) :
    (fun w : ℂ ↦
      positiveSurplusNoncubicAdmissibleProfileFunctional M ell (tau w) -
        ∑ k ∈ Finset.range N,
          positiveSurplusNoncubicAdmissibleProfileCoefficient M.bjrModel (tau w) ell k)
      =O[𝓝 (0 : ℂ)] (fun w : ℂ ↦ ‖w‖ ^ N) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_positiveSurplusNoncubicAdmissibleProfileCoefficient_norm_bound
      M hM ell
  obtain ⟨c, hc⟩ := htau.isBigOWith
  let Ctau : ℝ := max 1 c
  let A : ℝ := (2 : ℝ) ^ (3 * ell)
  have hCtau : 0 < Ctau :=
    zero_lt_one.trans_le (le_max_left 1 c)
  have hcCtau : c ≤ Ctau := le_max_right 1 c
  have hA : 0 < A := by positivity
  have hlinear : ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖tau w‖ ≤ Ctau * ‖w‖ := by
    filter_upwards [hc.bound] with w hw
    have hw' : ‖tau w‖ ≤ c * ‖w‖ := by simpa using hw
    exact hw'.trans
      (mul_le_mul_of_nonneg_right hcCtau (norm_nonneg w))
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2 * C * A * (A * Ctau) ^ N, ?_⟩
  filter_upwards [hlinear,
    Metric.ball_mem_nhds (0 : ℂ)
      (by positivity : 0 < 1 / (2 * A * Ctau))]
      with w hwlinear hwball
  let q : ℝ := Ctau * ‖w‖
  let ratio : ℝ := A * q
  have hq : 0 ≤ q := mul_nonneg hCtau.le (norm_nonneg w)
  have hratio0 : 0 ≤ ratio := mul_nonneg hA.le hq
  have hratiohalf : ratio < 1 / 2 := by
    have hwball' : ‖w‖ < 1 / (2 * A * Ctau) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hwball
    calc
      ratio < A * (Ctau * (1 / (2 * A * Ctau))) := by
        dsimp only [ratio, q]
        exact mul_lt_mul_of_pos_left
          (mul_lt_mul_of_pos_left hwball' hCtau) hA
      _ = 1 / 2 := by field_simp [hA.ne', hCtau.ne']
  have hratio1 : ratio < 1 := hratiohalf.trans (by norm_num)
  have hq1 : q < 1 := by
    have hAle : 1 ≤ A := by
      dsimp only [A]
      exact one_le_pow₀ (by norm_num)
    have hqle : q ≤ ratio := by
      dsimp only [ratio]
      nlinarith [hq]
    exact hqle.trans_lt hratio1
  have htauq : ‖tau w‖ ≤ q := by simpa only [q] using hwlinear
  let f : ℕ → ℂ := fun k ↦
    positiveSurplusNoncubicAdmissibleProfileCoefficient M.bjrModel (tau w) ell k
  have hterm (k : ℕ) :
      ‖f k‖ ≤ C * A * ratio ^ k := by
    calc
      ‖f k‖ ≤ C * (((k + 1 : ℕ) : ℝ) ^ (3 * ell)) * q ^ k := by
        simpa only [f] using hcoeff (tau w) q hq htauq k
      _ ≤ C * (A ^ (k + 1)) * q ^ k := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (noncubicPolynomialFactor_le_geometric ell k) hC)
          (pow_nonneg hq _)
      _ = C * A * ratio ^ k := by
        dsimp only [ratio]
        rw [pow_succ, mul_pow]
        ring
  have hsumNorm : Summable (fun k : ℕ ↦ ‖f k‖) := by
    have hgeom : Summable (fun k : ℕ ↦ C * A * ratio ^ k) :=
      (summable_geometric_of_lt_one hratio0 hratio1).mul_left (C * A)
    exact Summable.of_nonneg_of_le
      (fun k ↦ norm_nonneg (f k)) hterm hgeom
  have hsum : Summable f := hsumNorm.of_norm
  have htailIdentity :
      positiveSurplusNoncubicAdmissibleProfileFunctional M ell (tau w) -
          ∑ k ∈ Finset.range N, f k =
        ∑' n : ℕ, f (n + N) := by
    have hfull := positiveSurplusNoncubicAdmissibleProfileFunctional_eq_tsum
      M hM ell (tau w) q hq hq1
        (fun y ↦ ((tau w).norm_coe_le_norm y).trans htauq)
    have hsplit := hsum.sum_add_tsum_nat_add N
    rw [hfull, ← hsplit]
    abel
  have hshift (n : ℕ) :
      ‖f (n + N)‖ ≤
        (C * A * ratio ^ N) * ratio ^ n := by
    calc
      ‖f (n + N)‖ ≤ C * A * ratio ^ (n + N) := hterm (n + N)
      _ = (C * A * ratio ^ N) * ratio ^ n := by
        rw [pow_add]
        ring
  have hmajor : HasSum
      (fun n : ℕ ↦ (C * A * ratio ^ N) * ratio ^ n)
      ((C * A * ratio ^ N) * (1 - ratio)⁻¹) :=
    (hasSum_geometric_of_lt_one hratio0 hratio1).mul_left
      (C * A * ratio ^ N)
  have htailBound :
      ‖∑' n : ℕ, f (n + N)‖ ≤
        (C * A * ratio ^ N) * (1 - ratio)⁻¹ :=
    tsum_of_norm_bounded hmajor hshift
  have hinv : (1 - ratio)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ (sub_pos_of_lt hratio1) two_pos]
    linarith
  have htailFinal :
      ‖positiveSurplusNoncubicAdmissibleProfileFunctional
          M ell (tau w) -
        ∑ k ∈ Finset.range N,
          positiveSurplusNoncubicAdmissibleProfileCoefficient M.bjrModel (tau w) ell k‖ ≤
        (2 * C * A * (A * Ctau) ^ N) * ‖w‖ ^ N := by
    change ‖positiveSurplusNoncubicAdmissibleProfileFunctional
      M ell (tau w) - ∑ k ∈ Finset.range N, f k‖ ≤ _
    rw [htailIdentity]
    calc
      ‖∑' n : ℕ, f (n + N)‖ ≤
          (C * A * ratio ^ N) * (1 - ratio)⁻¹ := htailBound
      _ ≤ (C * A * ratio ^ N) * 2 := by
        exact mul_le_mul_of_nonneg_left hinv
          (mul_nonneg (mul_nonneg hC hA.le) (pow_nonneg hratio0 _))
      _ = (2 * C * A * (A * Ctau) ^ N) * ‖w‖ ^ N := by
        dsimp only [ratio, q]
        simp only [mul_pow]
        ring
  simpa only [norm_pow, Real.norm_eq_abs, abs_norm] using htailFinal

/-- Analytic profile germs with zero constant coefficient satisfy the
preceding literal size-tail estimate. -/
theorem positiveSurplusNoncubicProfileFunctional_sub_partialSum_isBigO
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell N : ℕ) {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    (fun w : ℂ ↦
      positiveSurplusNoncubicAdmissibleProfileFunctional M ell (tau w) -
        ∑ k ∈ Finset.range N,
          positiveSurplusNoncubicAdmissibleProfileCoefficient M.bjrModel (tau w) ell k)
      =O[𝓝 (0 : ℂ)] (fun w : ℂ ↦ ‖w‖ ^ N) :=
  positiveSurplusNoncubicProfileFunctional_sub_partialSum_isBigO_of_isBigO
    M hM ell N (noncubicProfile_isBigO_norm_of_coeff_zero hp hp0)

theorem
    positiveSurplusNoncubicAdmissibleProfileFunctional_hasFPowerSeriesAt
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    HasFPowerSeriesAt
      (fun w ↦ positiveSurplusNoncubicAdmissibleProfileFunctional
        M ell (tau w))
      (oneDimensionalFormalMultilinearSeries
        (positiveSurplusNoncubicProfileCompositionSeries M.bjrModel
          (oneDimensionalPowerSeries p) ell)) 0 := by
  have htau0 : tau 0 = 0 := by
    have h := hp.coeff_zero (1 : Fin 0 → ℂ)
    have h' : p.coeff 0 = tau 0 := by
      simpa only [FormalMultilinearSeries.coeff] using h
    exact h'.symm.trans hp0
  have hfullAnalytic : AnalyticAt ℂ
      (fun w ↦ positiveSurplusNoncubicAdmissibleProfileFunctional
        M ell (tau w)) 0 :=
    (positiveSurplusNoncubicAdmissibleProfileFunctional_analyticAt_of_norm_lt_one
      M hM ell (by simp)).comp_of_eq hp.analyticAt htau0
  obtain ⟨pFull, hpFull⟩ := hfullAnalytic
  have hcoeff : ∀ n : ℕ,
      pFull.coeff n =
        positiveSurplusNoncubicProfileCompositionCoeff M.bjrModel
          (oneDimensionalPowerSeries p) ell n := by
    intro n
    let N : ℕ := n + 1
    let Q : PowerSeries ℂ :=
      ∑ k ∈ Finset.range N,
        positiveSurplusNoncubicFixedSizeProfileCompositionSeries M.bjrModel
          (oneDimensionalPowerSeries p) ell k
    let pN : FormalMultilinearSeries ℂ ℂ ℂ :=
      ∑ k ∈ Finset.range N,
        oneDimensionalFormalMultilinearSeries
          (positiveSurplusNoncubicFixedSizeProfileCompositionSeries M.bjrModel
            (oneDimensionalPowerSeries p) ell k)
    have hpN : HasFPowerSeriesAt
        (fun w ↦ ∑ k ∈ Finset.range N,
          positiveSurplusNoncubicAdmissibleProfileCoefficient M.bjrModel (tau w) ell k)
        pN 0 := by
      simpa only [N, pN] using
        positiveSurplusNoncubicAdmissibleProfileCoefficient_partialSum_hasFPowerSeriesAt M.bjrModel hell N hp hp0
    have hdiff := hpFull.sub hpN
    have htail :=
      positiveSurplusNoncubicProfileFunctional_sub_partialSum_isBigO
        M hM ell N hp hp0
    have hzero : (pFull - pN).coeff n = 0 :=
      hdiff.coeff_eq_zero_of_isBigO_norm_pow htail
        (by dsimp only [N]; omega)
    have hpNEq : pN = oneDimensionalFormalMultilinearSeries Q := by
      dsimp only [pN, Q]
      exact (oneDimensionalFormalMultilinearSeries_map_finset_sum
        (Finset.range N)
        (fun k ↦ positiveSurplusNoncubicFixedSizeProfileCompositionSeries M.bjrModel (oneDimensionalPowerSeries p) ell k)).symm
    have hpNcoeff : pN.coeff n =
        positiveSurplusNoncubicProfileCompositionCoeff M.bjrModel
          (oneDimensionalPowerSeries p) ell n := by
      rw [hpNEq, oneDimensionalFormalMultilinearSeries_coeff]
      rfl
    change pFull.coeff n - pN.coeff n = 0 at hzero
    exact (sub_eq_zero.mp hzero).trans hpNcoeff
  have hpower : oneDimensionalPowerSeries pFull =
      positiveSurplusNoncubicProfileCompositionSeries M.bjrModel
        (oneDimensionalPowerSeries p) ell := by
    apply PowerSeries.ext
    intro n
    simp only [oneDimensionalPowerSeries_coeff,
      positiveSurplusNoncubicProfileCompositionSeries_coeff, hcoeff]
  have hpFullEq : pFull =
      oneDimensionalFormalMultilinearSeries
        (positiveSurplusNoncubicProfileCompositionSeries M.bjrModel
          (oneDimensionalPowerSeries p) ell) := by
    calc
      pFull = oneDimensionalFormalMultilinearSeries
          (oneDimensionalPowerSeries pFull) :=
        (oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries
          pFull).symm
      _ = _ := by rw [hpower]
  rw [← hpFullEq]
  exact hpFull


end PerronWright.FiniteIrreducibleKernelAmplitude
