import PerronWright.Analysis.FiniteIrreducibleCubicForbiddenCorrection
import PerronWright.Enumeration.CubicForbiddenCorrectionBridge

/-!
# Literal finite irreducible length assignments and cubic resolvents

Pure witness constraints and finite inclusion-exclusion are reused from the
proved graph classification. Actual finite Perron Neumann convergence
identifies every raw resolvent cylinder with the genuine infinite length
assignment sum, and true product-measure integration preserves this identity.
No regular-critical or primitive model is required.
-/
open MeasureTheory PerronWright
open scoped Classical Topology BigOperators
noncomputable section
namespace PerronWright.FiniteIrreducibleKernelAmplitude
open GraphCore
namespace MPR
export PerronWright.FiniteIrreducibleMarkedPathResolvent
  (profile pathResolventKernel)
end MPR
variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The existing coefficient sequence is summable by the actual finite path bridge. -/
theorem summable_profilePathEdgeCoefficient
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (tau : C(S, ℂ)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖tau x‖ ≤ q) (a b : S) :
    Summable (fun n : ℕ => GraphCore.profilePathEdgeCoefficient M.bjrModel tau a b n) := by
  simpa only [GraphCore.complexProfilePathWeight_eq_profilePathEdgeCoefficient] using
    (FiniteIrreduciblePathGeneratingSeries.hasSum_literal_pathWeight
      M hM tau q hq hq1 ha a b).summable

/-- The existing literal coefficient series sums to the true finite fold resolvent. -/
theorem tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (p : C(S, ℂ) × ℂ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ x, ‖MPR.profile M hM p x‖ ≤ q) (a b : S) :
    (∑' n : ℕ, GraphCore.profilePathEdgeCoefficient
      M.bjrModel (MPR.profile M hM p) a b n) =
        MPR.pathResolventKernel M hM p (a,b) := by
  simpa only [GraphCore.complexProfilePathWeight_eq_profilePathEdgeCoefficient] using
    (FiniteIrreduciblePathGeneratingSeries.hasSum_literal_fold_pathWeight
      M hM p q hq hq1 ha a b).tsum_eq

/-! ## Factorization of one literal witness intersection -/

/-- The one-edge coefficient sequence with the length frozen when the
pattern forces that edge. -/
def cubicForbiddenPatternEdgeCoefficient
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ)
    (x : Fin (2 * ell) → S) (n : ℕ) : ℂ :=
  if CubicForbiddenPatternForcesEdge J e then
    if n = cubicForbiddenPatternLength J e then
      profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) n
    else 0
  else
    profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2) n

theorem cubicForbiddenPatternEdgeCoefficient_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ)
    (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    Summable (cubicForbiddenPatternEdgeCoefficient M hM K J e q x) := by
  classical
  by_cases he : CubicForbiddenPatternForcesEdge J e
  · let c : ℕ → ℂ := fun n ↦
      profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) n
    have hs := (hasSum_ite_eq (cubicForbiddenPatternLength J e)
      (c (cubicForbiddenPatternLength J e))).summable
    exact hs.congr (fun n ↦ by
      by_cases hn : n = cubicForbiddenPatternLength J e
      · subst n
        simp [cubicForbiddenPatternEdgeCoefficient, he, c]
      · simp [cubicForbiddenPatternEdgeCoefficient, he, hn, c])
  · exact (summable_profilePathEdgeCoefficient M hM
      (MPR.profile M hM q) r hr hr1 hprofile
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2)).congr
        (fun n ↦ by simp [cubicForbiddenPatternEdgeCoefficient, he])

theorem tsum_cubicForbiddenPatternEdgeCoefficient
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ)
    (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    (∑' n : ℕ,
        cubicForbiddenPatternEdgeCoefficient M hM K J e q x n) =
      cubicForbiddenRawPatternEdgeFunction M hM K J e q x := by
  classical
  by_cases he : CubicForbiddenPatternForcesEdge J e
  · let c : ℕ → ℂ := fun n ↦
      profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) n
    calc
      (∑' n : ℕ,
          cubicForbiddenPatternEdgeCoefficient M hM K J e q x n) =
          c (cubicForbiddenPatternLength J e) := by
        calc
          _ = ∑' n : ℕ, if n = cubicForbiddenPatternLength J e then
              c (cubicForbiddenPatternLength J e) else 0 := by
            apply tsum_congr
            intro n
            by_cases hn : n = cubicForbiddenPatternLength J e
            · subst n
              simp [cubicForbiddenPatternEdgeCoefficient, he, c]
            · simp [cubicForbiddenPatternEdgeCoefficient, he, hn, c]
          _ = c (cubicForbiddenPatternLength J e) :=
            (hasSum_ite_eq (cubicForbiddenPatternLength J e)
              (c (cubicForbiddenPatternLength J e))).tsum_eq
      _ = cubicForbiddenRawPatternEdgeFunction M hM K J e q x := by
        simp [cubicForbiddenRawPatternEdgeFunction, he, c]
  · have hsum := tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
      M hM q r hr hr1 hprofile
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2)
    rw [show (∑' n : ℕ,
        cubicForbiddenPatternEdgeCoefficient M hM K J e q x n) =
        ∑' n : ℕ, profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
          (x (cubicKernelOrderedEndpoints K.graph e).1)
          (x (cubicKernelOrderedEndpoints K.graph e).2) n by
      apply tsum_congr
      intro n
      simp [cubicForbiddenPatternEdgeCoefficient, he]]
    rw [tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
      M hM q r hr hr1 hprofile]
    unfold cubicForbiddenRawPatternEdgeFunction
    rw [if_neg he]
    change (MPR.pathResolventKernel M hM q)
      (x (cubicKernelOrderedEndpoints K.graph e).1,
        x (cubicKernelOrderedEndpoints K.graph e).2) =
      (MPR.pathResolventKernel M hM q)
      (x (cubicKernelOrderedEndpoints K.graph e).1,
        x (cubicKernelOrderedEndpoints K.graph e).2)
    rfl

/-- A pattern-restricted table weight.  The outer compatibility test makes
an inconsistent witness intersection literally empty. -/
def cubicForbiddenPatternAssignmentWeight
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (l : Fin (3 * ell) → ℕ) : ℂ :=
  if CubicForbiddenPatternCompatible J then
    ∏ e : Fin (3 * ell),
      cubicForbiddenPatternEdgeCoefficient M hM K J e q x (l e)
  else 0

/-- The frozen-edge description agrees pointwise with the literal
simultaneous-occurrence indicator. -/
theorem cubicForbiddenPatternAssignmentWeight_eq_occurrenceIndicator
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (l : Fin (3 * ell) → ℕ) :
    cubicForbiddenPatternAssignmentWeight M hM K J q x l =
      if ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
      else 0 := by
  classical
  by_cases hall :
      ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l)
  · obtain ⟨hcompat, hlength⟩ :=
      (cubicForbiddenPattern_all_occurs_iff J l).mp hall
    rw [if_pos hall]
    unfold cubicForbiddenPatternAssignmentWeight
    rw [if_pos hcompat]
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : CubicForbiddenPatternForcesEdge J e
    · simp [cubicForbiddenPatternEdgeCoefficient, he, hlength e he]
    · simp [cubicForbiddenPatternEdgeCoefficient, he]
  · rw [if_neg hall]
    unfold cubicForbiddenPatternAssignmentWeight
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
      simp [cubicForbiddenPatternEdgeCoefficient, he, hne]
    · simp [hcompat]

theorem cubicForbiddenPatternAssignmentWeight_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    Summable (cubicForbiddenPatternAssignmentWeight M hM K J q x) := by
  classical
  by_cases hcompat : CubicForbiddenPatternCompatible J
  · exact (summable_finFunction_prod_and_tsum
        (fun e n ↦ cubicForbiddenPatternEdgeCoefficient
          M hM K J e q x n)
        (fun e ↦ cubicForbiddenPatternEdgeCoefficient_summable
          M hM K J e q x r hr hr1 hprofile)).1.congr
      (fun l ↦ by simp [cubicForbiddenPatternAssignmentWeight, hcompat])
  · exact summable_zero.congr
      (fun l ↦ by simp [cubicForbiddenPatternAssignmentWeight, hcompat])

theorem tsum_cubicForbiddenPatternAssignmentWeight
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r)
    (hcompat : CubicForbiddenPatternCompatible J) :
    (∑' l : Fin (3 * ell) → ℕ,
        cubicForbiddenPatternAssignmentWeight M hM K J q x l) =
      ∏ e : Fin (3 * ell),
        cubicForbiddenRawPatternEdgeFunction M hM K J e q x := by
  classical
  simp only [cubicForbiddenPatternAssignmentWeight, hcompat, if_true]
  rw [(summable_finFunction_prod_and_tsum
    (fun e n ↦ cubicForbiddenPatternEdgeCoefficient
      M hM K J e q x n)
    (fun e ↦ cubicForbiddenPatternEdgeCoefficient_summable
      M hM K J e q x r hr hr1 hprofile)).2]
  apply Finset.prod_congr rfl
  intro e _
  exact tsum_cubicForbiddenPatternEdgeCoefficient
    M hM K J e q x r hr hr1 hprofile

/-! ## The raw correction is the literal forbidden assignment sum -/

/-- Literal pointwise forbidden length-assignment sum for one labelled
cubic kernel. -/
def cubicKernelLiteralForbiddenAssignmentIntegrand
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S) : ℂ :=
  cubicKernelBranchProfileFunction M hM (ell := ell) q x *
    ∑' l : Fin (3 * ell) → ℕ,
      if ∃ w : CubicKernelForbiddenLengthWitness K.graph,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
      else 0

/-- Pointwise, the finite raw inclusion--exclusion sum is the literal
forbidden-assignment sum. -/
theorem cubicKernelRawForbiddenCorrection_eq_literalAssignmentIntegrand
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    letI := cubicKernelForbiddenLengthWitnessFintype K.graph
    (∑ J ∈ (Finset.univ :
        Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
          Finset.Nonempty,
      (-1 : ℂ) ^ (J.card + 1) *
        cubicForbiddenRawIntersectionFunction M hM K J q x) =
      cubicKernelLiteralForbiddenAssignmentIntegrand M hM K q x := by
  let _ := cubicKernelForbiddenLengthWitnessFintype K.graph
  classical
  let P := (Finset.univ :
    Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
      Finset.Nonempty
  let B : (Fin (3 * ell) → ℕ) → ℂ := fun l ↦
    ∏ e : Fin (3 * ell),
      profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
  have hJsum (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
      cubicForbiddenRawIntersectionFunction M hM K J q x =
        cubicKernelBranchProfileFunction M hM (ell := ell) q x *
          ∑' l : Fin (3 * ell) → ℕ,
            cubicForbiddenPatternAssignmentWeight M hM K J q x l := by
    unfold cubicForbiddenRawIntersectionFunction
    by_cases hcompat : CubicForbiddenPatternCompatible J
    · rw [if_pos hcompat,
          tsum_cubicForbiddenPatternAssignmentWeight
            M hM K J q x r hr hr1 hprofile hcompat]
      rw [ContinuousMap.mul_apply, ContinuousMap.prod_apply]
    · rw [if_neg hcompat]
      have hzero :
          (∑' l : Fin (3 * ell) → ℕ,
            cubicForbiddenPatternAssignmentWeight M hM K J q x l) = 0 := by
        simp [cubicForbiddenPatternAssignmentWeight, hcompat]
      rw [hzero, mul_zero]
      rfl
  have hsumJ (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
      Summable (fun l : Fin (3 * ell) → ℕ ↦
        (-1 : ℂ) ^ (J.card + 1) *
          cubicForbiddenPatternAssignmentWeight M hM K J q x l) :=
    (cubicForbiddenPatternAssignmentWeight_summable
      M hM K J q x r hr hr1 hprofile).mul_left _
  unfold cubicKernelLiteralForbiddenAssignmentIntegrand
  simp_rw [hJsum]
  rw [show (∑ J ∈ P, (-1 : ℂ) ^ (J.card + 1) *
        ((cubicKernelBranchProfileFunction M hM (ell := ell) q) x *
          ∑' l : Fin (3 * ell) → ℕ,
            cubicForbiddenPatternAssignmentWeight M hM K J q x l)) =
      (cubicKernelBranchProfileFunction M hM (ell := ell) q) x *
        ∑ J ∈ P, (-1 : ℂ) ^ (J.card + 1) *
          ∑' l : Fin (3 * ell) → ℕ,
            cubicForbiddenPatternAssignmentWeight M hM K J q x l by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J _
      ring]
  have hswap := Summable.tsum_finsetSum
    (s := P)
    (f := fun J l ↦ (-1 : ℂ) ^ (J.card + 1) *
      cubicForbiddenPatternAssignmentWeight M hM K J q x l)
    (fun J _ ↦ hsumJ J)
  have hscale (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
      (-1 : ℂ) ^ (J.card + 1) *
          ∑' l : Fin (3 * ell) → ℕ,
            cubicForbiddenPatternAssignmentWeight M hM K J q x l =
        ∑' l : Fin (3 * ell) → ℕ,
          (-1 : ℂ) ^ (J.card + 1) *
            cubicForbiddenPatternAssignmentWeight M hM K J q x l :=
    ((cubicForbiddenPatternAssignmentWeight_summable
      M hM K J q x r hr hr1 hprofile).tsum_mul_left _).symm
  simp_rw [hscale]
  rw [← hswap]
  apply congrArg (fun z : ℂ ↦
    cubicKernelBranchProfileFunction M hM (ell := ell) q x * z)
  apply tsum_congr
  intro l
  simp_rw [cubicForbiddenPatternAssignmentWeight_eq_occurrenceIndicator]
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

/-- After integration, the already defined raw analytic correction is
exactly the integral of the literal forbidden length-assignment `tsum`. -/
theorem cubicKernelIntegratedRawForbiddenCorrection_eq_literalAssignmentIntegral
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    cubicKernelIntegratedRawForbiddenCorrection M hM K q =
      ∫ x : Fin (2 * ell) → S,
        cubicKernelLiteralForbiddenAssignmentIntegrand M hM K q x
          ∂cubicKernelProductMeasure M ell := by
  let _ := cubicKernelForbiddenLengthWitnessFintype K.graph
  classical
  unfold cubicKernelIntegratedRawForbiddenCorrection
    cubicKernelIntegratedRawForbiddenIntersection
  simp_rw [← smul_eq_mul, ← map_smul]
  rw [← map_sum, cubicKernelIntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  exact cubicKernelRawForbiddenCorrection_eq_literalAssignmentIntegrand
    M hM K q x r hr hr1 hprofile

/-! ## The complementary literal admissible sum -/

/-- Literal unrestricted table sum for one labelled cubic kernel. -/
def cubicKernelLiteralUnrestrictedAssignmentIntegrand
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S) : ℂ :=
  cubicKernelBranchProfileFunction M hM (ell := ell) q x *
    ∑' l : Fin (3 * ell) → ℕ,
      ∏ e : Fin (3 * ell),
        profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
          (x (cubicKernelOrderedEndpoints K.graph e).1)
          (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)

/-- Literal admissible table sum, with the exact loop and zero-parallel-edge
conditions from `CubicKernelLengthAssignment.IsAdmissible`. -/
def cubicKernelLiteralAdmissibleAssignmentIntegrand
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S) : ℂ :=
  cubicKernelBranchProfileFunction M hM (ell := ell) q x *
    ∑' l : Fin (3 * ell) → ℕ,
      if CubicKernelLengthAssignment.IsAdmissible K.graph
          (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
      else 0

private theorem cubicKernelAssignmentProduct_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    Summable (fun l : Fin (3 * ell) → ℕ ↦
      ∏ e : Fin (3 * ell),
        profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
          (x (cubicKernelOrderedEndpoints K.graph e).1)
          (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)) := by
  exact (summable_finFunction_prod_and_tsum
    (fun e n ↦ profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2) n)
    (fun e ↦ summable_profilePathEdgeCoefficient M hM
      (MPR.profile M hM q) r hr hr1 hprofile _ _)).1

/-- The unrestricted marked-path resolvent product is the literal `tsum`
over all finite edge-length tables. -/
theorem cubicKernelResolventIntegrandFunction_eq_literalUnrestricted
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    cubicKernelResolventIntegrandFunction M hM K q x =
      cubicKernelLiteralUnrestrictedAssignmentIntegrand M hM K q x := by
  rw [cubicKernelResolventIntegrandFunction_apply]
  unfold cubicKernelResolventIntegrand
    cubicKernelLiteralUnrestrictedAssignmentIntegrand
  rw [cubicKernelBranchProfileFunction_apply]
  apply congrArg (fun z : ℂ ↦
    cubicKernelBranchProfileProduct M hM x q * z)
  rw [(summable_finFunction_prod_and_tsum
    (fun e n ↦ profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2) n)
    (fun e ↦ summable_profilePathEdgeCoefficient M hM
      (MPR.profile M hM q) r hr hr1 hprofile _ _)).2]
  apply Finset.prod_congr rfl
  intro e _
  exact tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
    M hM q r hr hr1 hprofile _ _ |>.symm

/-- Literal admissible and forbidden tables partition the unrestricted
table sum.  Absolute summability justifies the two subseries. -/
theorem cubicKernelLiteralAdmissible_add_forbidden_eq_unrestricted
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    cubicKernelLiteralAdmissibleAssignmentIntegrand M hM K q x +
        cubicKernelLiteralForbiddenAssignmentIntegrand M hM K q x =
      cubicKernelLiteralUnrestrictedAssignmentIntegrand M hM K q x := by
  classical
  let B : (Fin (3 * ell) → ℕ) → ℂ := fun l ↦
    ∏ e : Fin (3 * ell),
      profilePathEdgeCoefficient M.bjrModel (MPR.profile M hM q)
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
  let A : Set (Fin (3 * ell) → ℕ) := {l |
    CubicKernelLengthAssignment.IsAdmissible K.graph
      (Finsupp.equivFunOnFinite.symm l)}
  let F : Set (Fin (3 * ell) → ℕ) := {l |
    ∃ w : CubicKernelForbiddenLengthWitness K.graph,
      w.Occurs (Finsupp.equivFunOnFinite.symm l)}
  have hB : Summable B :=
    cubicKernelAssignmentProduct_summable M hM K q x r hr hr1 hprofile
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
  unfold cubicKernelLiteralAdmissibleAssignmentIntegrand
    cubicKernelLiteralForbiddenAssignmentIntegrand
    cubicKernelLiteralUnrestrictedAssignmentIntegrand
  rw [← mul_add]
  apply congrArg (fun z : ℂ ↦
    cubicKernelBranchProfileFunction M hM (ell := ell) q x * z)
  change (∑' l, A.indicator B l) + (∑' l, F.indicator B l) = ∑' l, B l
  rw [← hA.tsum_add hF]
  exact tsum_congr hterm

/-- The fixed-kernel admissible resolvent contribution is an integral of the
literal admissible length-assignment `tsum`. -/
theorem cubicKernelIntegratedResolvent_sub_rawForbidden_eq_literalAdmissible
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    cubicKernelIntegratedResolventProduct M hM K q -
        cubicKernelIntegratedRawForbiddenCorrection M hM K q =
      ∫ x : Fin (2 * ell) → S,
        cubicKernelLiteralAdmissibleAssignmentIntegrand M hM K q x
          ∂cubicKernelProductMeasure M ell := by
  rw [cubicKernelIntegratedRawForbiddenCorrection_eq_literalAssignmentIntegral
    M hM K q r hr hr1 hprofile]
  unfold cubicKernelIntegratedResolventProduct
  rw [cubicKernelIntegralCLM_apply]
  have hf : Integrable
      (⇑(cubicKernelResolventIntegrandFunction M hM K q))
      (cubicKernelProductMeasure M ell) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (cubicKernelResolventIntegrandFunction M hM K q).continuous
    · exact isClosed_closure.isCompact
  let _ := cubicKernelForbiddenLengthWitnessFintype K.graph
  let G : C((Fin (2 * ell) → S), ℂ) :=
    ∑ J ∈ (Finset.univ :
        Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
          Finset.Nonempty,
      (-1 : ℂ) ^ (J.card + 1) •
        cubicForbiddenRawIntersectionFunction M hM K J q
  have hG : Integrable (G : (Fin (2 * ell) → S) → ℂ)
      (cubicKernelProductMeasure M ell) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact G.continuous
    · exact isClosed_closure.isCompact
  have hg : Integrable
      (cubicKernelLiteralForbiddenAssignmentIntegrand M hM K q)
      (cubicKernelProductMeasure M ell) := by
    apply hG.congr
    filter_upwards [] with x
    have hx := cubicKernelRawForbiddenCorrection_eq_literalAssignmentIntegrand
      M hM K q x r hr hr1 hprofile
    simpa only [G, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul] using hx
  rw [← integral_sub hf hg]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [cubicKernelResolventIntegrandFunction_eq_literalUnrestricted
    M hM K q x r hr hr1 hprofile]
  have hsplit := cubicKernelLiteralAdmissible_add_forbidden_eq_unrestricted
    M hM K q x r hr hr1 hprofile
  exact sub_eq_iff_eq_add.mpr hsplit.symm

/-- Exact finite inverse-multiplicity sum of the literal admissible
assignment integrals. -/
def positiveSurplusCubicLiteralAdmissibleResolventSum
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      ∫ x : Fin (2 * ell) → S,
        cubicKernelLiteralAdmissibleAssignmentIntegrand M hM K q x
          ∂cubicKernelProductMeasure M ell

/-- On a strict-subcritical profile ball, the raw admissible resolvent sum
defined by inclusion--exclusion is exactly the literal admissible
length-assignment sum. -/
theorem positiveSurplusCubicAdmissibleResolventSum_eq_literal
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    positiveSurplusCubicAdmissibleResolventSum M hM ell q =
      positiveSurplusCubicLiteralAdmissibleResolventSum M hM ell q := by
  let _ := labelledConnectedCubicKernelFintype ell
  unfold positiveSurplusCubicAdmissibleResolventSum
    positiveSurplusCubicIntegratedResolventSum
    positiveSurplusCubicRawForbiddenCorrection
    positiveSurplusCubicLiteralAdmissibleResolventSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro K _
  rw [← mul_sub]
  congr 1
  exact cubicKernelIntegratedResolvent_sub_rawForbidden_eq_literalAdmissible
    M hM K q r hr hr1 hprofile


end PerronWright.FiniteIrreducibleKernelAmplitude

