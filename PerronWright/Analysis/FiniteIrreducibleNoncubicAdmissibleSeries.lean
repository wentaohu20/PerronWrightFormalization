import PerronWright.Analysis.FiniteIrreducibleNoncubicRemainder
import PerronWright.Analysis.FiniteIrreducibleCubicLiteralResolvent
import PerronWright.Enumeration.NoncubicBoundedKernelAdmissibleSeries

/-! Actual all-length admissible bounded-kernel series for literal finite
irreducible critical models. Pure witness/length-profile classifications
are reused through the data-only BJR model. Convergence and resolvent
identification use the proved finite Perron-gauge Neumann series, with
no primitive assumption. -/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators
noncomputable section
namespace PerronWright.FiniteIrreducibleKernelAmplitude
open GraphCore
namespace NBKAS_MPR
export PerronWright.FiniteIrreducibleMarkedPathResolvent (profile pathResolventKernel)
end NBKAS_MPR
variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## Raw and normalized finite witness cylinders -/

/-- One fixed-length path coefficient, evaluated at the endpoints of a
bounded kernel edge along the joint fold chart. -/
def boundedKernelFixedLengthEdgeFactor
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (n : ℕ)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  cubicFixedLengthPathKernel M hM n q
    (x (boundedKernelOrderedEndpoints K.shape e).1,
      x (boundedKernelOrderedEndpoints K.shape e).2)

@[simp] theorem boundedKernelFixedLengthEdgeFactor_eq_profileCoefficient
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (n : ℕ)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    boundedKernelFixedLengthEdgeFactor M hM K e n q x =
      profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) n := by
  rfl

theorem boundedKernelFixedLengthEdgeFactor_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (n : ℕ)
    (x : Fin K.shape.1.val → S) :
    AnalyticAt ℂ (fun q ↦
      boundedKernelFixedLengthEdgeFactor M hM K e n q x) (0, 0) := by
  let p : S × S :=
    (x (boundedKernelOrderedEndpoints K.shape e).1,
      x (boundedKernelOrderedEndpoints K.shape e).2)
  have heval : AnalyticAt ℂ
      (fun k : C(S × S, ℂ) ↦ k p)
      (cubicFixedLengthPathKernel M hM n (0, 0)) :=
    (ContinuousMap.evalCLM ℂ p : C(S × S, ℂ) →L[ℂ] ℂ).analyticAt _
  exact heval.comp_of_eq (cubicFixedLengthPathKernel_analytic M hM n) rfl

/-- Raw fixed-length/resolvent factor associated with one witness pattern. -/
def boundedKernelForbiddenRawPatternEdgeFactor
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S) : ℂ :=
  if BoundedKernelForbiddenPatternForcesEdge J e then
    boundedKernelFixedLengthEdgeFactor M hM K e
      (boundedKernelForbiddenPatternLength J e) q x
  else
    NBKAS_MPR.pathResolventKernel M hM q
      (x (boundedKernelOrderedEndpoints K.shape e).1,
        x (boundedKernelOrderedEndpoints K.shape e).2)

/-- Pole-removed edge factor for one witness pattern. -/
def boundedKernelForbiddenNormalizedPatternEdgeFactor
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S) : ℂ :=
  if BoundedKernelForbiddenPatternForcesEdge J e then
    q.2 * boundedKernelFixedLengthEdgeFactor M hM K e
      (boundedKernelForbiddenPatternLength J e) q x
  else
    boundedKernelNormalizedEdgeFactor M hM K.shape x e q

theorem boundedKernelForbiddenNormalizedPatternEdgeFactor_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (x : Fin K.shape.1.val → S) :
    AnalyticAt ℂ
      (fun q ↦ boundedKernelForbiddenNormalizedPatternEdgeFactor
        M hM K J e q x) (0, 0) := by
  classical
  unfold boundedKernelForbiddenNormalizedPatternEdgeFactor
  split_ifs
  · exact analyticAt_snd.mul
      (boundedKernelFixedLengthEdgeFactor_analytic M hM K e
        (boundedKernelForbiddenPatternLength J e) x)
  · exact boundedKernelNormalizedEdgeFactor_analytic M hM K.shape x e

theorem boundedKernelForbiddenNormalizedPatternEdgeFactor_eq_X_mul_raw
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (x : Fin K.shape.1.val → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      boundedKernelForbiddenNormalizedPatternEdgeFactor M hM K J e q x =
        q.2 * boundedKernelForbiddenRawPatternEdgeFactor M hM K J e q x := by
  filter_upwards
    [boundedNormalizedPathKernel_eq_smul_pathResolventKernel M hM] with q hq
  intro hX
  classical
  by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
  · simp [boundedKernelForbiddenNormalizedPatternEdgeFactor,
      boundedKernelForbiddenRawPatternEdgeFactor, he]
  · unfold boundedKernelForbiddenNormalizedPatternEdgeFactor
      boundedKernelForbiddenRawPatternEdgeFactor
    rw [if_neg he, if_neg he]
    have hfun := congrArg
      (fun f : C(S × S, ℂ) ↦
        f (x (boundedKernelOrderedEndpoints K.shape e).1,
          x (boundedKernelOrderedEndpoints K.shape e).2)) (hq hX)
    simpa only [boundedKernelNormalizedEdgeFactor,
      ContinuousMap.smul_apply, smul_eq_mul] using hfun

/-- Raw simultaneous witness intersection. -/
def boundedKernelForbiddenRawIntersection
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  if BoundedKernelForbiddenPatternCompatible J then
    boundedKernelBranchProfileProduct M hM K.shape x q *
      ∏ e : Fin K.shape.2.1.val,
        boundedKernelForbiddenRawPatternEdgeFactor M hM K J e q x
  else 0

/-- Pole-removed simultaneous witness intersection. -/
def boundedKernelForbiddenNormalizedIntersection
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  if BoundedKernelForbiddenPatternCompatible J then
    boundedKernelBranchProfileProduct M hM K.shape x q *
      ∏ e : Fin K.shape.2.1.val,
        boundedKernelForbiddenNormalizedPatternEdgeFactor M hM K J e q x
  else 0

theorem boundedKernelForbiddenNormalizedIntersection_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (x : Fin K.shape.1.val → S) :
    AnalyticAt ℂ (fun q ↦
      boundedKernelForbiddenNormalizedIntersection M hM K J q x)
      (0, 0) := by
  classical
  unfold boundedKernelForbiddenNormalizedIntersection
  split_ifs
  · exact (boundedKernelBranchProfileProduct_analytic M hM K.shape x).mul
      ((Finset.univ : Finset (Fin K.shape.2.1.val)).analyticAt_fun_prod
        (fun e _ ↦
          boundedKernelForbiddenNormalizedPatternEdgeFactor_analytic
            M hM K J e x))
  · exact analyticAt_const

theorem boundedKernelForbiddenNormalizedIntersection_axis
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (hJ : J.Nonempty) (g : C(S, ℂ)) (x : Fin K.shape.1.val → S) :
    boundedKernelForbiddenNormalizedIntersection M hM K J (g, 0) x = 0 := by
  classical
  by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
  · obtain ⟨e, he⟩ := boundedKernelForbiddenPattern_exists_forcedEdge hJ
    have hedge :
        boundedKernelForbiddenNormalizedPatternEdgeFactor
          M hM K J e (g, 0) x = 0 := by
      simp [boundedKernelForbiddenNormalizedPatternEdgeFactor, he]
    unfold boundedKernelForbiddenNormalizedIntersection
    rw [if_pos hcompat, Finset.prod_eq_zero (Finset.mem_univ e) hedge]
    simp
  · simp [boundedKernelForbiddenNormalizedIntersection, hcompat]

theorem boundedKernelForbiddenNormalizedIntersection_eq_pow_mul_raw
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (x : Fin K.shape.1.val → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      boundedKernelForbiddenNormalizedIntersection M hM K J q x =
        q.2 ^ K.shape.2.1.val *
          boundedKernelForbiddenRawIntersection M hM K J q x := by
  have hall :
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        ∀ e : Fin K.shape.2.1.val, q.2 ≠ 0 →
          boundedKernelForbiddenNormalizedPatternEdgeFactor
              M hM K J e q x =
            q.2 * boundedKernelForbiddenRawPatternEdgeFactor
              M hM K J e q x := by
    rw [Filter.eventually_all]
    intro e
    exact boundedKernelForbiddenNormalizedPatternEdgeFactor_eq_X_mul_raw
      M hM K J e x
  filter_upwards [hall] with q hq
  intro hX
  classical
  by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
  · unfold boundedKernelForbiddenNormalizedIntersection
      boundedKernelForbiddenRawIntersection
    rw [if_pos hcompat, if_pos hcompat]
    simp_rw [hq _ hX]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  · simp [boundedKernelForbiddenNormalizedIntersection,
      boundedKernelForbiddenRawIntersection, hcompat]

/-- Finite inclusion--exclusion correction on the raw resolvent scale. -/
def boundedKernelRawForbiddenCorrection
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ := by
  letI := boundedKernelForbiddenLengthWitnessFintype K
  exact ∑ J ∈ (Finset.univ :
      Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
        Finset.Nonempty,
    (-1 : ℂ) ^ (J.card + 1) *
      boundedKernelForbiddenRawIntersection M hM K J q x

/-- The same finite correction after removing one pole from every kernel
edge. -/
def boundedKernelNormalizedForbiddenCorrection
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ := by
  letI := boundedKernelForbiddenLengthWitnessFintype K
  exact ∑ J ∈ (Finset.univ :
      Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
        Finset.Nonempty,
    (-1 : ℂ) ^ (J.card + 1) *
      boundedKernelForbiddenNormalizedIntersection M hM K J q x

theorem boundedKernelNormalizedForbiddenCorrection_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (x : Fin K.shape.1.val → S) :
    AnalyticAt ℂ (fun q ↦
      boundedKernelNormalizedForbiddenCorrection M hM K q x) (0, 0) := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  unfold boundedKernelNormalizedForbiddenCorrection
  let s := (Finset.univ :
    Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
      Finset.Nonempty
  let F : Finset (BoundedKernelForbiddenLengthWitness K) →
      (C(S, ℂ) × ℂ → ℂ) := fun J q ↦
    (-1 : ℂ) ^ (J.card + 1) *
      boundedKernelForbiddenNormalizedIntersection M hM K J q x
  change AnalyticAt ℂ
    (fun q : C(S, ℂ) × ℂ ↦ Finset.sum s (fun J ↦ F J q)) (0, 0)
  have hsum : AnalyticAt ℂ (Finset.sum s F) (0, 0) := by
    apply Finset.analyticAt_sum
    intro J hJ
    exact analyticAt_const.mul
      (boundedKernelForbiddenNormalizedIntersection_analytic M hM K J x)
  have hfun : Finset.sum s F =
      (fun q : C(S, ℂ) × ℂ ↦ Finset.sum s (fun J ↦ F J q)) := by
    funext q
    exact Finset.sum_apply q s F
  rw [← hfun]
  exact hsum

theorem boundedKernelNormalizedForbiddenCorrection_axis
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (g : C(S, ℂ)) (x : Fin K.shape.1.val → S) :
    boundedKernelNormalizedForbiddenCorrection M hM K (g, 0) x = 0 := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  unfold boundedKernelNormalizedForbiddenCorrection
  apply Finset.sum_eq_zero
  intro J hJ
  have hne : J.Nonempty := (Finset.mem_filter.mp hJ).2
  rw [boundedKernelForbiddenNormalizedIntersection_axis M hM K J hne g x,
    mul_zero]

theorem boundedKernelNormalizedForbiddenCorrection_eq_pow_mul_raw
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (x : Fin K.shape.1.val → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      boundedKernelNormalizedForbiddenCorrection M hM K q x =
        q.2 ^ K.shape.2.1.val *
          boundedKernelRawForbiddenCorrection M hM K q x := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  have hall :
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        ∀ J : Finset (BoundedKernelForbiddenLengthWitness K),
          q.2 ≠ 0 →
          boundedKernelForbiddenNormalizedIntersection M hM K J q x =
            q.2 ^ K.shape.2.1.val *
              boundedKernelForbiddenRawIntersection M hM K J q x := by
    rw [Filter.eventually_all]
    intro J
    exact boundedKernelForbiddenNormalizedIntersection_eq_pow_mul_raw
      M hM K J x
  filter_upwards [hall] with q hq
  intro hX
  unfold boundedKernelNormalizedForbiddenCorrection
    boundedKernelRawForbiddenCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [hq J hX]
  ring

/-! ## Literal all-length assignment sums -/

/-- Literal unrestricted all-length path/profile integrand. -/
def boundedKernelLiteralUnrestrictedAssignmentIntegrand
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  boundedKernelBranchProfileProduct M hM K.shape x q *
    ∑' l : Fin K.shape.2.1.val → ℕ,
      ∏ e : Fin K.shape.2.1.val,
        profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
          (x (boundedKernelOrderedEndpoints K.shape e).1)
          (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)

/-- Literal admissible all-length path/profile integrand.  The predicate is
exactly the one encoded by `BoundedKernelLengthProfile`. -/
def boundedKernelLiteralAdmissibleAssignmentIntegrand
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  boundedKernelBranchProfileProduct M hM K.shape x q *
    ∑' l : Fin K.shape.2.1.val → ℕ,
      if BoundedKernelLengthAssignment.IsAdmissible K
          (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin K.shape.2.1.val,
          profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
            (x (boundedKernelOrderedEndpoints K.shape e).1)
            (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
      else 0

/-- Literal forbidden all-length path/profile integrand. -/
def boundedKernelLiteralForbiddenAssignmentIntegrand
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  boundedKernelBranchProfileProduct M hM K.shape x q *
    ∑' l : Fin K.shape.2.1.val → ℕ,
      if ∃ w : BoundedKernelForbiddenLengthWitness K,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin K.shape.2.1.val,
          profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
            (x (boundedKernelOrderedEndpoints K.shape e).1)
            (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
      else 0

private theorem boundedKernelAssignmentProduct_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    Summable (fun l : Fin K.shape.2.1.val → ℕ ↦
      ∏ e : Fin K.shape.2.1.val,
        profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
          (x (boundedKernelOrderedEndpoints K.shape e).1)
          (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)) := by
  exact (summable_finFunction_prod_and_tsum
    (fun e n ↦ profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2) n)
    (fun e ↦ summable_profilePathEdgeCoefficient M hM
      (NBKAS_MPR.profile M hM q) r hr hr1 hprofile _ _)).1

theorem boundedKernelCoreResolventIntegrand_eq_literalUnrestricted
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    boundedKernelCoreResolventIntegrand M hM K.shape x q =
      boundedKernelLiteralUnrestrictedAssignmentIntegrand M hM K q x := by
  unfold boundedKernelCoreResolventIntegrand
    boundedKernelLiteralUnrestrictedAssignmentIntegrand
  apply congrArg (fun z : ℂ ↦
    boundedKernelBranchProfileProduct M hM K.shape x q * z)
  rw [(summable_finFunction_prod_and_tsum
    (fun e n ↦ profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2) n)
    (fun e ↦ summable_profilePathEdgeCoefficient M hM
      (NBKAS_MPR.profile M hM q) r hr hr1 hprofile _ _)).2]
  apply Finset.prod_congr rfl
  intro e _
  exact tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
    M hM q r hr hr1 hprofile _ _ |>.symm

theorem boundedKernelLiteralAdmissible_add_forbidden_eq_unrestricted
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    boundedKernelLiteralAdmissibleAssignmentIntegrand M hM K q x +
        boundedKernelLiteralForbiddenAssignmentIntegrand M hM K q x =
      boundedKernelLiteralUnrestrictedAssignmentIntegrand M hM K q x := by
  classical
  let B : (Fin K.shape.2.1.val → ℕ) → ℂ := fun l ↦
    ∏ e : Fin K.shape.2.1.val,
      profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
  let A : Set (Fin K.shape.2.1.val → ℕ) := {l |
    BoundedKernelLengthAssignment.IsAdmissible K
      (Finsupp.equivFunOnFinite.symm l)}
  let F : Set (Fin K.shape.2.1.val → ℕ) := {l |
    ∃ w : BoundedKernelForbiddenLengthWitness K,
      w.Occurs (Finsupp.equivFunOnFinite.symm l)}
  have hB : Summable B :=
    boundedKernelAssignmentProduct_summable M hM K q x r hr hr1 hprofile
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
  unfold boundedKernelLiteralAdmissibleAssignmentIntegrand
    boundedKernelLiteralForbiddenAssignmentIntegrand
    boundedKernelLiteralUnrestrictedAssignmentIntegrand
  rw [← mul_add]
  apply congrArg (fun z : ℂ ↦
    boundedKernelBranchProfileProduct M hM K.shape x q * z)
  change (∑' l, A.indicator B l) + (∑' l, F.indicator B l) = ∑' l, B l
  rw [← hA.tsum_add hF]
  exact tsum_congr hterm

/-! ## The finite correction is the literal forbidden subseries -/

/-- The one-edge coefficient sequence with a pattern-forced length frozen. -/
def boundedKernelForbiddenPatternEdgeCoefficient
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S) (n : ℕ) : ℂ :=
  if BoundedKernelForbiddenPatternForcesEdge J e then
    if n = boundedKernelForbiddenPatternLength J e then
      profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) n
    else 0
  else
    profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2) n

theorem boundedKernelForbiddenPatternEdgeCoefficient_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    Summable (boundedKernelForbiddenPatternEdgeCoefficient
      M hM K J e q x) := by
  classical
  by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
  · let c : ℕ → ℂ := fun n ↦
      profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) n
    have hs := (hasSum_ite_eq (boundedKernelForbiddenPatternLength J e)
      (c (boundedKernelForbiddenPatternLength J e))).summable
    exact hs.congr (fun n ↦ by
      by_cases hn : n = boundedKernelForbiddenPatternLength J e
      · subst n
        simp [boundedKernelForbiddenPatternEdgeCoefficient, he, c]
      · simp [boundedKernelForbiddenPatternEdgeCoefficient, he, hn, c])
  · exact (summable_profilePathEdgeCoefficient M hM
      (NBKAS_MPR.profile M hM q) r hr hr1 hprofile
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2)).congr
        (fun n ↦ by
          simp [boundedKernelForbiddenPatternEdgeCoefficient, he])

theorem tsum_boundedKernelForbiddenPatternEdgeCoefficient
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    (∑' n : ℕ,
        boundedKernelForbiddenPatternEdgeCoefficient M hM K J e q x n) =
      boundedKernelForbiddenRawPatternEdgeFactor M hM K J e q x := by
  classical
  by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
  · let c : ℕ → ℂ := fun n ↦
      profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) n
    calc
      (∑' n : ℕ,
          boundedKernelForbiddenPatternEdgeCoefficient M hM K J e q x n) =
          c (boundedKernelForbiddenPatternLength J e) := by
        calc
          _ = ∑' n : ℕ,
              if n = boundedKernelForbiddenPatternLength J e then
                c (boundedKernelForbiddenPatternLength J e) else 0 := by
            apply tsum_congr
            intro n
            by_cases hn : n = boundedKernelForbiddenPatternLength J e
            · subst n
              simp [boundedKernelForbiddenPatternEdgeCoefficient, he, c]
            · simp [boundedKernelForbiddenPatternEdgeCoefficient, he, hn, c]
          _ = c (boundedKernelForbiddenPatternLength J e) :=
            (hasSum_ite_eq (boundedKernelForbiddenPatternLength J e)
              (c (boundedKernelForbiddenPatternLength J e))).tsum_eq
      _ = boundedKernelForbiddenRawPatternEdgeFactor M hM K J e q x := by
        simp [boundedKernelForbiddenRawPatternEdgeFactor, he, c]
  · rw [show (∑' n : ℕ,
        boundedKernelForbiddenPatternEdgeCoefficient M hM K J e q x n) =
        ∑' n : ℕ, profilePathEdgeCoefficient M.bjrModel
          (NBKAS_MPR.profile M hM q)
          (x (boundedKernelOrderedEndpoints K.shape e).1)
          (x (boundedKernelOrderedEndpoints K.shape e).2) n by
      apply tsum_congr
      intro n
      simp [boundedKernelForbiddenPatternEdgeCoefficient, he]]
    rw [tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
      M hM q r hr hr1 hprofile]
    simp [boundedKernelForbiddenRawPatternEdgeFactor, he]

/-- Pattern-restricted table weight; incompatible intersections are empty. -/
def boundedKernelForbiddenPatternAssignmentWeight
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (l : Fin K.shape.2.1.val → ℕ) : ℂ :=
  if BoundedKernelForbiddenPatternCompatible J then
    ∏ e : Fin K.shape.2.1.val,
      boundedKernelForbiddenPatternEdgeCoefficient M hM K J e q x (l e)
  else 0

theorem boundedKernelForbiddenPatternAssignmentWeight_eq_occurrenceIndicator
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (l : Fin K.shape.2.1.val → ℕ) :
    boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l =
      if ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin K.shape.2.1.val,
          profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
            (x (boundedKernelOrderedEndpoints K.shape e).1)
            (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
      else 0 := by
  classical
  by_cases hall :
      ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l)
  · obtain ⟨hcompat, hlength⟩ :=
      (boundedKernelForbiddenPattern_all_occurs_iff J l).mp hall
    rw [if_pos hall]
    unfold boundedKernelForbiddenPatternAssignmentWeight
    rw [if_pos hcompat]
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
    · simp [boundedKernelForbiddenPatternEdgeCoefficient, he,
        hlength e he]
    · simp [boundedKernelForbiddenPatternEdgeCoefficient, he]
  · rw [if_neg hall]
    unfold boundedKernelForbiddenPatternAssignmentWeight
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
      simp [boundedKernelForbiddenPatternEdgeCoefficient, he, hne]
    · simp [hcompat]

theorem boundedKernelForbiddenPatternAssignmentWeight_summable
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    Summable (boundedKernelForbiddenPatternAssignmentWeight
      M hM K J q x) := by
  classical
  by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
  · exact (summable_finFunction_prod_and_tsum
        (fun e n ↦ boundedKernelForbiddenPatternEdgeCoefficient
          M hM K J e q x n)
        (fun e ↦ boundedKernelForbiddenPatternEdgeCoefficient_summable
          M hM K J e q x r hr hr1 hprofile)).1.congr
      (fun l ↦ by
        simp [boundedKernelForbiddenPatternAssignmentWeight, hcompat])
  · exact summable_zero.congr
      (fun l ↦ by
        simp [boundedKernelForbiddenPatternAssignmentWeight, hcompat])

theorem tsum_boundedKernelForbiddenPatternAssignmentWeight
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r)
    (hcompat : BoundedKernelForbiddenPatternCompatible J) :
    (∑' l : Fin K.shape.2.1.val → ℕ,
        boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l) =
      ∏ e : Fin K.shape.2.1.val,
        boundedKernelForbiddenRawPatternEdgeFactor M hM K J e q x := by
  classical
  simp only [boundedKernelForbiddenPatternAssignmentWeight, hcompat, if_true]
  rw [(summable_finFunction_prod_and_tsum
    (fun e n ↦ boundedKernelForbiddenPatternEdgeCoefficient
      M hM K J e q x n)
    (fun e ↦ boundedKernelForbiddenPatternEdgeCoefficient_summable
      M hM K J e q x r hr hr1 hprofile)).2]
  apply Finset.prod_congr rfl
  intro e _
  exact tsum_boundedKernelForbiddenPatternEdgeCoefficient
    M hM K J e q x r hr hr1 hprofile

theorem boundedKernelRawForbiddenCorrection_eq_literalForbidden
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    boundedKernelRawForbiddenCorrection M hM K q x =
      boundedKernelLiteralForbiddenAssignmentIntegrand M hM K q x := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  classical
  let P := (Finset.univ :
    Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
      Finset.Nonempty
  let B : (Fin K.shape.2.1.val → ℕ) → ℂ := fun l ↦
    ∏ e : Fin K.shape.2.1.val,
      profilePathEdgeCoefficient M.bjrModel (NBKAS_MPR.profile M hM q)
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
  have hJsum (J : Finset (BoundedKernelForbiddenLengthWitness K)) :
      boundedKernelForbiddenRawIntersection M hM K J q x =
        boundedKernelBranchProfileProduct M hM K.shape x q *
          ∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelForbiddenPatternAssignmentWeight
              M hM K J q x l := by
    unfold boundedKernelForbiddenRawIntersection
    by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
    · rw [if_pos hcompat,
          tsum_boundedKernelForbiddenPatternAssignmentWeight
            M hM K J q x r hr hr1 hprofile hcompat]
    · rw [if_neg hcompat]
      have hzero :
          (∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelForbiddenPatternAssignmentWeight
              M hM K J q x l) = 0 := by
        simp [boundedKernelForbiddenPatternAssignmentWeight, hcompat]
      rw [hzero, mul_zero]
  have hsumJ (J : Finset (BoundedKernelForbiddenLengthWitness K)) :
      Summable (fun l : Fin K.shape.2.1.val → ℕ ↦
        (-1 : ℂ) ^ (J.card + 1) *
          boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l) :=
    (boundedKernelForbiddenPatternAssignmentWeight_summable
      M hM K J q x r hr hr1 hprofile).mul_left _
  unfold boundedKernelRawForbiddenCorrection
    boundedKernelLiteralForbiddenAssignmentIntegrand
  simp_rw [hJsum]
  rw [show (∑ J ∈ P, (-1 : ℂ) ^ (J.card + 1) *
        (boundedKernelBranchProfileProduct M hM K.shape x q *
          ∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l)) =
      boundedKernelBranchProfileProduct M hM K.shape x q *
        ∑ J ∈ P, (-1 : ℂ) ^ (J.card + 1) *
          ∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J _
      ring]
  apply congrArg (fun z : ℂ ↦
    boundedKernelBranchProfileProduct M hM K.shape x q * z)
  have hscale (J : Finset (BoundedKernelForbiddenLengthWitness K)) :
      (-1 : ℂ) ^ (J.card + 1) *
          ∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l =
        ∑' l : Fin K.shape.2.1.val → ℕ,
          (-1 : ℂ) ^ (J.card + 1) *
            boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l :=
    ((boundedKernelForbiddenPatternAssignmentWeight_summable
      M hM K J q x r hr hr1 hprofile).tsum_mul_left _).symm
  have hswap := Summable.tsum_finsetSum
    (s := P)
    (f := fun J l ↦ (-1 : ℂ) ^ (J.card + 1) *
      boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l)
    (fun J _ ↦ hsumJ J)
  simp_rw [hscale]
  rw [← hswap]
  apply tsum_congr
  intro l
  simp_rw [boundedKernelForbiddenPatternAssignmentWeight_eq_occurrenceIndicator]
  convert boundedKernelForbidden_inclusionExclusion_assignment K l (B l) using 1 <;>
    simp only [P, B]
  · apply Finset.sum_congr rfl
    intro J _hJ
    by_cases hocc : ∀ w ∈ J,
        w.Occurs (Finsupp.equivFunOnFinite.symm l) <;> simp_all
  · by_cases hex : ∃ w : BoundedKernelForbiddenLengthWitness K,
        w.Occurs (Finsupp.equivFunOnFinite.symm l) <;> simp_all

/-- The literal admissible all-length series is exactly the marked-path
resolvent product minus the finite forbidden-pattern correction. -/
theorem boundedKernelLiteralAdmissible_eq_resolvent_sub_finiteCorrection
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    boundedKernelLiteralAdmissibleAssignmentIntegrand M hM K q x =
      boundedKernelCoreResolventIntegrand M hM K.shape x q -
        boundedKernelRawForbiddenCorrection M hM K q x := by
  have hsplit := boundedKernelLiteralAdmissible_add_forbidden_eq_unrestricted
    M hM K q x r hr hr1 hprofile
  rw [← boundedKernelCoreResolventIntegrand_eq_literalUnrestricted
      M hM K q x r hr hr1 hprofile,
    ← boundedKernelRawForbiddenCorrection_eq_literalForbidden
      M hM K q x r hr hr1 hprofile] at hsplit
  exact eq_sub_of_add_eq hsplit

/-! ## Cubic normalization and the extra fold coordinate -/

/-- Pole-removed admissible amplitude for one bounded kernel. -/
def boundedKernelAdmissibleNormalizedCoreIntegrand
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  boundedKernelNormalizedCoreIntegrand M hM K.shape x q -
    boundedKernelNormalizedForbiddenCorrection M hM K q x

theorem boundedKernelAdmissibleNormalizedCoreIntegrand_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (x : Fin K.shape.1.val → S) :
    AnalyticAt ℂ (fun q ↦
      boundedKernelAdmissibleNormalizedCoreIntegrand M hM K q x)
      (0, 0) :=
  (boundedKernelNormalizedCoreIntegrand_analytic M hM K.shape x).sub
    (boundedKernelNormalizedForbiddenCorrection_analytic M hM K x)

/-- On the punctured strict-subcritical germ, the analytic amplitude is the
edge-pole normalization of the literal admissible assignment series. -/
theorem boundedKernelAdmissibleNormalized_eq_pow_mul_literal
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (x : Fin K.shape.1.val → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      ∀ r : ℝ, 0 ≤ r → r < 1 →
        (∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) → q.2 ≠ 0 →
        boundedKernelAdmissibleNormalizedCoreIntegrand M hM K q x =
          q.2 ^ K.shape.2.1.val *
            boundedKernelLiteralAdmissibleAssignmentIntegrand
              M hM K q x := by
  filter_upwards
    [boundedKernelNormalizedCoreIntegrand_eq_pow_mul_resolvent
      M hM K.shape x,
     boundedKernelNormalizedForbiddenCorrection_eq_pow_mul_raw
      M hM K x] with q hcore hforbidden
  intro r hr hr1 hprofile hX
  unfold boundedKernelAdmissibleNormalizedCoreIntegrand
  rw [hcore hX, hforbidden hX,
    boundedKernelLiteralAdmissible_eq_resolvent_sub_finiteCorrection
      M hM K q x r hr hr1 hprofile]
  ring

/-- Canonical jointly analytic remainder after cubic normalization of one
strictly noncubic bounded kernel. -/
def boundedKernelAdmissibleCubicDefectRemainder
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  q.2 ^ (3 * ell - K.shape.2.1.val - 1) *
    boundedKernelAdmissibleNormalizedCoreIntegrand M hM K q x

theorem boundedKernelAdmissibleCubicDefectRemainder_analytic
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (x : Fin K.shape.1.val → S) :
    AnalyticAt ℂ (fun q ↦
      boundedKernelAdmissibleCubicDefectRemainder M hM K q x)
      (0, 0) :=
  (analyticAt_snd.pow (3 * ell - K.shape.2.1.val - 1)).mul
    (boundedKernelAdmissibleNormalizedCoreIntegrand_analytic M hM K x)

/-- A strict edge deficit leaves one explicit fold coordinate after cubic
normalization, on the whole joint parameter space. -/
theorem boundedKernel_cubicNormalizedAdmissible_eq_X_mul_remainder
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (hedges : K.shape.2.1.val < 3 * ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    q.2 ^ (3 * ell - K.shape.2.1.val) *
        boundedKernelAdmissibleNormalizedCoreIntegrand M hM K q x =
      q.2 * boundedKernelAdmissibleCubicDefectRemainder M hM K q x := by
  have hsucc :
      3 * ell - K.shape.2.1.val - 1 + 1 =
        3 * ell - K.shape.2.1.val := by
    omega
  unfold boundedKernelAdmissibleCubicDefectRemainder
  have hpow :
      q.2 ^ (3 * ell - K.shape.2.1.val) =
        q.2 ^ (3 * ell - K.shape.2.1.val - 1) * q.2 := by
    conv_lhs => rw [← hsucc, pow_succ]
  rw [hpow]
  ring

/-- Specialized no-interface statement for one fixed connected noncubic
bounded kernel.  It is intentionally a kernel/length-profile theorem, not a
claim about the total graph series. -/
theorem connectedNoncubicKernel_cubicNormalizedAdmissible_eq_X_mul
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (q : C(S, ℂ) × ℂ)
    (x : Fin K.1.toLabelledBoundedKernel.shape.1.val → S) :
    q.2 ^ (3 * ell -
        K.1.toLabelledBoundedKernel.shape.2.1.val) *
        boundedKernelAdmissibleNormalizedCoreIntegrand M hM
          K.1.toLabelledBoundedKernel q x =
      q.2 * boundedKernelAdmissibleCubicDefectRemainder M hM
        K.1.toLabelledBoundedKernel q x :=
  boundedKernel_cubicNormalizedAdmissible_eq_X_mul_remainder
    M hM K.1.toLabelledBoundedKernel K.2 q x

/-- On the punctured strict-subcritical germ, the preceding identity is the
literal cubic normalization `X^(3*ell)` of the admissible all-length
assignment series. -/
theorem connectedNoncubicKernel_literal_cubicNormalization
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (x : Fin K.1.toLabelledBoundedKernel.shape.1.val → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      ∀ r : ℝ, 0 ≤ r → r < 1 →
        (∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) → q.2 ≠ 0 →
        q.2 ^ (3 * ell) *
            boundedKernelLiteralAdmissibleAssignmentIntegrand M hM
              K.1.toLabelledBoundedKernel q x =
          q.2 * boundedKernelAdmissibleCubicDefectRemainder M hM
            K.1.toLabelledBoundedKernel q x := by
  filter_upwards
    [boundedKernelAdmissibleNormalized_eq_pow_mul_literal
      M hM K.1.toLabelledBoundedKernel x] with q hnormalized
  intro r hr hr1 hprofile hX
  let B := K.1.toLabelledBoundedKernel
  have hsum :
      3 * ell = (3 * ell - B.shape.2.1.val) + B.shape.2.1.val := by
    omega
  have hpow :
      q.2 ^ (3 * ell) =
        q.2 ^ (3 * ell - B.shape.2.1.val) * q.2 ^ B.shape.2.1.val := by
    calc
      q.2 ^ (3 * ell) =
          q.2 ^ ((3 * ell - B.shape.2.1.val) + B.shape.2.1.val) :=
        congrArg (fun n : ℕ ↦ q.2 ^ n) hsum
      _ = q.2 ^ (3 * ell - B.shape.2.1.val) *
          q.2 ^ B.shape.2.1.val := pow_add _ _ _
  calc
    q.2 ^ (3 * ell) *
        boundedKernelLiteralAdmissibleAssignmentIntegrand M hM B q x =
      q.2 ^ (3 * ell - B.shape.2.1.val) *
        (q.2 ^ B.shape.2.1.val *
          boundedKernelLiteralAdmissibleAssignmentIntegrand M hM B q x) := by
        rw [hpow]
        ring
    _ = q.2 ^ (3 * ell - B.shape.2.1.val) *
        boundedKernelAdmissibleNormalizedCoreIntegrand M hM B q x := by
      rw [← hnormalized r hr hr1 hprofile hX]
    _ = q.2 * boundedKernelAdmissibleCubicDefectRemainder M hM B q x :=
      boundedKernel_cubicNormalizedAdmissible_eq_X_mul_remainder
        M hM B K.2 q x


end PerronWright.FiniteIrreducibleKernelAmplitude
