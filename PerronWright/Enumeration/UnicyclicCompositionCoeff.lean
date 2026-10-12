import PerronWright.Enumeration.CoreAttachmentGlobalWeightSum
import PerronWright.Enumeration.FieldRootedTreeFormal
import PerronWright.Enumeration.UnicyclicCycleWeightTrace

/-!
# The genuine unicyclic composition coefficient

This file deliberately keeps the composition object independent of the
core/attachment formula.  A `q`-vertex core is evaluated at a genuine
`C(S, ℂ)`-valued rooted-tree power series by mapping that series to each core
type coordinate, multiplying the resulting `q` scalar series, and integrating
the fixed core edge weight coefficientwise.  The external factor `X^q`
restores the root vertex carried by every rooted-tree profile.

The main target is therefore not a renamed attachment coefficient:

`complexFieldConnectedWeight g k 1 / k!`

is identified with the size-`k` coefficient of the above literal profile
composition, evaluated at `FieldRootedTree.series M g`.  The proof passes
through the proved rooted-tree formal equation, and the only arithmetic
normalization is the exact identity

`choose k q * n! / k! = 1 / q!`, for `q + n = k`.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private def continuousMapComplexEvalRingHom (x : S) :
    C(S, ℂ) →+* ℂ :=
  (Pi.evalRingHom (fun _ : S ↦ ℂ) x).comp ContinuousMap.coeFnRingHom

/-- Remove the compulsory leading `X` from a rooted-tree profile series. -/
def rootedTreeTail (T : PowerSeries C(S, ℂ)) :
    PowerSeries C(S, ℂ) :=
  PowerSeries.mk fun n ↦ PowerSeries.coeff (n + 1) T

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem rootedTreeTail_coeff
    (T : PowerSeries C(S, ℂ)) (n : ℕ) :
    PowerSeries.coeff n (rootedTreeTail T) =
      PowerSeries.coeff (n + 1) T := by
  rw [rootedTreeTail, PowerSeries.coeff_mk]

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
theorem X_mul_rootedTreeTail
    (T : PowerSeries C(S, ℂ))
    (hT0 : PowerSeries.constantCoeff T = 0) :
    PowerSeries.X * rootedTreeTail T = T := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simpa only [PowerSeries.coeff_zero_X_mul,
        PowerSeries.coeff_zero_eq_constantCoeff] using hT0.symm
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, rootedTreeTail_coeff]

/-- The genuine field-rooted tree equation after cancelling its compulsory
leading `X`. -/
private theorem rootedTreeTail_series_eq
    (M : CompactBJRModel S) (g : C(S, ℂ)) :
    rootedTreeTail (FieldRootedTree.series M g) =
      PowerSeries.C (FieldRootedTree.vertexFactor M g) *
        PowerSeries.subst
          (M.complexKernelActionPowerSeries (FieldRootedTree.series M g))
          (PowerSeries.exp C(S, ℂ)) := by
  apply PowerSeries.X_mul_injective
  calc
    PowerSeries.X * rootedTreeTail (FieldRootedTree.series M g) =
        FieldRootedTree.series M g := by
      apply X_mul_rootedTreeTail
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]
      exact FieldRootedTree.series_coeff_zero M g
    _ = FieldRootedTree.formalRHS M g (FieldRootedTree.series M g) :=
      FieldRootedTree.series_eq_formalRHS M g
    _ = PowerSeries.X *
        (PowerSeries.C (FieldRootedTree.vertexFactor M g) *
          PowerSeries.subst
            (M.complexKernelActionPowerSeries (FieldRootedTree.series M g))
            (PowerSeries.exp C(S, ℂ))) := by
      rfl

/-- Substitution of a zero-constant series into the formal exponential has
constant coefficient one. -/
private theorem subst_exp_coeff_zero
    (A : PowerSeries ℂ) (hA0 : PowerSeries.constantCoeff A = 0) :
    PowerSeries.coeff 0
        (PowerSeries.subst A (PowerSeries.exp ℂ)) = 1 := by
  have hA : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  rw [PowerSeries.coeff_subst' hA (PowerSeries.exp ℂ) 0,
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_pow, hA0, zero_pow hd, smul_zero]

/-- Uniqueness for the scalar formal differential equation `F' = F D`.
This is the coefficientwise device needed to prove the additive law for the
formal exponential after substitution. -/
private theorem powerSeries_eq_of_derivative_eq_mul
    (F G D : PowerSeries ℂ)
    (hF : PowerSeries.derivative ℂ F = F * D)
    (hG : PowerSeries.derivative ℂ G = G * D)
    (hzero : PowerSeries.constantCoeff F =
      PowerSeries.constantCoeff G) :
    F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hzero
      | succ m =>
          have hprod :
              PowerSeries.coeff m (F * D) =
                PowerSeries.coeff m (G * D) := by
            rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
            apply Finset.sum_congr rfl
            intro ij hij
            apply congrArg (fun z : ℂ ↦ z * PowerSeries.coeff ij.2 D)
            apply ih ij.1
            have hsum := Finset.mem_antidiagonal.mp hij
            omega
          have hFc := congrArg (PowerSeries.coeff m) hF
          have hGc := congrArg (PowerSeries.coeff m) hG
          rw [PowerSeries.coeff_derivative] at hFc hGc
          have heq :
              PowerSeries.coeff (m + 1) F * ((m : ℂ) + 1) =
                PowerSeries.coeff (m + 1) G * ((m : ℂ) + 1) :=
            hFc.trans (hprod.trans hGc.symm)
          have hm : (m : ℂ) + 1 ≠ 0 := by
            exact_mod_cast Nat.succ_ne_zero m
          exact mul_right_cancel₀ hm heq

/-- The ordinary additive law for the substituted formal exponential. -/
private theorem subst_exp_add
    (A B : PowerSeries ℂ)
    (hA0 : PowerSeries.constantCoeff A = 0)
    (hB0 : PowerSeries.constantCoeff B = 0) :
    PowerSeries.subst A (PowerSeries.exp ℂ) *
        PowerSeries.subst B (PowerSeries.exp ℂ) =
      PowerSeries.subst (A + B) (PowerSeries.exp ℂ) := by
  let EA := PowerSeries.subst A (PowerSeries.exp ℂ)
  let EB := PowerSeries.subst B (PowerSeries.exp ℂ)
  let EAB := PowerSeries.subst (A + B) (PowerSeries.exp ℂ)
  let D := PowerSeries.derivative ℂ A + PowerSeries.derivative ℂ B
  have hA : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  have hB : PowerSeries.HasSubst B :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hB0
  have hAB0 : PowerSeries.constantCoeff (A + B) = 0 := by
    simp [hA0, hB0]
  have hAB : PowerSeries.HasSubst (A + B) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hAB0
  have hEA : PowerSeries.derivative ℂ EA =
      EA * PowerSeries.derivative ℂ A := by
    unfold EA
    rw [PowerSeries.derivative_subst hA, PowerSeries.derivative_exp]
  have hEB : PowerSeries.derivative ℂ EB =
      EB * PowerSeries.derivative ℂ B := by
    unfold EB
    rw [PowerSeries.derivative_subst hB, PowerSeries.derivative_exp]
  have hprod : PowerSeries.derivative ℂ (EA * EB) = (EA * EB) * D := by
    rw [(PowerSeries.derivative ℂ).leibniz, hEA, hEB]
    unfold D
    ring
  have hsum : PowerSeries.derivative ℂ EAB = EAB * D := by
    unfold EAB D
    rw [PowerSeries.derivative_subst hAB, PowerSeries.derivative_exp]
    simp only [map_add]
  have hzero : PowerSeries.constantCoeff (EA * EB) =
      PowerSeries.constantCoeff EAB := by
    rw [map_mul]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [show PowerSeries.coeff 0 EA = 1 by
          exact subst_exp_coeff_zero A hA0,
      show PowerSeries.coeff 0 EB = 1 by
          exact subst_exp_coeff_zero B hB0,
      show PowerSeries.coeff 0 EAB = 1 by
          exact subst_exp_coeff_zero (A + B) hAB0]
    exact one_mul 1
  exact powerSeries_eq_of_derivative_eq_mul (EA * EB) EAB D
    hprod hsum hzero

private theorem prod_subst_exp_eq_subst_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → PowerSeries ℂ)
    (hA0 : ∀ i, PowerSeries.constantCoeff (A i) = 0) :
    (∏ i : ι, PowerSeries.subst (A i) (PowerSeries.exp ℂ)) =
      PowerSeries.subst (∑ i : ι, A i) (PowerSeries.exp ℂ) := by
  classical
  suffices h : ∀ s : Finset ι,
      (∏ i ∈ s, PowerSeries.subst (A i) (PowerSeries.exp ℂ)) =
        PowerSeries.subst (∑ i ∈ s, A i) (PowerSeries.exp ℂ) by
    simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      ext n
      cases n with
      | zero =>
          rw [PowerSeries.coeff_one]
          exact (subst_exp_coeff_zero 0 (by simp)).symm
      | succ n =>
          simp [PowerSeries.subst_zero_eq_C_constantCoeff]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih]
      apply subst_exp_add
      · exact hA0 i
      · simp only [map_sum, hA0, Finset.sum_const_zero]

/-- Scalar rooted-tree tail at one prescribed type. -/
def rootedTreeTailAt (T : PowerSeries C(S, ℂ)) (x : S) :
    PowerSeries ℂ :=
  PowerSeries.map (continuousMapComplexEvalRingHom x) (rootedTreeTail T)

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem rootedTreeTailAt_coeff
    (T : PowerSeries C(S, ℂ)) (x : S) (n : ℕ) :
    PowerSeries.coeff n (rootedTreeTailAt T x) =
      PowerSeries.coeff (n + 1) T x := by
  simp only [rootedTreeTailAt, PowerSeries.coeff_map,
    rootedTreeTail_coeff, continuousMapComplexEvalRingHom,
    RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
    ContinuousMap.coeFnRingHom_apply]

private def rootedTreeKernelSeriesAt
    (M : CompactBJRModel S) (g : C(S, ℂ)) (x : S) : PowerSeries ℂ :=
  PowerSeries.map (continuousMapComplexEvalRingHom x)
    (M.complexKernelActionPowerSeries (FieldRootedTree.series M g))

@[simp] private theorem rootedTreeKernelSeriesAt_coeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) (x : S) (n : ℕ) :
    PowerSeries.coeff n (rootedTreeKernelSeriesAt M g x) =
      M.kernel.complexAction M.mu
        (PowerSeries.coeff n (FieldRootedTree.series M g)) x := by
  simp only [rootedTreeKernelSeriesAt, PowerSeries.coeff_map,
    continuousMapComplexEvalRingHom, RingHom.coe_comp, Function.comp_apply,
    Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply,
    CompactBJRModel.complexKernelActionPowerSeries_coeff,
    ContinuousKernel.complexActionCLM_apply]

private theorem rootedTreeKernelSeriesAt_constantCoeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) (x : S) :
    PowerSeries.constantCoeff (rootedTreeKernelSeriesAt M g x) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [rootedTreeKernelSeriesAt_coeff,
    FieldRootedTree.series_coeff_zero]
  have hzero := (M.kernel.complexActionCLM M.mu).map_zero
  exact congrArg (fun f : C(S, ℂ) ↦ f x) hzero

private theorem rootedTreeTailAt_series_eq
    (M : CompactBJRModel S) (g : C(S, ℂ)) (x : S) :
    rootedTreeTailAt (FieldRootedTree.series M g) x =
      PowerSeries.C (FieldRootedTree.vertexFactor M g x) *
        PowerSeries.subst (rootedTreeKernelSeriesAt M g x)
          (PowerSeries.exp ℂ) := by
  have hA0 : PowerSeries.constantCoeff
      (M.complexKernelActionPowerSeries (FieldRootedTree.series M g)) = 0 := by
    rw [M.complexKernelActionPowerSeries_constantCoeff,
      ← PowerSeries.coeff_zero_eq_constantCoeff,
      FieldRootedTree.series_coeff_zero, map_zero]
  have hA : PowerSeries.HasSubst
      (M.complexKernelActionPowerSeries (FieldRootedTree.series M g)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  have hsubst :
      PowerSeries.map (continuousMapComplexEvalRingHom x)
          (PowerSeries.subst
            (M.complexKernelActionPowerSeries (FieldRootedTree.series M g))
            (PowerSeries.exp C(S, ℂ))) =
        PowerSeries.subst
          (PowerSeries.map (continuousMapComplexEvalRingHom x)
            (M.complexKernelActionPowerSeries (FieldRootedTree.series M g)))
          (PowerSeries.exp ℂ) := by
    change MvPowerSeries.map (continuousMapComplexEvalRingHom x)
        (PowerSeries.subst
          (M.complexKernelActionPowerSeries (FieldRootedTree.series M g))
          (PowerSeries.exp C(S, ℂ))) = _
    rw [PowerSeries.map_subst hA
      (h := continuousMapComplexEvalRingHom x)
      (PowerSeries.exp C(S, ℂ)), PowerSeries.map_exp]
    congr 1
  unfold rootedTreeTailAt rootedTreeKernelSeriesAt
  rw [rootedTreeTail_series_eq M g, map_mul, PowerSeries.map_C]
  exact congrArg
    (fun E : PowerSeries ℂ ↦
      PowerSeries.C (FieldRootedTree.vertexFactor M g x) * E)
    hsubst

private theorem complexCoreBranchActionSeries_eq_sum_at
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q : ℕ}
    (roots : Fin q → S) :
    M.complexCoreBranchActionSeries g roots =
      ∑ i : Fin q, rootedTreeKernelSeriesAt M g (roots i) := by
  ext n
  rw [M.complexCoreBranchActionSeries_coeff]
  simp only [map_sum, rootedTreeKernelSeriesAt_coeff]
  apply Fintype.sum_congr
  intro i
  rw [M.complexKernelActionPowerSeries_coeff]
  rfl

private theorem prod_rootedTreeTailAt_series_eq
    (M : CompactBJRModel S) (g : C(S, ℂ)) {q : ℕ}
    (roots : Fin q → S) :
    (∏ i : Fin q,
        rootedTreeTailAt (FieldRootedTree.series M g) (roots i)) =
      PowerSeries.C
          (∏ i : Fin q, FieldRootedTree.vertexFactor M g (roots i)) *
        PowerSeries.subst (M.complexCoreBranchActionSeries g roots)
          (PowerSeries.exp ℂ) := by
  simp_rw [rootedTreeTailAt_series_eq M g]
  rw [Finset.prod_mul_distrib]
  have hexp := prod_subst_exp_eq_subst_sum
    (fun i : Fin q ↦ rootedTreeKernelSeriesAt M g (roots i))
    (fun i ↦ rootedTreeKernelSeriesAt_constantCoeff M g (roots i))
  rw [hexp, ← complexCoreBranchActionSeries_eq_sum_at M g roots]
  simp only [map_prod]

/-- Genuine fixed-core profile composition.  This is defined directly from
the rooted-tree profile series, rather than from an attachment coefficient. -/
def fixedCoreProfileCompositionSeries
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    {q : ℕ} (H : SimpleGraph (Fin q)) : PowerSeries ℂ :=
  PowerSeries.X ^ q * PowerSeries.mk (fun n ↦
    ∫ roots : Fin q → S,
      finiteComplexGraphIntegrand M (1 : C(S, ℂ)) H roots *
        PowerSeries.coeff n
          (∏ i : Fin q, rootedTreeTailAt T (roots i))
      ∂Measure.pi (fun _ : Fin q ↦ M.mu))

/-- Coefficient formula for the independently defined fixed-core profile
composition.  This is the reusable endpoint for a later analytic realization
of the same homogeneous core polynomial. -/
theorem fixedCoreProfileCompositionSeries_coeff
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    {q : ℕ} (H : SimpleGraph (Fin q)) (n : ℕ) :
    PowerSeries.coeff (n + q)
        (fixedCoreProfileCompositionSeries M T H) =
      ∫ roots : Fin q → S,
        finiteComplexGraphIntegrand M (1 : C(S, ℂ)) H roots *
          PowerSeries.coeff n
            (∏ i : Fin q, rootedTreeTailAt T (roots i))
        ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
  rw [fixedCoreProfileCompositionSeries,
    PowerSeries.coeff_X_pow_mul]
  rw [PowerSeries.coeff_mk]

/-- The explicit factor `X^q` makes every coefficient below the core size
vanish.  This local finiteness is the formal input needed when the fixed-core
series are later summed over all cycle lengths. -/
theorem fixedCoreProfileCompositionSeries_coeff_eq_zero_of_lt
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    {q k : ℕ} (H : SimpleGraph (Fin q)) (hk : k < q) :
    PowerSeries.coeff k (fixedCoreProfileCompositionSeries M T H) = 0 := by
  unfold fixedCoreProfileCompositionSeries
  rw [PowerSeries.coeff_X_pow_mul']
  simp only [if_neg (not_le.mpr hk)]

private theorem finiteComplexGraphIntegrand_one_mul_profileProduct
    (M : CompactBJRModel S) (tau : C(S, ℂ)) {q : ℕ}
    (H : SimpleGraph (Fin q)) (roots : Fin q → S) :
    finiteComplexGraphIntegrand M (1 : C(S, ℂ)) H roots *
        (∏ i : Fin q, tau (roots i)) =
      finiteComplexGraphIntegrand M tau H roots := by
  classical
  unfold finiteComplexGraphIntegrand
  simp only [ContinuousMap.one_apply, Finset.prod_const_one, one_mul]
  ring

/-- The genuine rooted-tree formal equation turns literal fixed-core profile
composition into precisely the attachment-exponential coefficient. -/
theorem fixedCoreProfileCompositionSeries_actual_coeff
    (M : CompactBJRModel S) (g : C(S, ℂ))
    {q n k : ℕ} (H : SimpleGraph (Fin q)) (hqn : q + n = k) :
    PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M
          (FieldRootedTree.series M g) H) =
      ∫ roots : Fin q → S,
        finiteComplexGraphIntegrand M
            (FieldRootedTree.vertexFactor M g) H roots *
          PowerSeries.coeff n
            (PowerSeries.subst
              (M.complexCoreBranchActionSeries g roots)
              (PowerSeries.exp ℂ))
        ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
  have hk : k = n + q := by omega
  rw [hk, fixedCoreProfileCompositionSeries_coeff]
  apply integral_congr_ae
  filter_upwards [] with roots
  rw [prod_rootedTreeTailAt_series_eq M g roots,
    PowerSeries.coeff_C_mul]
  rw [← finiteComplexGraphIntegrand_one_mul_profileProduct M
    (FieldRootedTree.vertexFactor M g) H roots]
  ring

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
private theorem rootedTreeTailAt_X_mul_C
    (tau : C(S, ℂ)) (x : S) :
    rootedTreeTailAt (PowerSeries.X * PowerSeries.C tau) x =
      PowerSeries.C (tau x) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp only [rootedTreeTailAt, PowerSeries.coeff_map,
      rootedTreeTail_coeff, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C, if_pos, continuousMapComplexEvalRingHom,
      RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
      ContinuousMap.coeFnRingHom_apply]
  · simp only [rootedTreeTailAt, PowerSeries.coeff_map,
      rootedTreeTail_coeff, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C, if_neg hn, map_zero]

/-- A monomial profile `X tau` recovers the ordinary fixed-profile finite
core weight in degree `q`. -/
theorem fixedCoreProfileCompositionSeries_X_mul_C_coeff
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {q : ℕ} (H : SimpleGraph (Fin q)) :
    PowerSeries.coeff q
        (fixedCoreProfileCompositionSeries M
          (PowerSeries.X * PowerSeries.C tau) H) =
      finiteComplexGraphWeight M tau H := by
  have hcoeff := fixedCoreProfileCompositionSeries_coeff M
    (PowerSeries.X * PowerSeries.C tau) H 0
  rw [zero_add] at hcoeff
  rw [hcoeff]
  unfold finiteComplexGraphWeight
  apply integral_congr_ae
  filter_upwards [] with roots
  simp_rw [rootedTreeTailAt_X_mul_C]
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_prod]
  simp only [PowerSeries.constantCoeff_C]
  exact finiteComplexGraphIntegrand_one_mul_profileProduct M tau H roots

/-- The independently defined formal profile composition agrees on a
monomial profile with the direct simple-cycle trace term.  This is the exact
place where the proved labelled-cycle subtype identity is reused. -/
theorem sum_fixedCoreProfileCompositionSeries_X_mul_C_div_factorial
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {q : ℕ} (hq : 3 ≤ q) :
    (∑ H : {H : SimpleGraph (Fin q) //
        IsAdmissibleAttachmentCore q 0 H},
      PowerSeries.coeff q
        (fixedCoreProfileCompositionSeries M
          (PowerSeries.X * PowerSeries.C tau) H.1)) /
        (q.factorial : ℂ) =
      JointSimpleCycleEGF.profileSimpleCycleTerm M tau (q - 3) := by
  simp_rw [fixedCoreProfileCompositionSeries_X_mul_C_coeff M tau]
  exact
    sum_admissibleAttachmentCore_zero_div_factorial_eq_profileSimpleCycleTerm
      M tau hq

/-- The size-`k` coefficient of the literal simple-cycle profile composition.
The antidiagonal subtype only records the unique split `q + n = k`; the
summand itself is the coefficient of the independently defined fixed-core
profile series. -/
def unicyclicProfileCompositionCoeff
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ)) (k : ℕ) : ℂ :=
  ∑ p : {p : ℕ × ℕ // p ∈ coreOffSizePairs k},
    (∑ H : {H : SimpleGraph (Fin p.1.1) //
        IsAdmissibleAttachmentCore p.1.1 0 H},
      PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M T H.1)) /
      (p.1.1.factorial : ℂ)

/-- Exact factorial cancellation for the core/off-core split. -/
private theorem choose_mul_offFactorial_div_totalFactorial
    {k q n : ℕ} (hqn : q + n = k) :
    ((Nat.choose k q : ℂ) * (n.factorial : ℂ)) /
        (k.factorial : ℂ) =
      1 / (q.factorial : ℂ) := by
  have hqk : q ≤ k := by omega
  have hsub : k - q = n := by omega
  have hnat := Nat.choose_mul_factorial_mul_factorial hqk
  rw [hsub] at hnat
  have hcast :
      (Nat.choose k q : ℂ) * (q.factorial : ℂ) *
          (n.factorial : ℂ) =
        (k.factorial : ℂ) := by
    exact_mod_cast hnat
  have hqfac : (q.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero q
  have hkfac : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp [hqfac, hkfac]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hcast

/-- The explicit `n!` in the labelled-forest formula factors out of the
fixed-core sum and integral. -/
private theorem coreAttachmentFactorial_extract
    (M : CompactBJRModel S) (g : C(S, ℂ)) (q n : ℕ) :
    (∑ H : {H : SimpleGraph (Fin q) //
        IsAdmissibleAttachmentCore q 0 H},
      ∫ roots : Fin q → S,
        finiteComplexGraphIntegrand M
            (FieldRootedTree.vertexFactor M g) H.1 roots *
          ((n.factorial : ℂ) * PowerSeries.coeff n
            (PowerSeries.subst
              (M.complexCoreBranchActionSeries g roots)
              (PowerSeries.exp ℂ)))
        ∂Measure.pi (fun _ : Fin q ↦ M.mu)) =
      (n.factorial : ℂ) *
        ∑ H : {H : SimpleGraph (Fin q) //
            IsAdmissibleAttachmentCore q 0 H},
          ∫ roots : Fin q → S,
            finiteComplexGraphIntegrand M
                (FieldRootedTree.vertexFactor M g) H.1 roots *
              PowerSeries.coeff n
                (PowerSeries.subst
                  (M.complexCoreBranchActionSeries g roots)
                  (PowerSeries.exp ℂ))
            ∂Measure.pi (fun _ : Fin q ↦ M.mu) := by
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro H
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with roots
  ring

/-- No spurious core term occurs below cycle length three. -/
private theorem sum_admissibleAttachmentCore_zero_eq_zero_of_lt_three
    (M : CompactBJRModel S) (T : PowerSeries C(S, ℂ))
    {q k : ℕ} (hq : q < 3) :
    (∑ H : {H : SimpleGraph (Fin q) //
        IsAdmissibleAttachmentCore q 0 H},
      PowerSeries.coeff k
        (fixedCoreProfileCompositionSeries M T H.1)) = 0 := by
  classical
  apply Fintype.sum_eq_zero
  intro H
  exact False.elim (by
    have hthree := three_le_of_isAdmissibleAttachmentCore_zero H.2
    omega)

/-- The genuine unicyclic connected weight, after labelled-EGF
normalization, is the coefficient of the literal simple-cycle profile
composition evaluated at the genuine field-rooted tree series. -/
theorem complexFieldConnectedWeight_div_factorial_eq_unicyclicProfileCompositionCoeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) (k : ℕ) :
    M.complexFieldConnectedWeight g k 1 / (k.factorial : ℂ) =
      unicyclicProfileCompositionCoeff M
        (FieldRootedTree.series M g) k := by
  rw [complexFieldConnectedWeight_eq_coreAttachmentCoeff M g k 0]
  unfold unicyclicProfileCompositionCoeff
  rw [Finset.sum_div]
  apply Fintype.sum_congr
  intro p
  have hqn : p.1.1 + p.1.2 = k := mem_coreOffSizePairs.mp p.2
  rw [coreAttachmentFactorial_extract]
  have hfactor := choose_mul_offFactorial_div_totalFactorial
    (k := k) (q := p.1.1) (n := p.1.2) hqn
  let A : ℂ :=
    ∑ H : {H : SimpleGraph (Fin p.1.1) //
        IsAdmissibleAttachmentCore p.1.1 0 H},
      ∫ roots : Fin p.1.1 → S,
        finiteComplexGraphIntegrand M
            (FieldRootedTree.vertexFactor M g) H.1 roots *
          PowerSeries.coeff p.1.2
            (PowerSeries.subst
              (M.complexCoreBranchActionSeries g roots)
              (PowerSeries.exp ℂ))
        ∂Measure.pi (fun _ : Fin p.1.1 ↦ M.mu)
  calc
    ((Nat.choose k p.1.1 : ℂ) * ((p.1.2.factorial : ℂ) * A)) /
          (k.factorial : ℂ) =
        (((Nat.choose k p.1.1 : ℂ) * (p.1.2.factorial : ℂ)) /
          (k.factorial : ℂ)) * A := by ring
    _ = (1 / (p.1.1.factorial : ℂ)) * A := by rw [hfactor]
    _ = A / (p.1.1.factorial : ℂ) := by ring
    _ = (∑ H : {H : SimpleGraph (Fin p.1.1) //
          IsAdmissibleAttachmentCore p.1.1 0 H},
        PowerSeries.coeff k
          (fixedCoreProfileCompositionSeries M
            (FieldRootedTree.series M g) H.1)) /
          (p.1.1.factorial : ℂ) := by
      apply congrArg (fun z : ℂ ↦ z / (p.1.1.factorial : ℂ))
      dsimp only [A]
      apply Fintype.sum_congr
      intro H
      exact (fixedCoreProfileCompositionSeries_actual_coeff
        M g H.1 hqn).symm

end GraphCore
end PerronWright
