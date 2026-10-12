import PerronWright.Enumeration.UnicyclicCompositionCoeff
import PerronWright.Enumeration.RootedTreePhysicalSeries
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Analytic realization of one fixed unicyclic core

This file realizes the already constructed formal series
`GraphCore.fixedCoreProfileCompositionSeries` as the Taylor series of the
actual fixed-core weight after substitution of an analytic profile.  The
argument is deliberately restricted to one fixed finite core.  In
particular, it does not interchange an infinite sum over cycle lengths with
Taylor coefficients.
-/

open MeasureTheory
open scoped Classical Topology
noncomputable section

namespace PerronWright
namespace GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem hasFPowerSeriesAt_factorial_nsmul_coeff
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    {f : ℂ → A} {p : FormalMultilinearSeries ℂ ℂ A} {z : ℂ}
    (hp : HasFPowerSeriesAt f p z) (n : ℕ) :
    n.factorial • p.coeff n = iteratedDeriv n f z := by
  obtain ⟨r, hr⟩ := hp
  have h := hr.factorial_smul (1 : ℂ) n
  simpa only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] using h

/-- For a one-variable analytic product, diagonal Taylor coefficients are
the ordinary Cauchy product.  This is the only generic coefficient lemma
needed by the fixed-core realization. -/
private theorem hasFPowerSeriesAt_mul_oneDimensional
    {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    {f g : ℂ → A}
    {p q : FormalMultilinearSeries ℂ ℂ A}
    (hp : HasFPowerSeriesAt f p 0)
    (hq : HasFPowerSeriesAt g q 0) :
    HasFPowerSeriesAt (fun z ↦ f z * g z)
      (oneDimensionalFormalMultilinearSeries
        (oneDimensionalPowerSeries p * oneDimensionalPowerSeries q)) 0 := by
  obtain ⟨r, hr⟩ := hp.analyticAt.mul hq.analyticAt
  have hfun : f * g = fun z ↦ f z * g z := by
    funext z
    rfl
  rw [hfun] at hr
  have hrPower :
      oneDimensionalPowerSeries r =
        oneDimensionalPowerSeries p * oneDimensionalPowerSeries q := by
    apply PowerSeries.ext
    intro n
    have hfac : (n.factorial : ℂ) ≠ 0 := by
      exact_mod_cast n.factorial_ne_zero
    apply smul_right_injective (R := ℂ) A hfac
    simp only [Algebra.smul_def, map_natCast]
    calc
      (n.factorial : A) *
          PowerSeries.coeff n (oneDimensionalPowerSeries r) =
          iteratedDeriv n (fun z ↦ f z * g z) 0 := by
        rw [oneDimensionalPowerSeries_coeff]
        simpa only [nsmul_eq_mul] using
          hasFPowerSeriesAt_factorial_nsmul_coeff hr n
      _ = ∑ j ∈ Finset.range (n + 1),
          (Nat.choose n j : A) * iteratedDeriv j f 0 *
            iteratedDeriv (n - j) g 0 := by
        exact iteratedDeriv_mul
          (hp.analyticAt.contDiffAt.of_le le_top)
          (hq.analyticAt.contDiffAt.of_le le_top)
      _ = (n.factorial : A) *
          PowerSeries.coeff n
            (oneDimensionalPowerSeries p * oneDimensionalPowerSeries q) := by
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp only [oneDimensionalPowerSeries_coeff,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hchoose := Nat.choose_mul_factorial_mul_factorial hjle
        have hchooseA :
            (Nat.choose n j : A) * (j.factorial : A) *
                ((n - j).factorial : A) = (n.factorial : A) := by
          simpa only [Nat.cast_mul] using
            congrArg (fun m : ℕ ↦ (m : A)) hchoose
        have hpj := hasFPowerSeriesAt_factorial_nsmul_coeff hp j
        have hqj := hasFPowerSeriesAt_factorial_nsmul_coeff hq (n - j)
        simp only [nsmul_eq_mul] at hpj hqj
        rw [← hpj, ← hqj]
        rw [← hchooseA]
        ring
  have hrSeries :
      r = oneDimensionalFormalMultilinearSeries
        (oneDimensionalPowerSeries p * oneDimensionalPowerSeries q) := by
    rw [← oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries r,
      hrPower]
  simpa only [hrSeries] using hr

private theorem hasFPowerSeriesAt_const_oneDimensional
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (a : A) :
    HasFPowerSeriesAt (fun _ : ℂ ↦ a)
      (oneDimensionalFormalMultilinearSeries (PowerSeries.C a)) 0 := by
  have hraw : HasFPowerSeriesAt (fun _ : ℂ ↦ a)
      (constFormalMultilinearSeries ℂ ℂ a) 0 := hasFPowerSeriesAt_const
  have hpower :
      oneDimensionalPowerSeries (constFormalMultilinearSeries ℂ ℂ a) =
        PowerSeries.C a := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
        simp [FormalMultilinearSeries.coeff,
          constFormalMultilinearSeries_apply_zero]
    | succ n =>
        simp [FormalMultilinearSeries.coeff,
          constFormalMultilinearSeries_apply_succ]
  have hseries :
      constFormalMultilinearSeries ℂ ℂ a =
        oneDimensionalFormalMultilinearSeries (PowerSeries.C a) := by
    rw [← oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries
      (constFormalMultilinearSeries ℂ ℂ a), hpower]
  simpa only [hseries] using hraw

private theorem hasFPowerSeriesAt_finset_prod_oneDimensional
    {ι A : Type*} [DecidableEq ι]
    [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (s : Finset ι) (f : ι → ℂ → A)
    (p : ι → FormalMultilinearSeries ℂ ℂ A)
    (hp : ∀ i ∈ s, HasFPowerSeriesAt (f i) (p i) 0) :
    HasFPowerSeriesAt (fun z ↦ ∏ i ∈ s, f i z)
      (oneDimensionalFormalMultilinearSeries
        (∏ i ∈ s, oneDimensionalPowerSeries (p i))) 0 := by
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.prod_empty, map_one] using
        (hasFPowerSeriesAt_const_oneDimensional (1 : A))
  | @insert i s hi ih =>
      have hiPower := hp i (Finset.mem_insert_self i s)
      have hsPower := ih (fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.prod_insert hi,
        oneDimensionalPowerSeries_oneDimensionalFormalMultilinearSeries] using
        hasFPowerSeriesAt_mul_oneDimensional hiPower hsPower

private theorem ContinuousLinearMap.comp_hasFPowerSeriesAt_local
    {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (L : A →L[ℂ] B) {f : ℂ → A}
    {p : FormalMultilinearSeries ℂ ℂ A}
    (hp : HasFPowerSeriesAt f p 0) :
    HasFPowerSeriesAt (fun z ↦ L (f z))
      (L.compFormalMultilinearSeries p) 0 := by
  obtain ⟨r, hr⟩ := hp
  refine ⟨r, ?_⟩
  simpa only [Function.comp_def] using L.comp_hasFPowerSeriesOnBall hr

private def coreCoordinateMap {q : ℕ} (i : Fin q) :
    C(Fin q → S, S) :=
  ⟨fun roots ↦ roots i, continuous_apply i⟩

private def corePullbackCLM {q : ℕ} (i : Fin q) :
    C(S, ℂ) →L[ℂ] C(Fin q → S, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ (coreCoordinateMap i)

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] private theorem corePullbackCLM_apply
    {q : ℕ} (i : Fin q) (tau : C(S, ℂ)) (roots : Fin q → S) :
    corePullbackCLM i tau roots = tau (roots i) := rfl

private def corePullbackAlgHom {q : ℕ} (i : Fin q) :
    C(S, ℂ) →ₐ[ℂ] C(Fin q → S, ℂ) :=
  ContinuousMap.compRightAlgHom ℂ ℂ (coreCoordinateMap i)

private def corePullbackSeries {q : ℕ} (i : Fin q)
    (T : PowerSeries C(S, ℂ)) : PowerSeries C(Fin q → S, ℂ) :=
  PowerSeries.map (corePullbackAlgHom i).toRingHom T

private def corePullbackTailSeries {q : ℕ} (i : Fin q)
    (T : PowerSeries C(S, ℂ)) : PowerSeries C(Fin q → S, ℂ) :=
  PowerSeries.map (corePullbackAlgHom i).toRingHom (rootedTreeTail T)

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] private theorem corePullbackSeries_coeff
    {q : ℕ} (i : Fin q) (T : PowerSeries C(S, ℂ)) (n : ℕ)
    (roots : Fin q → S) :
    PowerSeries.coeff n (corePullbackSeries i T) roots =
      PowerSeries.coeff n T (roots i) := by
  simp [corePullbackSeries, corePullbackAlgHom, coreCoordinateMap]

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] private theorem corePullbackTailSeries_coeff
    {q : ℕ} (i : Fin q) (T : PowerSeries C(S, ℂ)) (n : ℕ)
    (roots : Fin q → S) :
    PowerSeries.coeff n (corePullbackTailSeries i T) roots =
      PowerSeries.coeff (n + 1) T (roots i) := by
  simp [corePullbackTailSeries, corePullbackAlgHom, coreCoordinateMap,
    rootedTreeTail_coeff]

omit [MeasurableSpace S] [BorelSpace S] in
private theorem oneDimensionalPowerSeries_corePullback
    {q : ℕ} (i : Fin q)
    (p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)) :
    oneDimensionalPowerSeries
        ((corePullbackCLM i).compFormalMultilinearSeries p) =
      corePullbackSeries i (oneDimensionalPowerSeries p) := by
  apply PowerSeries.ext
  intro n
  rw [oneDimensionalPowerSeries_compContinuousLinearMap_coeff]
  ext roots
  simp only [corePullbackSeries_coeff, corePullbackCLM_apply,
    oneDimensionalPowerSeries_coeff]

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
private theorem corePullbackSeries_eq_X_mul_tail
    {q : ℕ} (i : Fin q) (T : PowerSeries C(S, ℂ))
    (hT0 : PowerSeries.constantCoeff T = 0) :
    corePullbackSeries i T =
      PowerSeries.X * corePullbackTailSeries i T := by
  calc
    corePullbackSeries i T =
        corePullbackSeries i
          (PowerSeries.X * rootedTreeTail T) := by
      rw [X_mul_rootedTreeTail T hT0]
    _ = PowerSeries.X * corePullbackTailSeries i T := by
      simp only [corePullbackSeries, corePullbackTailSeries, map_mul,
        PowerSeries.map_X]

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
private theorem prod_corePullbackSeries_eq_X_pow_mul_tail
    {q : ℕ} (T : PowerSeries C(S, ℂ))
    (hT0 : PowerSeries.constantCoeff T = 0) :
    (∏ i : Fin q, corePullbackSeries i T) =
      PowerSeries.X ^ q * ∏ i : Fin q, corePullbackTailSeries i T := by
  classical
  have hfactor : ∀ i : Fin q,
      corePullbackSeries i T =
        PowerSeries.X * corePullbackTailSeries i T :=
    fun i ↦ corePullbackSeries_eq_X_mul_tail i T hT0
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private def coreProductMeasure (M : CompactBJRModel S) (q : ℕ) :
    Measure (Fin q → S) :=
  Measure.pi (fun _ : Fin q ↦ M.mu)

private instance coreProductMeasure_isFinite
    (M : CompactBJRModel S) (q : ℕ) :
    IsFiniteMeasure (coreProductMeasure M q) := by
  unfold coreProductMeasure
  infer_instance

private def coreIntegralCLM (M : CompactBJRModel S) (q : ℕ) :
    C(Fin q → S, ℂ) →L[ℂ] ℂ :=
  (MeasureTheory.L1.integralCLM'
      (α := Fin q → S) (E := ℂ) (μ := coreProductMeasure M q) ℂ).comp
    (ContinuousMap.toLp 1 (coreProductMeasure M q) ℂ)

private theorem coreIntegralCLM_apply
    (M : CompactBJRModel S) (q : ℕ) (f : C(Fin q → S, ℂ)) :
    coreIntegralCLM M q f =
      ∫ roots : Fin q → S, f roots ∂coreProductMeasure M q := by
  unfold coreIntegralCLM
  rw [ContinuousLinearMap.comp_apply, ← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  apply integral_congr_ae
  exact ContinuousMap.coeFn_toLp
    (p := 1) (μ := coreProductMeasure M q) (𝕜 := ℂ) f

private def fixedCoreEdgeProfile
    (M : CompactBJRModel S) {q : ℕ} (H : SimpleGraph (Fin q)) :
    C(Fin q → S, ℂ) := by
  classical
  exact ⟨finiteComplexGraphIntegrand M (1 : C(S, ℂ)) H,
    continuous_finiteComplexGraphIntegrand M (1 : C(S, ℂ)) H⟩

private def fixedCoreFunctional
    (M : CompactBJRModel S) {q : ℕ} (H : SimpleGraph (Fin q)) :
    C(Fin q → S, ℂ) →L[ℂ] ℂ :=
  (coreIntegralCLM M q).comp
    (ContinuousLinearMap.mul ℂ C(Fin q → S, ℂ)
      (fixedCoreEdgeProfile M H))

private theorem finiteComplexGraphIntegrand_one_mul_profileProduct_local
    (M : CompactBJRModel S) (tau : C(S, ℂ)) {q : ℕ}
    (H : SimpleGraph (Fin q)) (roots : Fin q → S) :
    finiteComplexGraphIntegrand M (1 : C(S, ℂ)) H roots *
        (∏ i : Fin q, tau (roots i)) =
      finiteComplexGraphIntegrand M tau H roots := by
  classical
  unfold finiteComplexGraphIntegrand
  simp only [ContinuousMap.one_apply, Finset.prod_const_one, one_mul]
  ring

private theorem fixedCoreFunctional_profileProduct
    (M : CompactBJRModel S) (tau : C(S, ℂ)) {q : ℕ}
    (H : SimpleGraph (Fin q)) :
    fixedCoreFunctional M H
        (∏ i : Fin q, corePullbackCLM i tau) =
      finiteComplexGraphWeight M tau H := by
  classical
  unfold fixedCoreFunctional
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    coreIntegralCLM_apply]
  unfold fixedCoreEdgeProfile finiteComplexGraphWeight coreProductMeasure
  apply integral_congr_ae
  filter_upwards [] with roots
  change finiteComplexGraphIntegrand M (1 : C(S, ℂ)) H roots *
      (∏ i : Fin q, corePullbackCLM i tau) roots =
    finiteComplexGraphIntegrand M tau H roots
  rw [ContinuousMap.prod_apply]
  simp only [corePullbackCLM_apply]
  exact finiteComplexGraphIntegrand_one_mul_profileProduct_local
    M tau H roots

private def applyCLMToPowerSeries
    {A B : Type*} [Semiring A] [Semiring B]
    (L : A →+ B) (P : PowerSeries A) : PowerSeries B :=
  PowerSeries.mk fun n ↦ L (PowerSeries.coeff n P)

@[simp] private theorem applyCLMToPowerSeries_coeff
    {A B : Type*} [Semiring A] [Semiring B]
    (L : A →+ B) (P : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (applyCLMToPowerSeries L P) =
      L (PowerSeries.coeff n P) := by
  rw [applyCLMToPowerSeries, PowerSeries.coeff_mk]

private theorem applyCLMToPowerSeries_X_pow_mul
    {A B : Type*} [CommSemiring A] [CommSemiring B]
    (L : A →+ B) (q : ℕ) (P : PowerSeries A) :
    applyCLMToPowerSeries L (PowerSeries.X ^ q * P) =
      PowerSeries.X ^ q * applyCLMToPowerSeries L P := by
  apply PowerSeries.ext
  intro n
  simp only [applyCLMToPowerSeries_coeff,
    PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

private def rootsEvalRingHom {q : ℕ} (roots : Fin q → S) :
    C(Fin q → S, ℂ) →+* ℂ :=
  (Pi.evalRingHom (fun _ : Fin q → S ↦ ℂ) roots).comp
    ContinuousMap.coeFnRingHom

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
private theorem map_corePullbackTailSeries
    {q : ℕ} (i : Fin q) (T : PowerSeries C(S, ℂ))
    (roots : Fin q → S) :
    PowerSeries.map (rootsEvalRingHom roots)
        (corePullbackTailSeries i T) =
      rootedTreeTailAt T (roots i) := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, rootsEvalRingHom,
    RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
    ContinuousMap.coeFnRingHom_apply, corePullbackTailSeries_coeff,
    rootedTreeTailAt_coeff]

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
private theorem coeff_prod_corePullbackTailSeries_apply
    {q : ℕ} (T : PowerSeries C(S, ℂ)) (n : ℕ)
    (roots : Fin q → S) :
    PowerSeries.coeff n
        (∏ i : Fin q, corePullbackTailSeries i T) roots =
      PowerSeries.coeff n
        (∏ i : Fin q, rootedTreeTailAt T (roots i)) := by
  calc
    PowerSeries.coeff n
        (∏ i : Fin q, corePullbackTailSeries i T) roots =
        PowerSeries.coeff n
          (PowerSeries.map (rootsEvalRingHom roots)
            (∏ i : Fin q, corePullbackTailSeries i T)) := by
      simp only [PowerSeries.coeff_map, rootsEvalRingHom,
        RingHom.coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
        ContinuousMap.coeFnRingHom_apply]
    _ = PowerSeries.coeff n
          (∏ i : Fin q,
            PowerSeries.map (rootsEvalRingHom roots)
              (corePullbackTailSeries i T)) := by
      rw [map_prod]
    _ = PowerSeries.coeff n
          (∏ i : Fin q, rootedTreeTailAt T (roots i)) := by
      simp_rw [map_corePullbackTailSeries]

private theorem oneDimensionalPowerSeries_compCLM
    {A B : Type*}
    [NormedRing A] [NormedAlgebra ℂ A]
    [NormedRing B] [NormedAlgebra ℂ B]
    (L : A →L[ℂ] B) (p : FormalMultilinearSeries ℂ ℂ A) :
    oneDimensionalPowerSeries (L.compFormalMultilinearSeries p) =
      applyCLMToPowerSeries L.toLinearMap.toAddMonoidHom
        (oneDimensionalPowerSeries p) := by
  apply PowerSeries.ext
  intro n
  rw [oneDimensionalPowerSeries_compContinuousLinearMap_coeff,
    applyCLMToPowerSeries_coeff]
  rfl

private theorem fixedCoreFunctional_powerSeries
    (M : CompactBJRModel S) {q : ℕ} (H : SimpleGraph (Fin q))
    (T : PowerSeries C(S, ℂ))
    (hT0 : PowerSeries.constantCoeff T = 0) :
    applyCLMToPowerSeries
        (fixedCoreFunctional M H).toLinearMap.toAddMonoidHom
        (∏ i : Fin q, corePullbackSeries i T) =
      fixedCoreProfileCompositionSeries M T H := by
  classical
  rw [prod_corePullbackSeries_eq_X_pow_mul_tail T hT0]
  rw [applyCLMToPowerSeries_X_pow_mul
    (fixedCoreFunctional M H).toLinearMap.toAddMonoidHom q]
  unfold fixedCoreProfileCompositionSeries
  apply congrArg (fun P : PowerSeries ℂ ↦ PowerSeries.X ^ q * P)
  apply PowerSeries.ext
  intro n
  rw [applyCLMToPowerSeries_coeff, PowerSeries.coeff_mk]
  change fixedCoreFunctional M H
      (PowerSeries.coeff n
        (∏ i : Fin q, corePullbackTailSeries i T)) = _
  unfold fixedCoreFunctional
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    coreIntegralCLM_apply]
  unfold fixedCoreEdgeProfile coreProductMeasure
  apply integral_congr_ae
  filter_upwards [] with roots
  change finiteComplexGraphIntegrand M (1 : C(S, ℂ)) H roots *
      PowerSeries.coeff n
        (∏ i : Fin q, corePullbackTailSeries i T) roots = _
  rw [coeff_prod_corePullbackTailSeries_apply T n roots]

/-- The Taylor series of one actual fixed-core weight is the literal profile
composition series already used in the combinatorial coefficient bridge. -/
theorem finiteComplexGraphWeight_hasFPowerSeriesAt_profileComposition
    (M : CompactBJRModel S) {q : ℕ} (H : SimpleGraph (Fin q))
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    HasFPowerSeriesAt
      (fun w ↦ finiteComplexGraphWeight M (tau w) H)
      (oneDimensionalFormalMultilinearSeries
        (fixedCoreProfileCompositionSeries M
          (oneDimensionalPowerSeries p) H)) 0 := by
  classical
  let T : PowerSeries C(S, ℂ) := oneDimensionalPowerSeries p
  let P : PowerSeries C(Fin q → S, ℂ) :=
    ∏ i : Fin q, corePullbackSeries i T
  have hT0 : PowerSeries.constantCoeff T = 0 := by
    simpa only [T, oneDimensionalPowerSeries_constantCoeff]
  have hcoordinate : ∀ i : Fin q,
      HasFPowerSeriesAt
        (fun w ↦ corePullbackCLM i (tau w))
        ((corePullbackCLM i).compFormalMultilinearSeries p) 0 := by
    intro i
    exact ContinuousLinearMap.comp_hasFPowerSeriesAt_local
      (corePullbackCLM i) hp
  have hproduct :
      HasFPowerSeriesAt
        (fun w ↦ ∏ i : Fin q, corePullbackCLM i (tau w))
        (oneDimensionalFormalMultilinearSeries P) 0 := by
    have h := hasFPowerSeriesAt_finset_prod_oneDimensional
      (Finset.univ : Finset (Fin q))
      (fun i w ↦ corePullbackCLM i (tau w))
      (fun i ↦ (corePullbackCLM i).compFormalMultilinearSeries p)
      (fun i _ ↦ hcoordinate i)
    simpa only [P, T, oneDimensionalPowerSeries_corePullback] using h
  have hlinear := ContinuousLinearMap.comp_hasFPowerSeriesAt_local
    (fixedCoreFunctional M H) hproduct
  have hpower :
      oneDimensionalPowerSeries
          ((fixedCoreFunctional M H).compFormalMultilinearSeries
            (oneDimensionalFormalMultilinearSeries P)) =
        fixedCoreProfileCompositionSeries M T H := by
    calc
      oneDimensionalPowerSeries
          ((fixedCoreFunctional M H).compFormalMultilinearSeries
            (oneDimensionalFormalMultilinearSeries P)) =
          applyCLMToPowerSeries
            (fixedCoreFunctional M H).toLinearMap.toAddMonoidHom P := by
        rw [oneDimensionalPowerSeries_compCLM,
          oneDimensionalPowerSeries_oneDimensionalFormalMultilinearSeries]
      _ = fixedCoreProfileCompositionSeries M T H :=
        fixedCoreFunctional_powerSeries M H T hT0
  have hseries :
      (fixedCoreFunctional M H).compFormalMultilinearSeries
          (oneDimensionalFormalMultilinearSeries P) =
        oneDimensionalFormalMultilinearSeries
          (fixedCoreProfileCompositionSeries M T H) := by
    rw [← oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries
      ((fixedCoreFunctional M H).compFormalMultilinearSeries
        (oneDimensionalFormalMultilinearSeries P)), hpower]
  simpa only [Function.comp_def, hseries, T,
    fixedCoreFunctional_profileProduct] using hlinear

end GraphCore
end PerronWright
