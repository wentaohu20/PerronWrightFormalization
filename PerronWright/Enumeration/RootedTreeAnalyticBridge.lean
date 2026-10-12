import PerronWright.Enumeration.RootedTreeComplexFormal
import PerronWright.Analysis.TreeSubcriticalAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The analytic zero-tree germ and the labelled-tree series

The purpose of this file is deliberately narrow.  We first convert a
one-variable formal multilinear series to the `PowerSeries` having the same
diagonal coefficients.  We then prove, rather than assume, the compatibility
with the continuous linear kernel action and with analytic exponential
composition.  This is the missing bridge between `TreeAnalytic.zero_tree_branch`
and `CompactBJRModel.complexRootedTreeFormalRHS`.
-/

open scoped Classical Topology
noncomputable section

namespace PerronWright

/-- Forget the convergence data of a one-variable formal multilinear series
and retain its diagonal coefficients as a formal power series. -/
def oneDimensionalPowerSeries
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (p : FormalMultilinearSeries ℂ ℂ A) : PowerSeries A :=
  PowerSeries.mk p.coeff

@[simp] theorem oneDimensionalPowerSeries_coeff
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (p : FormalMultilinearSeries ℂ ℂ A) (n : ℕ) :
    PowerSeries.coeff n (oneDimensionalPowerSeries p) = p.coeff n := by
  simp [oneDimensionalPowerSeries]

@[simp] theorem oneDimensionalPowerSeries_constantCoeff
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (p : FormalMultilinearSeries ℂ ℂ A) :
    PowerSeries.constantCoeff (oneDimensionalPowerSeries p) = p.coeff 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  exact oneDimensionalPowerSeries_coeff p 0

/-- Passing to diagonal coefficients commutes with postcomposition by a
continuous linear map.  This is the only linear compatibility needed below. -/
theorem oneDimensionalPowerSeries_compContinuousLinearMap_coeff
    {A B : Type*}
    [NormedRing A] [NormedAlgebra ℂ A]
    [NormedRing B] [NormedAlgebra ℂ B]
    (L : A →L[ℂ] B) (p : FormalMultilinearSeries ℂ ℂ A) (n : ℕ) :
    PowerSeries.coeff n
        (oneDimensionalPowerSeries (L.compFormalMultilinearSeries p)) =
      L (PowerSeries.coeff n (oneDimensionalPowerSeries p)) := by
  simp only [oneDimensionalPowerSeries_coeff,
    FormalMultilinearSeries.coeff,
    ContinuousLinearMap.compFormalMultilinearSeries_apply']

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The one-variable coefficient conversion commutes with the actual complex
kernel action used in the rooted-tree formal equation. -/
theorem CompactBJRModel.oneDimensionalPowerSeries_kernelAction
    (M : CompactBJRModel S)
    (p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)) :
    oneDimensionalPowerSeries
        ((M.kernel.complexActionCLM M.mu).compFormalMultilinearSeries p) =
      M.complexKernelActionPowerSeries (oneDimensionalPowerSeries p) := by
  apply PowerSeries.ext
  intro n
  rw [oneDimensionalPowerSeries_compContinuousLinearMap_coeff]
  exact (M.complexKernelActionPowerSeries_coeff
    (oneDimensionalPowerSeries p) n).symm

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

/-- Substitution of a zero-constant series into the formal exponential has
constant coefficient one.  This local copy keeps the analytic bridge
independent of private implementation lemmas in the uniqueness module. -/
private theorem subst_exp_coeff_zero_of_constantCoeff_zero
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (F : PowerSeries A) (hF0 : PowerSeries.constantCoeff F = 0) :
    PowerSeries.coeff 0
        (PowerSeries.subst F (PowerSeries.exp A)) = 1 := by
  have hF : PowerSeries.HasSubst F :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hF0
  rw [PowerSeries.coeff_subst' hF (PowerSeries.exp A) 0,
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_pow, hF0, zero_pow hd, smul_zero]

/-- The factorial-normalized coefficients of the analytic exponential of a
zero-based germ satisfy the same marked-factor recurrence as formal
substitution into `PowerSeries.exp`. -/
private theorem exp_comp_factorial_coeff_recurrence
    {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    {f : ℂ → A} {p : FormalMultilinearSeries ℂ ℂ A}
    (hp : HasFPowerSeriesAt f p 0) (hp0 : p.coeff 0 = 0) (n : ℕ) :
    ((n + 1).factorial : A) *
        ((NormedSpace.expSeries ℂ A).comp p).coeff (n + 1) =
      ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : A) *
          (((j + 1).factorial : A) * p.coeff (j + 1)) *
          (((n - j).factorial : A) *
            ((NormedSpace.expSeries ℂ A).comp p).coeff (n - j)) := by
  let e : ℂ → A := fun z ↦ NormedSpace.exp (f z)
  let q : FormalMultilinearSeries ℂ ℂ A :=
    (NormedSpace.expSeries ℂ A).comp p
  have hf0 : f 0 = 0 := by
    have hzero : p.coeff 0 = f 0 := by
      simpa only [FormalMultilinearSeries.coeff] using
        hp.coeff_zero (1 : Fin 0 → ℂ)
    rw [← hzero, hp0]
  have he0 : HasFPowerSeriesAt (NormedSpace.exp : A → A)
      (NormedSpace.expSeries ℂ A) (f 0) := by
    simpa only [hf0] using
      (NormedSpace.exp_hasFPowerSeriesAt_zero (𝕂 := ℂ) (𝔸 := A))
  have hq : HasFPowerSeriesAt e q 0 := by
    simpa only [e, q, Function.comp_def] using he0.comp hp
  have hderiv : deriv e =ᶠ[𝓝 0] fun z ↦ deriv f z * e z := by
    filter_upwards [hp.analyticAt.eventually_analyticAt] with z hz
    have hcomp :=
      (hasFDerivAt_exp (𝕂 := ℂ) (𝔸 := A)).comp_hasDerivAt
        z hz.differentiableAt.hasDerivAt
    change deriv (NormedSpace.exp ∘ f) z = deriv f z * e z
    simpa only [e, smul_apply, one_apply_eq_self, smul_eq_mul,
      mul_comm] using hcomp.deriv
  have hdf : ContDiffAt ℂ n (deriv f) 0 :=
    hp.analyticAt.contDiffAt.derivWithin (m := n) le_top
  have he : ContDiffAt ℂ n e 0 :=
    hq.analyticAt.contDiffAt.of_le le_top
  change ((n + 1).factorial : A) * q.coeff (n + 1) =
    ∑ j ∈ Finset.range (n + 1),
      (Nat.choose n j : A) *
        (((j + 1).factorial : A) * p.coeff (j + 1)) *
        (((n - j).factorial : A) * q.coeff (n - j))
  calc
    ((n + 1).factorial : A) * q.coeff (n + 1) =
        iteratedDeriv (n + 1) e 0 := by
      simpa only [← Nat.cast_smul_eq_nsmul A, smul_eq_mul] using
        hasFPowerSeriesAt_factorial_nsmul_coeff hq (n + 1)
    _ = iteratedDeriv n (deriv e) 0 := by
      rw [iteratedDeriv_succ']
    _ = iteratedDeriv n (fun z ↦ deriv f z * e z) 0 :=
      hderiv.iteratedDeriv_eq n
    _ = ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : A) *
          iteratedDeriv j (deriv f) 0 *
          iteratedDeriv (n - j) e 0 :=
      iteratedDeriv_mul hdf he
    _ = ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : A) *
          (((j + 1).factorial : A) * p.coeff (j + 1)) *
          (((n - j).factorial : A) * q.coeff (n - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← congrFun (iteratedDeriv_succ' (n := j) (f := f)) 0,
        ← hasFPowerSeriesAt_factorial_nsmul_coeff hp (j + 1),
        ← hasFPowerSeriesAt_factorial_nsmul_coeff hq (n - j)]
      simp only [nsmul_eq_mul]

/-- Analytic exponential composition agrees coefficientwise with formal
substitution into the power-series exponential.  No convergence radius is
assumed: convergence enters only through the supplied `HasFPowerSeriesAt`. -/
theorem oneDimensionalPowerSeries_exp_comp
    {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [Algebra ℚ A]
    {f : ℂ → A} {p : FormalMultilinearSeries ℂ ℂ A}
    (hp : HasFPowerSeriesAt f p 0) (hp0 : p.coeff 0 = 0) :
    oneDimensionalPowerSeries ((NormedSpace.expSeries ℂ A).comp p) =
      PowerSeries.subst (oneDimensionalPowerSeries p)
        (PowerSeries.exp A) := by
  let q : FormalMultilinearSeries ℂ ℂ A :=
    (NormedSpace.expSeries ℂ A).comp p
  let F : PowerSeries A := oneDimensionalPowerSeries p
  let E : PowerSeries A :=
    PowerSeries.subst F (PowerSeries.exp A)
  have hF0 : PowerSeries.constantCoeff F = 0 := by
    simpa only [F, oneDimensionalPowerSeries_constantCoeff]
  have hF : PowerSeries.HasSubst F :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hF0
  have hf0 : f 0 = 0 := by
    have hzero : p.coeff 0 = f 0 := by
      simpa only [FormalMultilinearSeries.coeff] using
        hp.coeff_zero (1 : Fin 0 → ℂ)
    rw [← hzero, hp0]
  have he0 : HasFPowerSeriesAt (NormedSpace.exp : A → A)
      (NormedSpace.expSeries ℂ A) (f 0) := by
    simpa only [hf0] using
      (NormedSpace.exp_hasFPowerSeriesAt_zero (𝕂 := ℂ) (𝔸 := A))
  have hq : HasFPowerSeriesAt (fun z ↦ NormedSpace.exp (f z)) q 0 := by
    simpa only [q, Function.comp_def] using he0.comp hp
  apply PowerSeries.ext
  intro k
  simp only [oneDimensionalPowerSeries_coeff]
  change q.coeff k = PowerSeries.coeff k E
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero =>
          have hq0 := hq.coeff_zero (1 : Fin 0 → ℂ)
          calc
            q.coeff 0 = 1 := by
              simpa only [FormalMultilinearSeries.coeff, hf0,
                NormedSpace.exp_zero] using hq0
            _ = PowerSeries.coeff 0 E := by
              simpa only [E] using
                (subst_exp_coeff_zero_of_constantCoeff_zero F hF0).symm
      | succ n =>
          have hrecq := exp_comp_factorial_coeff_recurrence hp hp0 n
          have hrecE := factorial_mul_subst_exp_coeff_succ F hF n
          have hmul :
              ((n + 1).factorial : A) * q.coeff (n + 1) =
                ((n + 1).factorial : A) *
                  PowerSeries.coeff (n + 1) E := by
            rw [hrecq]
            change _ = ((n + 1).factorial : A) *
              PowerSeries.coeff (n + 1)
                (PowerSeries.subst F (PowerSeries.exp A))
            rw [hrecE]
            apply Finset.sum_congr rfl
            intro j hj
            rw [ih (n - j) (by omega)]
            simp only [F, E, oneDimensionalPowerSeries_coeff]
          have huQ : IsUnit (((n + 1).factorial : ℕ) : ℚ) :=
            isUnit_iff_ne_zero.mpr (by positivity)
          have hu : IsUnit (((n + 1).factorial : ℕ) : A) := by
            simpa only [map_natCast] using huQ.map (algebraMap ℚ A)
          exact hu.mul_left_cancel hmul

omit [MeasurableSpace S] [BorelSpace S] in
private theorem continuousMap_exp_apply (f : C(S, ℂ)) (x : S) :
    NormedSpace.exp f x = Complex.exp (f x) := by
  simpa only [ContinuousMap.evalAlgHom_apply, ← Complex.exp_eq_exp_ℂ] using
    NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x)
      (ContinuousMap.evalCLM ℂ x).continuous f

/-- The constant factor in the complex formal rooted-tree equation is exactly
the analytic zero-field factor `exp (-degree)`. -/
theorem CompactBJRModel.complex_zeroTreeVertexFactor_eq_exp_neg_degree
    (M : CompactBJRModel S) :
    continuousMapComplexifyRingHom M.zeroTreeVertexFactor =
      NormedSpace.exp (-TreeCritical.degree M) := by
  ext x
  simp only [continuousMapComplexifyRingHom_apply,
    TreeRealComplexBridge.complexify_apply,
    M.zeroTreeVertexFactor_apply, continuousMap_exp_apply,
    ContinuousMap.neg_apply, TreeCritical.degree_apply,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    CompactBJRModel.degreeFunction, ContinuousKernel.degreeMap_apply]

private def zeroFieldLine : ℂ →L[ℂ] ℂ × C(S, ℂ) :=
  ContinuousLinearMap.inl ℂ ℂ C(S, ℂ)

/-- The Taylor series of any analytic zero-tree branch supplied by the actual
implicit equation is the complexified genuine labelled-tree series.  Both the
formal fixed-point equation and the final identification are conclusions. -/
theorem CompactBJRModel.zeroTreeBranch_taylorSeries_eq_complexTypeRootedTreeEGF
    (M : CompactBJRModel S)
    (psi : ℂ × C(S, ℂ) → C(S, ℂ))
    (hpsi : AnalyticAt ℂ psi (0, 0))
    (hpsi0 : psi (0, 0) = 0)
    (hres : ∀ᶠ x in 𝓝 (0, (0 : C(S, ℂ))),
      TreeCritical.residual M (x, psi x) = 0) :
    ∃ p : FormalMultilinearSeries ℂ ℂ C(S, ℂ),
      HasFPowerSeriesAt (fun z ↦ psi (z, 0)) p 0 ∧
      oneDimensionalPowerSeries p =
        M.complexRootedTreeFormalRHS (oneDimensionalPowerSeries p) ∧
      oneDimensionalPowerSeries p = M.complexTypeRootedTreeEGF := by
  let phi : ℂ → C(S, ℂ) := fun z ↦ psi (z, 0)
  have hphi : AnalyticAt ℂ phi 0 := by
    have h := hpsi.compContinuousLinearMap
      (u := zeroFieldLine (S := S)) (x := (0 : ℂ))
    have heq : psi ∘ (zeroFieldLine (S := S)) = phi := by
      funext z
      simp only [phi, zeroFieldLine, Function.comp_apply,
        ContinuousLinearMap.inl_apply]
    rw [← heq]
    exact h
  obtain ⟨p, hp⟩ := hphi
  have hphi0 : phi 0 = 0 := by
    simpa only [phi] using hpsi0
  have hp0 : p.coeff 0 = 0 := by
    calc
      p.coeff 0 = phi 0 := by
        simpa only [FormalMultilinearSeries.coeff] using
          hp.coeff_zero (1 : Fin 0 → ℂ)
      _ = 0 := hphi0

  let K : C(S, ℂ) →L[ℂ] C(S, ℂ) :=
    M.kernel.complexActionCLM M.mu
  let kappa : ℂ → C(S, ℂ) := fun z ↦ K (phi z)
  let pK : FormalMultilinearSeries ℂ ℂ C(S, ℂ) :=
    K.compFormalMultilinearSeries p
  have hpK : HasFPowerSeriesAt kappa pK 0 := by
    obtain ⟨r, hr⟩ := hp
    refine ⟨r, ?_⟩
    simpa only [kappa, pK, Function.comp_def] using
      K.comp_hasFPowerSeriesOnBall hr
  have hpK0 : pK.coeff 0 = 0 := by
    change K (p.coeff 0) = 0
    rw [hp0, map_zero]

  let q : FormalMultilinearSeries ℂ ℂ C(S, ℂ) :=
    (NormedSpace.expSeries ℂ C(S, ℂ)).comp pK
  have hkappa0 : kappa 0 = 0 := by
    simp only [kappa, hphi0, map_zero]
  have hexp0 : HasFPowerSeriesAt
      (NormedSpace.exp : C(S, ℂ) → C(S, ℂ))
      (NormedSpace.expSeries ℂ C(S, ℂ)) (kappa 0) := by
    simpa only [hkappa0] using
      (NormedSpace.exp_hasFPowerSeriesAt_zero
        (𝕂 := ℂ) (𝔸 := C(S, ℂ)))
  have hq : HasFPowerSeriesAt
      (fun z ↦ NormedSpace.exp (kappa z)) q 0 := by
    simpa only [q, Function.comp_def] using hexp0.comp hpK

  let c : C(S, ℂ) :=
    continuousMapComplexifyRingHom M.zeroTreeVertexFactor
  let Lc : C(S, ℂ) →L[ℂ] C(S, ℂ) :=
    ContinuousLinearMap.mul ℂ C(S, ℂ) c
  let h : ℂ → C(S, ℂ) :=
    fun z ↦ c * NormedSpace.exp (kappa z)
  let r : FormalMultilinearSeries ℂ ℂ C(S, ℂ) :=
    Lc.compFormalMultilinearSeries q
  have hr : HasFPowerSeriesAt h r 0 := by
    obtain ⟨rho, hrho⟩ := hq
    refine ⟨rho, ?_⟩
    simpa only [h, r, Lc, Function.comp_def,
      ContinuousLinearMap.mul_apply'] using
      Lc.comp_hasFPowerSeriesOnBall hrho

  have hresLine : ∀ᶠ z in 𝓝 (0 : ℂ),
      TreeCritical.residual M ((z, 0), phi z) = 0 := by
    have ht : Filter.Tendsto (zeroFieldLine (S := S)) (𝓝 (0 : ℂ))
        (𝓝 ((0 : ℂ), (0 : C(S, ℂ)))) := by
      have hz : zeroFieldLine (S := S) (0 : ℂ) =
          ((0 : ℂ), (0 : C(S, ℂ))) := by
        rw [map_zero]
        apply Prod.ext <;> rfl
      rw [← hz]
      exact (zeroFieldLine (S := S)).continuous.continuousAt
    simpa only [zeroFieldLine, phi, ContinuousLinearMap.inl_apply,
      map_zero] using ht.eventually hres
  have hfixed : phi =ᶠ[𝓝 (0 : ℂ)] fun z ↦ z • h z := by
    filter_upwards [hresLine] with z hz
    have hz' : phi z = z • NormedSpace.exp
        (-TreeCritical.degree M + K (phi z)) := by
      change phi z - z • NormedSpace.exp
        ((0 : C(S, ℂ)) - TreeCritical.degree M + K (phi z)) = 0 at hz
      simpa only [zero_sub] using sub_eq_zero.mp hz
    calc
      phi z = z • NormedSpace.exp
          (-TreeCritical.degree M + K (phi z)) := hz'
      _ = z •
          (NormedSpace.exp (-TreeCritical.degree M) *
            NormedSpace.exp (K (phi z))) := by
        rw [NormedSpace.exp_add]
      _ = z • h z := by
        rw [← M.complex_zeroTreeVertexFactor_eq_exp_neg_degree]

  have hrhsDeriv : deriv (fun z ↦ z • h z) 0 = h 0 := by
    have hh := (hasDerivAt_id (0 : ℂ)).smul hr.hasDerivAt
    have hfun : (fun z : ℂ ↦ z • h z) = (id : ℂ → ℂ) • h := by
      funext z
      rfl
    rw [hfun]
    simpa only [id_eq, zero_smul, zero_add, one_smul] using hh.deriv
  have hphiDeriv : deriv phi 0 = h 0 :=
    hfixed.deriv_eq.trans hrhsDeriv
  have hdslope : dslope phi 0 =ᶠ[𝓝 (0 : ℂ)] h := by
    filter_upwards [hfixed] with z hz
    by_cases hz0 : z = 0
    · subst z
      simpa only [dslope_same] using hphiDeriv
    · rw [dslope_of_ne _ hz0]
      rw [slope, sub_zero, hphi0, hz, vsub_eq_sub, sub_zero, ← mul_smul,
        inv_mul_cancel₀ hz0, one_smul]
  have hpSlope := hp.has_fpower_series_dslope_fslope
  have hpSlopeEq : p.fslope = r :=
    hpSlope.eq_formalMultilinearSeries_of_eventually hr hdslope

  have hqPower : oneDimensionalPowerSeries q =
      PowerSeries.subst (oneDimensionalPowerSeries pK)
        (PowerSeries.exp C(S, ℂ)) := by
    simpa only [q] using oneDimensionalPowerSeries_exp_comp hpK hpK0
  have hpKPower : oneDimensionalPowerSeries pK =
      M.complexKernelActionPowerSeries (oneDimensionalPowerSeries p) := by
    simpa only [pK, K] using M.oneDimensionalPowerSeries_kernelAction p

  have hformal : oneDimensionalPowerSeries p =
      M.complexRootedTreeFormalRHS (oneDimensionalPowerSeries p) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
        simp only [oneDimensionalPowerSeries_coeff, hp0,
          M.complexRootedTreeFormalRHS_coeff_zero]
    | succ n =>
        have hcoeff' : p.coeff (n + 1) = c * q.coeff n := by
          rw [← FormalMultilinearSeries.coeff_fslope, hpSlopeEq]
          simp only [r, Lc, FormalMultilinearSeries.coeff,
            ContinuousLinearMap.compFormalMultilinearSeries_apply',
            ContinuousLinearMap.mul_apply']
        rw [CompactBJRModel.complexRootedTreeFormalRHS,
          PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]
        calc
          PowerSeries.coeff (n + 1) (oneDimensionalPowerSeries p) =
              p.coeff (n + 1) := oneDimensionalPowerSeries_coeff p (n + 1)
          _ = c * q.coeff n := hcoeff'
          _ = c * PowerSeries.coeff n (oneDimensionalPowerSeries q) := by
            rw [oneDimensionalPowerSeries_coeff]
          _ = c * PowerSeries.coeff n
                (PowerSeries.subst (oneDimensionalPowerSeries pK)
                  (PowerSeries.exp C(S, ℂ))) := by
            rw [hqPower]
          _ = c * PowerSeries.coeff n
                (PowerSeries.subst
                  (M.complexKernelActionPowerSeries
                    (oneDimensionalPowerSeries p))
                  (PowerSeries.exp C(S, ℂ))) := by
            rw [hpKPower]
          _ = continuousMapComplexifyRingHom M.zeroTreeVertexFactor *
                PowerSeries.coeff n
                  (PowerSeries.subst
                    (M.complexKernelActionPowerSeries
                      (oneDimensionalPowerSeries p))
                    (PowerSeries.exp C(S, ℂ))) := rfl
  have hactual := M.complexRootedTreeFormalRHS_fixedPoint_unique
    (oneDimensionalPowerSeries p)
    (by simpa only [oneDimensionalPowerSeries_constantCoeff] using hp0)
    hformal
  exact ⟨p, hp, hformal, hactual⟩

/-- Existence form, obtained directly from the proved Banach analytic implicit
branch. -/
theorem CompactBJRModel.exists_zeroTreeBranch_with_labelledTreeTaylorSeries
    (M : CompactBJRModel S) :
    ∃ (psi : ℂ × C(S, ℂ) → C(S, ℂ))
        (p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)),
      AnalyticAt ℂ psi (0, 0) ∧
      psi (0, 0) = 0 ∧
      (∀ᶠ x in 𝓝 (0, (0 : C(S, ℂ))),
        TreeCritical.residual M (x, psi x) = 0) ∧
      HasFPowerSeriesAt (fun z ↦ psi (z, 0)) p 0 ∧
      oneDimensionalPowerSeries p = M.complexTypeRootedTreeEGF := by
  obtain ⟨psi, hpsi, hpsi0, hres, -⟩ :=
    TreeAnalytic.zero_tree_branch M.kernel M.mu (TreeCritical.degree M)
  obtain ⟨p, hp, -, hactual⟩ :=
    M.zeroTreeBranch_taylorSeries_eq_complexTypeRootedTreeEGF
      psi hpsi hpsi0 hres
  exact ⟨psi, p, hpsi, hpsi0, hres, hp, hactual⟩

end PerronWright


