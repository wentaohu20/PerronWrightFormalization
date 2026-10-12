import PerronWright.Analysis.RadiusResponse

open MeasureTheory PerronWright
open scoped Topology ContDiff

noncomputable section

namespace PerronWright.TreeFold

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Linearization of the tree equation with the Perron coordinate of the profile fixed. -/
def foldBaseDerivative (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (ℂ × C(S, ℂ)) →L[ℂ] (C(S, ℂ) × ℂ) :=
  (((ContinuousLinearMap.id ℂ C(S, ℂ) - M.kernel.complexActionCLM M.mu).comp
      (ContinuousLinearMap.snd ℂ ℂ C(S, ℂ))) -
    (ContinuousLinearMap.fst ℂ ℂ C(S, ℂ)).smulRight (1 : C(S, ℂ))).prod
    ((M.normalizedPerronFunctional hM).comp
      (ContinuousLinearMap.snd ℂ ℂ C(S, ℂ)))

theorem foldBaseDerivative_apply (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (q : ℂ × C(S, ℂ)) :
    foldBaseDerivative M hM q =
      (q.2 - M.kernel.complexAction M.mu q.2 - q.1 • (1 : C(S, ℂ)),
        M.normalizedPerronFunctional hM q.2) := rfl

theorem foldBaseDerivative_injective (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    Function.Injective (foldBaseDerivative M hM) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q hq
  have hfirst := congrArg Prod.fst hq
  have hsecond := congrArg Prod.snd hq
  change q.2 - M.kernel.complexAction M.mu q.2 - q.1 • (1 : C(S, ℂ)) = 0 at hfirst
  change M.normalizedPerronFunctional hM q.2 = 0 at hsecond
  have hrho := congrArg (M.normalizedPerronFunctional hM) hfirst
  simp only [map_sub, M.normalizedPerronFunctional_action hM, map_smul,
    FoldCoefficients.normalizedPerronFunctional_one, smul_eq_mul,
    sub_self, map_zero, zero_sub] at hrho
  have hrho0 : q.1 = 0 := (mul_eq_zero.mp (neg_eq_zero.mp hrho)).resolve_right
    (FoldCoefficients.first_scalar_ne_zero M hM)
  rw [hrho0, zero_smul, sub_zero] at hfirst
  have hf := M.complex_fixed_eq_perronFunctional_smul hM q.2 (sub_eq_zero.mp hfirst).symm
  rw [hsecond, zero_smul] at hf
  exact Prod.ext hrho0 hf

theorem foldBaseDerivative_surjective (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    Function.Surjective (foldBaseDerivative M hM) := by
  rintro ⟨y, c⟩
  let ell := M.normalizedPerronFunctional hM
  let u := M.complexPerronFunction hM
  let r : ℂ := -(ell y) / ell 1
  let f : C(S, ℂ) := y + r • 1
  let w : C(S, ℂ) := M.augmentedKernelInverse hM f
  have h1 : ell 1 ≠ 0 := by
    rw [FoldCoefficients.normalizedPerronFunctional_one]
    exact FoldCoefficients.first_scalar_ne_zero M hM
  have hf : ell f = 0 := by
    change ell (y + (-(ell y) / ell 1) • 1) = 0
    rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ h1]
    exact add_neg_cancel _
  obtain ⟨hw0, hw⟩ := M.augmentedKernelInverse_on_complement hM f hf
  refine ⟨(r, w + c • u), ?_⟩
  rw [foldBaseDerivative_apply]
  apply Prod.ext
  · change (w + c • u) - M.kernel.complexActionCLM M.mu (w + c • u) - r • 1 = y
    rw [map_add, map_smul]
    have hu : M.kernel.complexActionCLM M.mu u = u := M.complexPerronFunction_fixed hM
    rw [hu]
    calc
      _ = (w - M.kernel.complexAction M.mu w) - r • 1 := by
        change (w + c • u) - (M.kernel.complexAction M.mu w + c • u) - r • 1 = _
        abel
      _ = y := by
        rw [hw]
        change y + r • 1 - r • 1 = y
        abel
  · change ell (w + c • u) = c
    rw [map_add, map_smul, smul_eq_mul, hw0,
      M.normalizedPerronFunctional_perronFunction]
    ring

theorem foldBaseDerivative_invertible (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (foldBaseDerivative M hM).IsInvertible := by
  exact ⟨ContinuousLinearEquiv.ofBijective (foldBaseDerivative M hM)
    (LinearMap.ker_eq_bot.mpr (foldBaseDerivative_injective M hM))
    (LinearMap.range_eq_top.mpr (foldBaseDerivative_surjective M hM)),
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- The actual tree equation and a scalar coordinate along the Perron direction. -/
def foldResidual (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ))) : C(S, ℂ) × ℂ :=
  (TreeCritical.residual M ((p.2.1, p.1.1), p.2.2),
    M.normalizedPerronFunctional hM p.2.2 -
      M.normalizedPerronFunctional hM 1 - p.1.2)

theorem foldResidual_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (foldResidual M hM) ((0, 0), (1, 1)) := by
  let a : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) := ((0, 0), (1, 1))
  have hz : AnalyticAt ℂ (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦ p.2.1) a :=
    analyticAt_fst.comp analyticAt_snd
  have hg : AnalyticAt ℂ (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦ p.1.1) a :=
    analyticAt_fst.comp analyticAt_fst
  have ht : AnalyticAt ℂ (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦ p.1.2) a :=
    analyticAt_snd.comp analyticAt_fst
  have hU : AnalyticAt ℂ (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦ p.2.2) a :=
    analyticAt_snd.comp analyticAt_snd
  have hfirst : AnalyticAt ℂ (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦
      TreeCritical.residual M ((p.2.1, p.1.1), p.2.2)) a := by
    exact (TreeAnalytic.residual_analytic M.kernel M.mu (TreeCritical.degree M)
      ((1, 0), 1)).comp_of_eq ((hz.prod hg).prod hU) rfl
  have hsecond : AnalyticAt ℂ (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦
      M.normalizedPerronFunctional hM p.2.2 -
        M.normalizedPerronFunctional hM 1 - p.1.2) a :=
    (((M.normalizedPerronFunctional hM).analyticAt _ |>.comp hU).sub
      analyticAt_const).sub ht
  exact hfirst.prod hsecond

theorem foldResidual_base (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    foldResidual M hM ((0, 0), (1, 1)) = (0, 0) := by
  simp only [foldResidual, TreeCritical.critical_base, sub_self]

theorem foldResidual_fderiv_unknown (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    fderiv ℂ (fun q : ℂ × C(S, ℂ) ↦ foldResidual M hM ((0, 0), q)) (1, 1) =
      foldBaseDerivative M hM := by
  let K := M.kernel.complexActionCLM M.mu
  let d := TreeCritical.degree M
  let ell := M.normalizedPerronFunctional hM
  let a : ℂ × C(S, ℂ) := (1, 1)
  have hsnd := hasFDerivAt_snd (𝕜 := ℂ) (p := a)
  have hfst := hasFDerivAt_fst (𝕜 := ℂ) (p := a)
  have hinner := (K.hasFDerivAt.comp a hsnd).const_add (-d)
  have hexp := (hasFDerivAt_exp (𝕂 := ℂ) (x := -d + K 1)).comp a hinner
  have hfirst := hsnd.sub (hfst.smul hexp)
  have hsecond := (ell.hasFDerivAt.comp a hsnd).sub_const (ell 1)
  have h := (hfirst.prodMk hsecond).fderiv
  convert h using 1
  · congr 1
    funext q
    simp only [foldResidual, TreeCritical.residual, TreeAnalytic.residual, zero_sub, sub_zero]
    rfl
  · ext q <;>
      simp only [foldBaseDerivative, a, d, K, ell, TreeCritical.degree, Function.comp_apply,
        neg_add_cancel, NormedSpace.exp_zero,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
        sub_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, one_apply_eq_self, one_smul, add_apply,
        ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply] <;> abel

theorem foldResidual_partial (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    fderiv ℂ (foldResidual M hM) ((0, 0), (1, 1)) ∘L
      ContinuousLinearMap.inr ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ)) =
        foldBaseDerivative M hM := by
  let a : ℂ × C(S, ℂ) := (1, 1)
  have hj := (hasFDerivAt_const (𝕜 := ℂ) ((0, 0) : C(S, ℂ) × ℂ) a).prodMk
    (hasFDerivAt_id a)
  have h := ((foldResidual_analytic M hM).hasStrictFDerivAt.hasFDerivAt.comp a hj).fderiv
  have hinr : ContinuousLinearMap.inr ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ)) =
      ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℂ (ℂ × C(S, ℂ))) := by
    ext q <;> rfl
  rw [hinr, ← h]
  exact foldResidual_fderiv_unknown M hM

theorem foldResidual_fderiv_apply (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (v : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ))) :
    fderiv ℂ (foldResidual M hM) ((0, 0), (1, 1)) v =
      (v.2.2 - M.kernel.complexAction M.mu v.2.2 -
        v.2.1 • (1 : C(S, ℂ)) - v.1.1,
        M.normalizedPerronFunctional hM v.2.2 - v.1.2) := by
  let K := M.kernel.complexActionCLM M.mu
  let d := TreeCritical.degree M
  let ell := M.normalizedPerronFunctional hM
  let a : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) := ((0, 0), (1, 1))
  have hz : HasFDerivAt (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦ p.2.1)
      ((ContinuousLinearMap.fst ℂ ℂ C(S, ℂ)).comp
        (ContinuousLinearMap.snd ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ)))) a :=
    (hasFDerivAt_fst (𝕜 := ℂ) (p := a.2)).comp a
      (hasFDerivAt_snd (𝕜 := ℂ) (p := a))
  have hg : HasFDerivAt (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦ p.1.1)
      ((ContinuousLinearMap.fst ℂ C(S, ℂ) ℂ).comp
        (ContinuousLinearMap.fst ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ)))) a :=
    (hasFDerivAt_fst (𝕜 := ℂ) (p := a.1)).comp a
      (hasFDerivAt_fst (𝕜 := ℂ) (p := a))
  have ht : HasFDerivAt (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦ p.1.2)
      ((ContinuousLinearMap.snd ℂ C(S, ℂ) ℂ).comp
        (ContinuousLinearMap.fst ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ)))) a :=
    (hasFDerivAt_snd (𝕜 := ℂ) (p := a.1)).comp a
      (hasFDerivAt_fst (𝕜 := ℂ) (p := a))
  have hU : HasFDerivAt (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦ p.2.2)
      ((ContinuousLinearMap.snd ℂ ℂ C(S, ℂ)).comp
        (ContinuousLinearMap.snd ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ)))) a :=
    (hasFDerivAt_snd (𝕜 := ℂ) (p := a.2)).comp a
      (hasFDerivAt_snd (𝕜 := ℂ) (p := a))
  have hinner := (hg.sub_const d).add (K.hasFDerivAt.comp a hU)
  have hexp := (hasFDerivAt_exp (𝕂 := ℂ) (x := (0 : C(S, ℂ)) - d + K 1)).comp a hinner
  have hfirst := hU.sub (hz.smul hexp)
  have hsecond := ((ell.hasFDerivAt.comp a hU).sub_const (ell 1)).sub ht
  have heq : foldResidual M hM =
      (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦
        (p.2.2 - p.2.1 • NormedSpace.exp (p.1.1 - d + K p.2.2),
          ell p.2.2 - ell 1 - p.1.2)) := rfl
  have hres := (hfirst.prodMk hsecond).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun p ↦ congrFun heq p))
  rw [hres.fderiv]
  simp only [a, d, K, ell, TreeCritical.degree, Function.comp_apply, Pi.add_apply,
    zero_sub, neg_add_cancel,
    NormedSpace.exp_zero, one_smul, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, add_apply]
  apply Prod.ext
  · change v.2.2 - (v.1.1 + M.kernel.complexActionCLM M.mu v.2.2 +
        v.2.1 • (1 : C(S, ℂ))) = _
    simp only [ContinuousKernel.complexActionCLM_apply]
    abel_nf
  · abel

/-- A joint analytic local parametrization of every tree solution near the critical point.
The scalar parameter is exactly the Perron coordinate of the profile deviation. -/
theorem foldCurve_germ (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ ψ : C(S, ℂ) × ℂ → ℂ × C(S, ℂ),
      AnalyticAt ℂ ψ (0, 0) ∧ ψ (0, 0) = (1, 1) ∧
      (∀ᶠ q in 𝓝 ((0, 0) : C(S, ℂ) × ℂ),
        TreeCritical.residual M (((ψ q).1, q.1), (ψ q).2) = 0 ∧
        M.normalizedPerronFunctional hM ((ψ q).2 - 1) = q.2) ∧
      (∀ᶠ p in 𝓝 ((((0, 0) : C(S, ℂ) × ℂ), ((1, 1) : ℂ × C(S, ℂ)))),
        foldResidual M hM p = (0, 0) ↔ ψ p.1 = p.2) := by
  let f := foldResidual M hM
  let a : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) := ((0, 0), (1, 1))
  have hc : ContDiffAt ℂ ω f a := (foldResidual_analytic M hM).contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hi : (fderiv ℂ f a ∘L
      ContinuousLinearMap.inr ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ))).IsInvertible := by
    rw [foldResidual_partial]
    exact foldBaseDerivative_invertible M hM
  refine ⟨hc.implicitFunction hn hi, (hc.contDiffAt_implicitFunction hn hi).analyticAt,
    hc.implicitFunction_apply_self hn hi, ?_, ?_⟩
  · filter_upwards [hc.eventually_apply_implicitFunction hn hi] with q hq
    have hzero : f a = (0, 0) := foldResidual_base M hM
    rw [hzero] at hq
    have hfirst := congrArg Prod.fst hq
    have hsecond := congrArg Prod.snd hq
    exact ⟨hfirst, by
      change M.normalizedPerronFunctional hM (hc.implicitFunction hn hi q).2 -
        M.normalizedPerronFunctional hM 1 - q.2 = 0 at hsecond
      rw [← map_sub] at hsecond
      exact sub_eq_zero.mp hsecond⟩
  · have h := hc.eventually_apply_eq_iff_implicitFunction hn hi
    have hzero : f a = (0, 0) := foldResidual_base M hM
    simpa only [hzero] using h

def foldCurve (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    C(S, ℂ) × ℂ → ℂ × C(S, ℂ) :=
  Classical.choose (foldCurve_germ M hM)

theorem foldCurve_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (foldCurve M hM) (0, 0) :=
  (Classical.choose_spec (foldCurve_germ M hM)).1

theorem foldCurve_base (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    foldCurve M hM (0, 0) = (1, 1) :=
  (Classical.choose_spec (foldCurve_germ M hM)).2.1

theorem foldCurve_equations (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ q in 𝓝 ((0, 0) : C(S, ℂ) × ℂ),
      TreeCritical.residual M (((foldCurve M hM q).1, q.1), (foldCurve M hM q).2) = 0 ∧
      M.normalizedPerronFunctional hM ((foldCurve M hM q).2 - 1) = q.2 :=
  (Classical.choose_spec (foldCurve_germ M hM)).2.2.1

theorem foldCurve_tangent (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fderiv ℂ (foldCurve M hM) (0, 0)) (0, 1) =
      (0, M.complexPerronFunction hM) := by
  let ψ := foldCurve M hM
  let q₀ : C(S, ℂ) × ℂ := (0, 0)
  let a : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) := (q₀, (1, 1))
  have hψ := foldCurve_analytic M hM
  have hψ0 := foldCurve_base M hM
  have heq : (fun q ↦ foldResidual M hM (q, ψ q)) =ᶠ[𝓝 q₀]
      (fun _ ↦ ((0, 0) : C(S, ℂ) × ℂ)) := by
    filter_upwards [foldCurve_equations M hM] with q hq
    apply Prod.ext
    · exact hq.1
    · change M.normalizedPerronFunctional hM (ψ q).2 -
        M.normalizedPerronFunctional hM 1 - q.2 = 0
      rw [← map_sub, hq.2]
      ring
  have hD : fderiv ℂ (fun q ↦ foldResidual M hM (q, ψ q)) q₀ = 0 := by
    have h := heq.fderiv_eq (𝕜 := ℂ)
    simpa using h
  have hj := (hasFDerivAt_id q₀).prodMk hψ.hasStrictFDerivAt.hasFDerivAt
  have ha : (q₀, ψ q₀) = a := by
    exact congrArg (fun t : ℂ × C(S, ℂ) ↦ (q₀, t)) hψ0
  have houter : HasFDerivAt (foldResidual M hM)
      (fderiv ℂ (foldResidual M hM) a) (q₀, ψ q₀) := by
    rw [ha]
    exact (foldResidual_analytic M hM).hasStrictFDerivAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun q ↦ foldResidual M hM (q, ψ q))
      ((fderiv ℂ (foldResidual M hM) a) ∘L
        ((ContinuousLinearMap.id ℂ (C(S, ℂ) × ℂ)).prod
          (fderiv ℂ ψ q₀))) q₀ := by
    simpa only [Function.comp_def, id_eq] using (houter.comp q₀ hj)
  have hzero := congrArg (fun L : (C(S, ℂ) × ℂ) →L[ℂ] (C(S, ℂ) × ℂ) ↦ L (0, 1))
    (hcomp.fderiv.symm.trans hD)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply] at hzero
  let v := (fderiv ℂ ψ q₀) (0, 1)
  have hv : foldBaseDerivative M hM v = ((0 : C(S, ℂ)), 1) := by
    have hf := foldResidual_fderiv_apply M hM ((0, 1), v)
    rw [hf] at hzero
    rw [foldBaseDerivative_apply]
    apply Prod.ext
    · change v.2 - M.kernel.complexAction M.mu v.2 - v.1 • (1 : C(S, ℂ)) = 0
      have hs := congrArg Prod.fst hzero
      simpa using hs
    · change M.normalizedPerronFunctional hM v.2 = 1
      have hs := congrArg Prod.snd hzero
      simpa only [Prod.fst, Prod.snd] using sub_eq_zero.mp hs
  have htarget : foldBaseDerivative M hM (0, M.complexPerronFunction hM) =
      ((0 : C(S, ℂ)), 1) := by
    rw [foldBaseDerivative_apply, M.normalizedPerronFunctional_perronFunction]
    simp only [M.complexPerronFunction_fixed hM, sub_self, zero_smul]
  exact (foldBaseDerivative_injective M hM (hv.trans htarget.symm))

/-- The coordinate of the actual critical profile on the analytic fold curve. -/
def criticalCoordinate (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (g : C(S, ℂ)) : ℂ :=
  M.normalizedPerronFunctional hM (RadiusResponse.profile M hM g - 1)

theorem criticalCoordinate_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (criticalCoordinate M hM) 0 := by
  unfold criticalCoordinate
  exact (M.normalizedPerronFunctional hM).analyticAt _ |>.comp
    ((RadiusResponse.profile_analytic M hM).sub analyticAt_const)

theorem criticalCoordinate_base (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    criticalCoordinate M hM 0 = 0 := by
  simp only [criticalCoordinate, RadiusResponse.profile_base, sub_self, map_zero]

theorem criticalPair_on_foldCurve (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ g in 𝓝 (0 : C(S, ℂ)),
      foldCurve M hM (g, criticalCoordinate M hM g) = CriticalPair.criticalPair M hM g := by
  have hcp := Classical.choose_spec (CriticalPair.criticalPair_germ M hM)
  rw [← CriticalPair.criticalPair] at hcp
  have hfold := (Classical.choose_spec (foldCurve_germ M hM)).2.2.2
  rw [← foldCurve] at hfold
  let j : C(S, ℂ) → (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) :=
    fun g ↦ ((g, criticalCoordinate M hM g), CriticalPair.criticalPair M hM g)
  have hj : Filter.Tendsto j (𝓝 0) (𝓝 ((0, 0), (1, 1))) := by
    have hleft : Filter.Tendsto (fun g : C(S, ℂ) ↦ (g, criticalCoordinate M hM g))
        (𝓝 0) (𝓝 (0, 0)) := by
      simpa only [id_eq, criticalCoordinate_base] using
        (continuousAt_id.tendsto.prodMk_nhds
          (criticalCoordinate_analytic M hM).continuousAt.tendsto)
    have hright : Filter.Tendsto (CriticalPair.criticalPair M hM)
        (𝓝 0) (𝓝 (1, 1)) := by
      simpa only [hcp.2.1] using hcp.1.continuousAt.tendsto
    exact hleft.prodMk_nhds hright
  filter_upwards [hcp.2.2.1, hj.eventually hfold] with g heq hu
  apply hu.mp
  apply Prod.ext
  · exact sub_eq_zero.mpr heq.1
  · change M.normalizedPerronFunctional hM (RadiusResponse.profile M hM g) -
      M.normalizedPerronFunctional hM 1 - criticalCoordinate M hM g = 0
    rw [criticalCoordinate, ← map_sub]
    ring

def centeredFoldCurve (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (q : C(S, ℂ) × ℂ) : ℂ × C(S, ℂ) :=
  foldCurve M hM (q.1, criticalCoordinate M hM q.1 + q.2)

theorem centeredFoldCurve_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (centeredFoldCurve M hM) (0, 0) := by
  have hfst : AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦ q.1)
      ((0, 0) : C(S, ℂ) × ℂ) := analyticAt_fst
  have hsnd : AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦ q.2)
      ((0, 0) : C(S, ℂ) × ℂ) := analyticAt_snd
  have hcrit : AnalyticAt ℂ
      (fun q : C(S, ℂ) × ℂ ↦ criticalCoordinate M hM q.1) (0, 0) :=
    (criticalCoordinate_analytic M hM).comp_of_eq hfst rfl
  have harg : AnalyticAt ℂ
      (fun q : C(S, ℂ) × ℂ ↦ (q.1, criticalCoordinate M hM q.1 + q.2)) (0, 0) :=
    hfst.prod (hcrit.add hsnd)
  unfold centeredFoldCurve
  exact (foldCurve_analytic M hM).comp_of_eq harg (by
    simp only [criticalCoordinate_base, zero_add])

theorem centeredFoldCurve_critical (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ g in 𝓝 (0 : C(S, ℂ)),
      centeredFoldCurve M hM (g, 0) = CriticalPair.criticalPair M hM g := by
  filter_upwards [criticalPair_on_foldCurve M hM] with g hg
  simpa only [centeredFoldCurve, add_zero] using hg

end PerronWright.TreeFold
