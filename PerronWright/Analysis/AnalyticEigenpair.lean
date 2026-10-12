import PerronWright.Analysis.PerronFunctional
import PerronWright.Analysis.TreeImplicit
import PerronWright.Analysis.AugmentedInverse

open MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The actual normalized eigenpair equation for the perturbed operator
`K ∘ M_τ`, with no spectral assertion hidden in the definition. -/
def eigenResidual (K : C(S, ℂ) →L[ℂ] C(S, ℂ))
    (ell : C(S, ℂ) →L[ℂ] ℂ)
    (p : C(S, ℂ) × (ℂ × C(S, ℂ))) : C(S, ℂ) × ℂ :=
  (K (p.1 * p.2.2) - p.2.1 • p.2.2, ell p.2.2 - 1)

omit [MeasurableSpace S] [BorelSpace S] in
theorem eigenResidual_analytic (K : C(S, ℂ) →L[ℂ] C(S, ℂ))
    (ell : C(S, ℂ) →L[ℂ] ℂ)
    (p : C(S, ℂ) × (ℂ × C(S, ℂ))) :
    AnalyticAt ℂ (eigenResidual K ell) p := by
  have hτ : AnalyticAt ℂ
      (fun q : C(S, ℂ) × (ℂ × C(S, ℂ)) => q.1) p := analyticAt_fst
  have hLam : AnalyticAt ℂ
      (fun q : C(S, ℂ) × (ℂ × C(S, ℂ)) => q.2.1) p :=
    analyticAt_fst.comp analyticAt_snd
  have hv : AnalyticAt ℂ
      (fun q : C(S, ℂ) × (ℂ × C(S, ℂ)) => q.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  have hfirst : AnalyticAt ℂ
      (fun q : C(S, ℂ) × (ℂ × C(S, ℂ)) =>
        K (q.1 * q.2.2) - q.2.1 • q.2.2) p :=
    ((K.analyticAt _).comp (hτ.mul hv)).sub (hLam.smul hv)
  have hsecond : AnalyticAt ℂ
      (fun q : C(S, ℂ) × (ℂ × C(S, ℂ)) => ell q.2.2 - 1) p :=
    ((ell.analyticAt _).comp hv).sub analyticAt_const
  exact hfirst.prod hsecond

theorem eigenResidual_base (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    eigenResidual (M.kernel.complexActionCLM M.mu)
      (M.normalizedPerronFunctional hM)
      (1, (1, M.complexPerronFunction hM)) = (0, 0) := by
  simp [eigenResidual, M.complexPerronFunction_fixed hM,
    M.normalizedPerronFunctional_perronFunction hM]

def eigenBaseDerivative (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (ℂ × C(S, ℂ)) →L[ℂ] (C(S, ℂ) × ℂ) :=
  (((M.kernel.complexActionCLM M.mu - ContinuousLinearMap.id ℂ C(S, ℂ)).comp
      (ContinuousLinearMap.snd ℂ ℂ C(S, ℂ))) -
    (ContinuousLinearMap.fst ℂ ℂ C(S, ℂ)).smulRight (M.complexPerronFunction hM)).prod
    ((M.normalizedPerronFunctional hM).comp (ContinuousLinearMap.snd ℂ ℂ C(S, ℂ)))

theorem eigenBaseDerivative_apply (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (q : ℂ × C(S, ℂ)) :
    eigenBaseDerivative M hM q =
      (M.kernel.complexAction M.mu q.2 - q.2 - q.1 • M.complexPerronFunction hM,
        M.normalizedPerronFunctional hM q.2) := rfl

theorem eigenBaseDerivative_injective (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    Function.Injective (eigenBaseDerivative M hM) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q hq
  have hfirst := congrArg Prod.fst hq
  have hsecond := congrArg Prod.snd hq
  change M.kernel.complexAction M.mu q.2 - q.2 - q.1 • M.complexPerronFunction hM = 0 at hfirst
  change M.normalizedPerronFunctional hM q.2 = 0 at hsecond
  have hlam := congrArg (M.normalizedPerronFunctional hM) hfirst
  simp only [map_sub, M.normalizedPerronFunctional_action hM, map_smul,
    M.normalizedPerronFunctional_perronFunction hM, smul_eq_mul, mul_one,
    sub_self, map_zero, zero_sub] at hlam
  have hlam0 : q.1 = 0 := neg_eq_zero.mp hlam
  rw [hlam0, zero_smul, sub_zero] at hfirst
  have hf := M.complex_fixed_eq_perronFunctional_smul hM q.2 (sub_eq_zero.mp hfirst)
  rw [hsecond, zero_smul] at hf
  exact Prod.ext hlam0 hf

theorem eigenBaseDerivative_surjective (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    Function.Surjective (eigenBaseDerivative M hM) := by
  rintro ⟨y, c⟩
  let ell := M.normalizedPerronFunctional hM
  let u := M.complexPerronFunction hM
  let A := M.augmentedKernelInverse hM
  refine ⟨(-ell y, (c + ell y) • u - A y), ?_⟩
  rw [eigenBaseDerivative_apply]
  apply Prod.ext
  · have hr := M.augmentedKernelInverse_right_inverse hM y
    rw [M.perronProjection_apply, M.normalizedPerronFunctional_inverse] at hr
    change A y - M.kernel.complexAction M.mu (A y) + ell y • u = y at hr
    change M.kernel.complexActionCLM M.mu ((c + ell y) • u - A y) -
      ((c + ell y) • u - A y) - (-ell y) • u = y
    rw [map_sub, map_smul]
    have hu : M.kernel.complexActionCLM M.mu u = u := M.complexPerronFunction_fixed hM
    rw [hu, neg_smul]
    calc
      _ = A y - M.kernel.complexAction M.mu (A y) + ell y • u := by
        change (c + ell y) • u - M.kernel.complexAction M.mu (A y) -
          ((c + ell y) • u - A y) - -(ell y • u) = _
        abel
      _ = y := hr
  · change ell ((c + ell y) • u - A y) = c
    have hu : ell u = 1 := M.normalizedPerronFunctional_perronFunction hM
    have hy : ell (A y) = ell y := M.normalizedPerronFunctional_inverse hM y
    rw [map_sub, map_smul, hu, hy, smul_eq_mul, mul_one]
    ring

theorem eigenBaseDerivative_invertible (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (eigenBaseDerivative M hM).IsInvertible := by
  exact ⟨ContinuousLinearEquiv.ofBijective (eigenBaseDerivative M hM)
    (LinearMap.ker_eq_bot.mpr (eigenBaseDerivative_injective M hM))
    (LinearMap.range_eq_top.mpr (eigenBaseDerivative_surjective M hM)),
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

theorem eigenResidual_fderiv_unknown (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    fderiv ℂ (fun q : ℂ × C(S, ℂ) ↦
      eigenResidual (M.kernel.complexActionCLM M.mu) (M.normalizedPerronFunctional hM) (1, q))
      (1, M.complexPerronFunction hM) = eigenBaseDerivative M hM := by
  let K := M.kernel.complexActionCLM M.mu
  let ell := M.normalizedPerronFunctional hM
  let u := M.complexPerronFunction hM
  let a : ℂ × C(S, ℂ) := (1, u)
  have hsnd := hasFDerivAt_snd (𝕜 := ℂ) (p := a)
  have hfst := hasFDerivAt_fst (𝕜 := ℂ) (p := a)
  have hfirst := (K.hasFDerivAt.comp a hsnd).sub (hfst.smul hsnd)
  have hsecond := (ell.hasFDerivAt.comp a hsnd).sub_const 1
  have h := (hfirst.prodMk hsecond).fderiv
  convert h using 1
  · congr 1
    funext q
    simp only [eigenResidual, one_mul]
    rfl
  · ext q <;>
      simp only [eigenBaseDerivative, a, K, ell, u, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.comp_apply, sub_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
        one_smul, add_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        ContinuousMap.add_apply] <;> abel

theorem eigenResidual_partial (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    fderiv ℂ (eigenResidual (M.kernel.complexActionCLM M.mu) (M.normalizedPerronFunctional hM))
      (1, (1, M.complexPerronFunction hM)) ∘L
      ContinuousLinearMap.inr ℂ C(S, ℂ) (ℂ × C(S, ℂ)) = eigenBaseDerivative M hM := by
  let a : ℂ × C(S, ℂ) := (1, M.complexPerronFunction hM)
  have hj := (hasFDerivAt_const (𝕜 := ℂ) (1 : C(S, ℂ)) a).prodMk (hasFDerivAt_id a)
  have h := ((eigenResidual_analytic (M.kernel.complexActionCLM M.mu)
    (M.normalizedPerronFunctional hM) (1, a)).hasStrictFDerivAt.hasFDerivAt.comp a hj).fderiv
  have hinr : ContinuousLinearMap.inr ℂ C(S, ℂ) (ℂ × C(S, ℂ)) =
      ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℂ (ℂ × C(S, ℂ))) := by
    ext q <;> rfl
  rw [hinr, ← h]
  exact eigenResidual_fderiv_unknown M hM

/-- A normalized analytic eigenpair germ for the actual compact-model operator. -/
theorem eigenpair_germ (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ ψ : C(S, ℂ) → ℂ × C(S, ℂ), AnalyticAt ℂ ψ 1 ∧
      ψ 1 = (1, M.complexPerronFunction hM) ∧
      (∀ᶠ τ in 𝓝 (1 : C(S, ℂ)),
        M.kernel.complexAction M.mu (τ * (ψ τ).2) = (ψ τ).1 • (ψ τ).2 ∧
        M.normalizedPerronFunctional hM (ψ τ).2 = 1) ∧
      (∀ᶠ p in 𝓝 ((1 : C(S, ℂ)), (1, M.complexPerronFunction hM)),
        eigenResidual (M.kernel.complexActionCLM M.mu) (M.normalizedPerronFunctional hM) p =
          (0, 0) ↔ ψ p.1 = p.2) := by
  let f := eigenResidual (M.kernel.complexActionCLM M.mu) (M.normalizedPerronFunctional hM)
  let a : C(S, ℂ) × (ℂ × C(S, ℂ)) := (1, (1, M.complexPerronFunction hM))
  have hc : ContDiffAt ℂ ω f a := (eigenResidual_analytic _ _ a).contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hi : (fderiv ℂ f a ∘L ContinuousLinearMap.inr ℂ C(S, ℂ) (ℂ × C(S, ℂ))).IsInvertible := by
    rw [eigenResidual_partial]
    exact eigenBaseDerivative_invertible M hM
  refine ⟨hc.implicitFunction hn hi, (hc.contDiffAt_implicitFunction hn hi).analyticAt,
    hc.implicitFunction_apply_self hn hi, ?_, ?_⟩
  · filter_upwards [hc.eventually_apply_implicitFunction hn hi] with τ hτ
    have hzero : f a = (0, 0) := eigenResidual_base M hM
    rw [hzero] at hτ
    have hfirst := congrArg Prod.fst hτ
    have hsecond := congrArg Prod.snd hτ
    exact ⟨sub_eq_zero.mp hfirst, sub_eq_zero.mp hsecond⟩
  · have h := hc.eventually_apply_eq_iff_implicitFunction hn hi
    have hzero : f a = (0, 0) := eigenResidual_base M hM
    simpa only [hzero] using h

theorem eigenvalue_eigenvector_germs (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ lam : C(S, ℂ) → ℂ, ∃ vec : C(S, ℂ) → C(S, ℂ),
      AnalyticAt ℂ lam 1 ∧ AnalyticAt ℂ vec 1 ∧
      lam 1 = 1 ∧ vec 1 = M.complexPerronFunction hM ∧
      ∀ᶠ τ in 𝓝 (1 : C(S, ℂ)),
        M.kernel.complexAction M.mu (τ * vec τ) = lam τ • vec τ ∧
        M.normalizedPerronFunctional hM (vec τ) = 1 := by
  obtain ⟨ψ, hψ, hbase, heq, _⟩ := eigenpair_germ M hM
  exact ⟨fun τ ↦ (ψ τ).1, fun τ ↦ (ψ τ).2,
    analyticAt_fst.comp hψ, analyticAt_snd.comp hψ,
    congrArg Prod.fst hbase, congrArg Prod.snd hbase, heq⟩

end PerronWright

