import PerronWright.Analysis.FiniteIrreducibleAugmented
import PerronWright.Analysis.AnalyticEigenpair

/-! Normalized analytic eigenpairs of the actual finite irreducible kernel.
The inverse and simplicity used here are proved finite conclusions, not B2 assumptions. -/

open scoped Topology ContDiff
noncomputable section
namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem eigenResidual_base (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    eigenResidual (M.complexOperator)
      (M.normalizedPerronFunctional hcrit)
      (1, (1, M.complexPerronFunction hcrit)) = (0, 0) := by
  simp [eigenResidual, M.complexPerronFunction_fixed hcrit,
    M.normalizedPerronFunctional_perronFunction hcrit]

def eigenBaseDerivative (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    (ℂ × C(S, ℂ)) →L[ℂ] (C(S, ℂ) × ℂ) :=
  (((M.complexOperator - ContinuousLinearMap.id ℂ C(S, ℂ)).comp
      (ContinuousLinearMap.snd ℂ ℂ C(S, ℂ))) -
    (ContinuousLinearMap.fst ℂ ℂ C(S, ℂ)).smulRight (M.complexPerronFunction hcrit)).prod
    ((M.normalizedPerronFunctional hcrit).comp (ContinuousLinearMap.snd ℂ ℂ C(S, ℂ)))

theorem eigenBaseDerivative_apply (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (q : ℂ × C(S, ℂ)) :
    eigenBaseDerivative M hcrit q =
      (M.complexOperator q.2 - q.2 - q.1 • M.complexPerronFunction hcrit,
        M.normalizedPerronFunctional hcrit q.2) := rfl

theorem eigenBaseDerivative_injective (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    Function.Injective (eigenBaseDerivative M hcrit) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q hq
  have hfirst := congrArg Prod.fst hq
  have hsecond := congrArg Prod.snd hq
  change M.complexOperator q.2 - q.2 - q.1 • M.complexPerronFunction hcrit = 0 at hfirst
  change M.normalizedPerronFunctional hcrit q.2 = 0 at hsecond
  have hlam := congrArg (M.normalizedPerronFunctional hcrit) hfirst
  simp only [map_sub, M.normalizedPerronFunctional_action hcrit, map_smul,
    M.normalizedPerronFunctional_perronFunction hcrit, smul_eq_mul, mul_one,
    sub_self, map_zero, zero_sub] at hlam
  have hlam0 : q.1 = 0 := neg_eq_zero.mp hlam
  rw [hlam0, zero_smul, sub_zero] at hfirst
  have hf := M.complex_fixed_eq_perronFunctional_smul hcrit q.2 (sub_eq_zero.mp hfirst)
  rw [hsecond, zero_smul] at hf
  exact Prod.ext hlam0 hf

theorem eigenBaseDerivative_surjective (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    Function.Surjective (eigenBaseDerivative M hcrit) := by
  rintro ⟨y, c⟩
  let ell := M.normalizedPerronFunctional hcrit
  let u := M.complexPerronFunction hcrit
  let A := M.augmentedKernelInverse hcrit
  refine ⟨(-ell y, (c + ell y) • u - A y), ?_⟩
  rw [eigenBaseDerivative_apply]
  apply Prod.ext
  · have hr := M.augmentedKernelInverse_right_inverse hcrit y
    rw [M.perronProjection_apply, M.normalizedPerronFunctional_inverse] at hr
    change A y - M.complexOperator (A y) + ell y • u = y at hr
    change M.complexOperator ((c + ell y) • u - A y) -
      ((c + ell y) • u - A y) - (-ell y) • u = y
    rw [map_sub, map_smul]
    have hu : M.complexOperator u = u := M.complexPerronFunction_fixed hcrit
    rw [hu, neg_smul]
    calc
      _ = A y - M.complexOperator (A y) + ell y • u := by
        change (c + ell y) • u - M.complexOperator (A y) -
          ((c + ell y) • u - A y) - -(ell y • u) = _
        abel
      _ = y := hr
  · change ell ((c + ell y) • u - A y) = c
    have hu : ell u = 1 := M.normalizedPerronFunctional_perronFunction hcrit
    have hy : ell (A y) = ell y := M.normalizedPerronFunctional_inverse hcrit y
    rw [map_sub, map_smul, hu, hy, smul_eq_mul, mul_one]
    ring

theorem eigenBaseDerivative_invertible (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    (eigenBaseDerivative M hcrit).IsInvertible := by
  exact ⟨ContinuousLinearEquiv.ofBijective (eigenBaseDerivative M hcrit)
    (LinearMap.ker_eq_bot.mpr (eigenBaseDerivative_injective M hcrit))
    (LinearMap.range_eq_top.mpr (eigenBaseDerivative_surjective M hcrit)),
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

theorem eigenResidual_fderiv_unknown (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    fderiv ℂ (fun q : ℂ × C(S, ℂ) ↦
      eigenResidual (M.complexOperator) (M.normalizedPerronFunctional hcrit) (1, q))
      (1, M.complexPerronFunction hcrit) = eigenBaseDerivative M hcrit := by
  let K := M.complexOperator
  let ell := M.normalizedPerronFunctional hcrit
  let u := M.complexPerronFunction hcrit
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

theorem eigenResidual_partial (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    fderiv ℂ (eigenResidual (M.complexOperator) (M.normalizedPerronFunctional hcrit))
      (1, (1, M.complexPerronFunction hcrit)) ∘L
      ContinuousLinearMap.inr ℂ C(S, ℂ) (ℂ × C(S, ℂ)) = eigenBaseDerivative M hcrit := by
  let a : ℂ × C(S, ℂ) := (1, M.complexPerronFunction hcrit)
  have hj := (hasFDerivAt_const (𝕜 := ℂ) (1 : C(S, ℂ)) a).prodMk (hasFDerivAt_id a)
  have h := ((eigenResidual_analytic (M.complexOperator)
    (M.normalizedPerronFunctional hcrit) (1, a)).hasStrictFDerivAt.hasFDerivAt.comp a hj).fderiv
  have hinr : ContinuousLinearMap.inr ℂ C(S, ℂ) (ℂ × C(S, ℂ)) =
      ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℂ (ℂ × C(S, ℂ))) := by
    ext q <;> rfl
  rw [hinr, ← h]
  exact eigenResidual_fderiv_unknown M hcrit

/-- A normalized analytic eigenpair germ for the actual compact-model operator. -/
theorem eigenpair_germ (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∃ ψ : C(S, ℂ) → ℂ × C(S, ℂ), AnalyticAt ℂ ψ 1 ∧
      ψ 1 = (1, M.complexPerronFunction hcrit) ∧
      (∀ᶠ τ in 𝓝 (1 : C(S, ℂ)),
        M.complexOperator (τ * (ψ τ).2) = (ψ τ).1 • (ψ τ).2 ∧
        M.normalizedPerronFunctional hcrit (ψ τ).2 = 1) ∧
      (∀ᶠ p in 𝓝 ((1 : C(S, ℂ)), (1, M.complexPerronFunction hcrit)),
        eigenResidual (M.complexOperator) (M.normalizedPerronFunctional hcrit) p =
          (0, 0) ↔ ψ p.1 = p.2) := by
  let f := eigenResidual (M.complexOperator) (M.normalizedPerronFunctional hcrit)
  let a : C(S, ℂ) × (ℂ × C(S, ℂ)) := (1, (1, M.complexPerronFunction hcrit))
  have hc : ContDiffAt ℂ ω f a := (eigenResidual_analytic _ _ a).contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hi : (fderiv ℂ f a ∘L ContinuousLinearMap.inr ℂ C(S, ℂ) (ℂ × C(S, ℂ))).IsInvertible := by
    rw [eigenResidual_partial]
    exact eigenBaseDerivative_invertible M hcrit
  refine ⟨hc.implicitFunction hn hi, (hc.contDiffAt_implicitFunction hn hi).analyticAt,
    hc.implicitFunction_apply_self hn hi, ?_, ?_⟩
  · filter_upwards [hc.eventually_apply_implicitFunction hn hi] with τ hτ
    have hzero : f a = (0, 0) := eigenResidual_base M hcrit
    rw [hzero] at hτ
    have hfirst := congrArg Prod.fst hτ
    have hsecond := congrArg Prod.snd hτ
    exact ⟨sub_eq_zero.mp hfirst, sub_eq_zero.mp hsecond⟩
  · have h := hc.eventually_apply_eq_iff_implicitFunction hn hi
    have hzero : f a = (0, 0) := eigenResidual_base M hcrit
    simpa only [hzero] using h

theorem eigenvalue_eigenvector_germs (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∃ lam : C(S, ℂ) → ℂ, ∃ vec : C(S, ℂ) → C(S, ℂ),
      AnalyticAt ℂ lam 1 ∧ AnalyticAt ℂ vec 1 ∧
      lam 1 = 1 ∧ vec 1 = M.complexPerronFunction hcrit ∧
      ∀ᶠ τ in 𝓝 (1 : C(S, ℂ)),
        M.complexOperator (τ * vec τ) = lam τ • vec τ ∧
        M.normalizedPerronFunctional hcrit (vec τ) = 1 := by
  obtain ⟨ψ, hψ, hbase, heq, _⟩ := eigenpair_germ M hcrit
  exact ⟨fun τ ↦ (ψ τ).1, fun τ ↦ (ψ τ).2,
    analyticAt_fst.comp hψ, analyticAt_snd.comp hψ,
    congrArg Prod.fst hbase, congrArg Prod.snd hbase, heq⟩

end PerronWright.FiniteIrreducibleModel



