import PerronWright.Analysis.FiniteIrreducibleComplexCritical

/-!
# A proved finite analytic tree fold germ

The full joint tree equation uses the actual discrete BJR kernel.  Its
Perron-coordinate augmentation has a constructed invertible derivative,
so the Banach analytic implicit-function theorem gives a genuine local
solution germ.  No fold, inverse or primitive hypothesis is assumed.
-/

open scoped Topology ContDiff

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def foldBaseDerivative (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    (ℂ × C(S, ℂ)) →L[ℂ] (C(S, ℂ) × ℂ) :=
  (((ContinuousLinearMap.id ℂ C(S, ℂ) - M.complexOperator).comp
      (ContinuousLinearMap.snd ℂ ℂ C(S, ℂ))) -
    (ContinuousLinearMap.fst ℂ ℂ C(S, ℂ)).smulRight (1 : C(S, ℂ))).prod
    ((M.normalizedPerronFunctional hcrit).comp (ContinuousLinearMap.snd ℂ ℂ C(S, ℂ)))

theorem foldBaseDerivative_apply (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (q : ℂ × C(S, ℂ)) :
    M.foldBaseDerivative hcrit q =
      (q.2 - M.complexOperator q.2 - q.1 • (1 : C(S, ℂ)),
        M.normalizedPerronFunctional hcrit q.2) := rfl

theorem foldBaseDerivative_injective (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    Function.Injective (M.foldBaseDerivative hcrit) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q hq
  have hfirst := congrArg Prod.fst hq
  have hsecond := congrArg Prod.snd hq
  change q.2 - M.complexOperator q.2 - q.1 • (1 : C(S, ℂ)) = 0 at hfirst
  change M.normalizedPerronFunctional hcrit q.2 = 0 at hsecond
  have hrho := congrArg (M.normalizedPerronFunctional hcrit) hfirst
  simp only [map_sub, M.normalizedPerronFunctional_action hcrit, map_smul,
    smul_eq_mul, sub_self, map_zero, zero_sub] at hrho
  have hrho0 : q.1 = 0 := (mul_eq_zero.mp (neg_eq_zero.mp hrho)).resolve_right
    (M.normalizedPerronFunctional_one_ne_zero hcrit)
  rw [hrho0, zero_smul, sub_zero] at hfirst
  have hf := M.complex_fixed_eq_perronFunctional_smul hcrit q.2 (sub_eq_zero.mp hfirst).symm
  rw [hsecond, zero_smul] at hf
  exact Prod.ext hrho0 hf

theorem foldBaseDerivative_surjective (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    Function.Surjective (M.foldBaseDerivative hcrit) := by
  rintro ⟨y, c⟩
  let ell := M.normalizedPerronFunctional hcrit
  let u := M.complexPerronFunction hcrit
  let r : ℂ := -(ell y) / ell 1
  let f : C(S, ℂ) := y + r • 1
  let w : C(S, ℂ) := M.augmentedKernelInverse hcrit f
  have h1 : ell 1 ≠ 0 := M.normalizedPerronFunctional_one_ne_zero hcrit
  have hf : ell f = 0 := by
    change ell (y + (-(ell y) / ell 1) • 1) = 0
    rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ h1]
    exact add_neg_cancel _
  obtain ⟨hw0, hw⟩ := M.augmentedKernelInverse_on_complement hcrit f hf
  refine ⟨(r, w + c • u), ?_⟩
  rw [M.foldBaseDerivative_apply]
  apply Prod.ext
  · change (w + c • u) - M.complexOperator (w + c • u) - r • 1 = y
    rw [map_add, map_smul]
    have hu : M.complexOperator u = u := M.complexPerronFunction_fixed hcrit
    rw [hu]
    calc
      _ = (w - M.complexOperator w) - r • 1 := by abel
      _ = y := by
        rw [hw]
        change y + r • 1 - r • 1 = y
        abel
  · change ell (w + c • u) = c
    rw [map_add, map_smul, smul_eq_mul, hw0,
      M.normalizedPerronFunctional_perronFunction]
    ring

theorem foldBaseDerivative_invertible (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    (M.foldBaseDerivative hcrit).IsInvertible :=
  ⟨ContinuousLinearEquiv.ofBijective (M.foldBaseDerivative hcrit)
    (LinearMap.ker_eq_bot.mpr (M.foldBaseDerivative_injective hcrit))
    (LinearMap.range_eq_top.mpr (M.foldBaseDerivative_surjective hcrit)),
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

def foldResidual (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ))) : C(S, ℂ) × ℂ :=
  (M.treeResidual ((p.2.1, p.1.1), p.2.2),
    M.normalizedPerronFunctional hcrit p.2.2 - M.normalizedPerronFunctional hcrit 1 - p.1.2)

theorem foldResidual_analytic (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    AnalyticAt ℂ (M.foldResidual hcrit) ((0, 0), (1, 1)) := by
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
      M.treeResidual ((p.2.1, p.1.1), p.2.2)) a :=
    (M.treeResidual_analytic ((1, 0), 1)).comp_of_eq ((hz.prod hg).prod hU) rfl
  have hsecond : AnalyticAt ℂ (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦
      M.normalizedPerronFunctional hcrit p.2.2 - M.normalizedPerronFunctional hcrit 1 - p.1.2) a :=
    (((M.normalizedPerronFunctional hcrit).analyticAt _ |>.comp hU).sub analyticAt_const).sub ht
  exact hfirst.prod hsecond

theorem foldResidual_base (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    M.foldResidual hcrit ((0, 0), (1, 1)) = (0, 0) := by
  simp only [foldResidual, M.treeResidual_base, sub_self]

theorem foldResidual_fderiv_unknown (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    fderiv ℂ (fun q : ℂ × C(S, ℂ) ↦ M.foldResidual hcrit ((0, 0), q)) (1, 1) =
      M.foldBaseDerivative hcrit := by
  let K := M.complexOperator
  let d := TreeCritical.degree M.bjrModel
  let ell := M.normalizedPerronFunctional hcrit
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
    simp only [foldResidual, treeResidual, TreeCritical.residual, TreeAnalytic.residual,
      zero_sub, sub_zero]
    rfl
  · ext q <;>
      simp only [foldBaseDerivative, a, d, K, ell, TreeCritical.degree, complexOperator,
        bjrModel, Function.comp_apply, neg_add_cancel, NormedSpace.exp_zero,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply, sub_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
        one_apply_eq_self, one_smul, add_apply, ContinuousMap.sub_apply,
        ContinuousMap.smul_apply, ContinuousMap.add_apply] <;> abel

theorem foldResidual_partial (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    fderiv ℂ (M.foldResidual hcrit) ((0, 0), (1, 1)) ∘L
      ContinuousLinearMap.inr ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ)) = M.foldBaseDerivative hcrit := by
  let a : ℂ × C(S, ℂ) := (1, 1)
  have hj := (hasFDerivAt_const (𝕜 := ℂ) ((0, 0) : C(S, ℂ) × ℂ) a).prodMk
    (hasFDerivAt_id a)
  have h := ((M.foldResidual_analytic hcrit).hasStrictFDerivAt.hasFDerivAt.comp a hj).fderiv
  have hinr : ContinuousLinearMap.inr ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ)) =
      ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℂ (ℂ × C(S, ℂ))) := by
    ext q <;> rfl
  rw [hinr, ← h]
  exact M.foldResidual_fderiv_unknown hcrit

/-- A genuine analytic local germ, with local uniqueness for the tree equation
and the prescribed Perron coordinate. -/
theorem foldCurve_germ (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∃ ψ : C(S, ℂ) × ℂ → ℂ × C(S, ℂ),
      AnalyticAt ℂ ψ (0, 0) ∧ ψ (0, 0) = (1, 1) ∧
      (∀ᶠ q in 𝓝 ((0, 0) : C(S, ℂ) × ℂ),
        M.treeResidual (((ψ q).1, q.1), (ψ q).2) = 0 ∧
        M.normalizedPerronFunctional hcrit ((ψ q).2 - 1) = q.2) ∧
      (∀ᶠ p in 𝓝 ((((0, 0) : C(S, ℂ) × ℂ), ((1, 1) : ℂ × C(S, ℂ)))),
        M.foldResidual hcrit p = (0, 0) ↔ ψ p.1 = p.2) := by
  let f := M.foldResidual hcrit
  let a : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) := ((0, 0), (1, 1))
  have hc : ContDiffAt ℂ ω f a := (M.foldResidual_analytic hcrit).contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hi : (fderiv ℂ f a ∘L
      ContinuousLinearMap.inr ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ))).IsInvertible := by
    rw [M.foldResidual_partial]
    exact M.foldBaseDerivative_invertible hcrit
  refine ⟨hc.implicitFunction hn hi, (hc.contDiffAt_implicitFunction hn hi).analyticAt,
    hc.implicitFunction_apply_self hn hi, ?_, ?_⟩
  · filter_upwards [hc.eventually_apply_implicitFunction hn hi] with q hq
    have hzero : f a = (0, 0) := M.foldResidual_base hcrit
    rw [hzero] at hq
    have hfirst := congrArg Prod.fst hq
    have hsecond := congrArg Prod.snd hq
    exact ⟨hfirst, by
      change M.normalizedPerronFunctional hcrit (hc.implicitFunction hn hi q).2 -
        M.normalizedPerronFunctional hcrit 1 - q.2 = 0 at hsecond
      rw [← map_sub] at hsecond
      exact sub_eq_zero.mp hsecond⟩
  · have h := hc.eventually_apply_eq_iff_implicitFunction hn hi
    have hzero : f a = (0, 0) := M.foldResidual_base hcrit
    simpa only [hzero] using h

end PerronWright.FiniteIrreducibleModel
