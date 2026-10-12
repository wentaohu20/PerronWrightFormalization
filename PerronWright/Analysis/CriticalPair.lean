import PerronWright.Analysis.AnalyticEigenpair
import PerronWright.Analysis.FoldCoefficients
import Mathlib.Topology.ContinuousMap.Star

open MeasureTheory PerronWright
open scoped Topology ContDiff

noncomputable section

namespace PerronWright.CriticalPair

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

def eigenpair (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    C(S, ℂ) → ℂ × C(S, ℂ) :=
  Classical.choose (PerronWright.eigenpair_germ M hM)

def eigenvalue (M : CompactBJRModel S) (hM : M.IsRegularCritical) (τ : C(S, ℂ)) : ℂ :=
  (eigenpair M hM τ).1

def eigenvector (M : CompactBJRModel S) (hM : M.IsRegularCritical) (τ : C(S, ℂ)) : C(S, ℂ) :=
  (eigenpair M hM τ).2

theorem eigenvalue_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (eigenvalue M hM) 1 :=
  analyticAt_fst.comp (Classical.choose_spec (PerronWright.eigenpair_germ M hM)).1

theorem eigenvector_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (eigenvector M hM) 1 :=
  analyticAt_snd.comp (Classical.choose_spec (PerronWright.eigenpair_germ M hM)).1

theorem eigenvalue_base (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    eigenvalue M hM 1 = 1 :=
  congrArg Prod.fst (Classical.choose_spec (PerronWright.eigenpair_germ M hM)).2.1

theorem eigenvector_base (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    eigenvector M hM 1 = M.complexPerronFunction hM :=
  congrArg Prod.snd (Classical.choose_spec (PerronWright.eigenpair_germ M hM)).2.1

theorem eigenpair_equations (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ τ in 𝓝 (1 : C(S, ℂ)),
      M.kernel.complexAction M.mu (τ * eigenvector M hM τ) =
        eigenvalue M hM τ • eigenvector M hM τ ∧
      M.normalizedPerronFunctional hM (eigenvector M hM τ) = 1 :=
  (Classical.choose_spec (PerronWright.eigenpair_germ M hM)).2.2.1

theorem eigenvalue_relative_formula (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    eigenvalue M hM =ᶠ[𝓝 (1 : C(S, ℂ))]
      (fun τ ↦ 1 + M.normalizedPerronFunctional hM ((τ - 1) * eigenvector M hM τ)) := by
  filter_upwards [eigenpair_equations M hM] with τ hτ
  have heq := congrArg (M.normalizedPerronFunctional hM) hτ.1
  rw [M.normalizedPerronFunctional_action, map_smul, hτ.2, smul_eq_mul, mul_one] at heq
  rw [sub_mul, one_mul, map_sub, hτ.2, heq]
  ring

theorem eigenvalue_fderiv (M : CompactBJRModel S) (hM : M.IsRegularCritical) (h : C(S, ℂ)) :
    (fderiv ℂ (eigenvalue M hM) 1) h =
      M.normalizedPerronFunctional hM (h * M.complexPerronFunction hM) := by
  let ell := M.normalizedPerronFunctional hM
  let vec := eigenvector M hM
  have hv := (eigenvector_analytic M hM).hasStrictFDerivAt.hasFDerivAt
  have hp := ((hasFDerivAt_id (𝕜 := ℂ) (1 : C(S, ℂ))).sub_const 1).mul hv
  have hc := (ell.hasFDerivAt.comp 1 hp).const_add (1 : ℂ)
  have heq := (eigenvalue_relative_formula M hM).fderiv_eq (𝕜 := ℂ)
  rw [heq]
  have hd : fderiv ℂ (fun τ : C(S, ℂ) ↦
      1 + ell ((τ - 1) * eigenvector M hM τ)) 1 =
      ell ∘L ((M.complexPerronFunction hM) • ContinuousLinearMap.id ℂ C(S, ℂ)) := by
    convert hc.fderiv using 1
    · rfl
    · simp only [id_eq, sub_self, zero_smul, zero_add, eigenvector_base]
  rw [hd]
  change ell (M.complexPerronFunction hM * h) = ell (h * M.complexPerronFunction hM)
  rw [mul_comm]

theorem eigenvalue_fderiv_perron (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fderiv ℂ (eigenvalue M hM) 1) (M.complexPerronFunction hM) =
      (M.beta hM : ℂ) / (M.alpha hM : ℂ) := by
  rw [eigenvalue_fderiv, ← pow_two, FoldCoefficients.normalizedPerronFunctional_perron_sq]

theorem eigenvalue_fderiv_perron_re_pos (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    0 < ((fderiv ℂ (eigenvalue M hM) 1) (M.complexPerronFunction hM)).re := by
  rw [eigenvalue_fderiv_perron, ← Complex.ofReal_div, Complex.ofReal_re]
  exact div_pos (M.beta_pos hM) (M.alpha_pos hM)

theorem eigenvalue_fderiv_perron_ne_zero (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fderiv ℂ (eigenvalue M hM) 1) (M.complexPerronFunction hM) ≠ 0 := by
  rw [eigenvalue_fderiv_perron]
  exact div_ne_zero (Complex.ofReal_ne_zero.mpr (M.beta_pos hM).ne')
    (Complex.ofReal_ne_zero.mpr (M.alpha_pos hM).ne')

def criticalBaseDerivative (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (ℂ × C(S, ℂ)) →L[ℂ] (C(S, ℂ) × ℂ) :=
  (((ContinuousLinearMap.id ℂ C(S, ℂ) - M.kernel.complexActionCLM M.mu).comp
      (ContinuousLinearMap.snd ℂ ℂ C(S, ℂ))) -
    (ContinuousLinearMap.fst ℂ ℂ C(S, ℂ)).smulRight (1 : C(S, ℂ))).prod
    ((fderiv ℂ (eigenvalue M hM) 1).comp (ContinuousLinearMap.snd ℂ ℂ C(S, ℂ)))

theorem criticalBaseDerivative_apply (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (q : ℂ × C(S, ℂ)) :
    criticalBaseDerivative M hM q =
      (q.2 - M.kernel.complexAction M.mu q.2 - q.1 • (1 : C(S, ℂ)),
        (fderiv ℂ (eigenvalue M hM) 1) q.2) := rfl

theorem criticalBaseDerivative_injective (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    Function.Injective (criticalBaseDerivative M hM) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro q hq
  have hfirst := congrArg Prod.fst hq
  have hsecond := congrArg Prod.snd hq
  change q.2 - M.kernel.complexAction M.mu q.2 - q.1 • (1 : C(S, ℂ)) = 0 at hfirst
  change (fderiv ℂ (eigenvalue M hM) 1) q.2 = 0 at hsecond
  have hrho := congrArg (M.normalizedPerronFunctional hM) hfirst
  simp only [map_sub, M.normalizedPerronFunctional_action hM, map_smul,
    FoldCoefficients.normalizedPerronFunctional_one, smul_eq_mul,
    sub_self, map_zero, zero_sub] at hrho
  have hrho0 : q.1 = 0 := (mul_eq_zero.mp (neg_eq_zero.mp hrho)).resolve_right
    (FoldCoefficients.first_scalar_ne_zero M hM)
  rw [hrho0, zero_smul, sub_zero] at hfirst
  have hf := M.complex_fixed_eq_perronFunctional_smul hM q.2 (sub_eq_zero.mp hfirst).symm
  rw [hf, map_smul, smul_eq_mul] at hsecond
  have hell0 : M.normalizedPerronFunctional hM q.2 = 0 :=
    (mul_eq_zero.mp hsecond).resolve_right (eigenvalue_fderiv_perron_ne_zero M hM)
  rw [hell0, zero_smul] at hf
  exact Prod.ext hrho0 hf

theorem criticalBaseDerivative_surjective (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    Function.Surjective (criticalBaseDerivative M hM) := by
  rintro ⟨y, c⟩
  let ell := M.normalizedPerronFunctional hM
  let u := M.complexPerronFunction hM
  let D := fderiv ℂ (eigenvalue M hM) 1
  let r : ℂ := -(ell y) / ell 1
  let f : C(S, ℂ) := y + r • 1
  let w : C(S, ℂ) := M.augmentedKernelInverse hM f
  let t : ℂ := (c - D w) / D u
  have h1 : ell 1 ≠ 0 := by
    rw [FoldCoefficients.normalizedPerronFunctional_one]
    exact FoldCoefficients.first_scalar_ne_zero M hM
  have hD : D u ≠ 0 := eigenvalue_fderiv_perron_ne_zero M hM
  have hf : ell f = 0 := by
    change ell (y + (-(ell y) / ell 1) • 1) = 0
    rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ h1]
    exact add_neg_cancel _
  have hw : w - M.kernel.complexAction M.mu w = f :=
    (M.augmentedKernelInverse_on_complement hM f hf).2
  refine ⟨(r, w + t • u), ?_⟩
  rw [criticalBaseDerivative_apply]
  apply Prod.ext
  · change (w + t • u) - M.kernel.complexActionCLM M.mu (w + t • u) - r • 1 = y
    rw [map_add, map_smul]
    have hu : M.kernel.complexActionCLM M.mu u = u := M.complexPerronFunction_fixed hM
    rw [hu]
    calc
      _ = (w - M.kernel.complexAction M.mu w) - r • 1 := by
        change (w + t • u) - (M.kernel.complexAction M.mu w + t • u) - r • 1 = _
        abel
      _ = y := by
        rw [hw]
        change y + r • 1 - r • 1 = y
        abel
  · change D (w + t • u) = c
    rw [map_add, map_smul, smul_eq_mul]
    change D w + ((c - D w) / D u) * D u = c
    rw [div_mul_cancel₀ _ hD]
    ring

theorem criticalBaseDerivative_invertible (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (criticalBaseDerivative M hM).IsInvertible := by
  exact ⟨ContinuousLinearEquiv.ofBijective (criticalBaseDerivative M hM)
    (LinearMap.ker_eq_bot.mpr (criticalBaseDerivative_injective M hM))
    (LinearMap.range_eq_top.mpr (criticalBaseDerivative_surjective M hM)),
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- The actual tree equation together with the critical eigenvalue constraint. -/
def criticalResidual (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (p : C(S, ℂ) × (ℂ × C(S, ℂ))) : C(S, ℂ) × ℂ :=
  (TreeCritical.residual M ((p.2.1, p.1), p.2.2), eigenvalue M hM p.2.2 - 1)

theorem criticalResidual_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (criticalResidual M hM) (0, (1, 1)) := by
  let a : C(S, ℂ) × (ℂ × C(S, ℂ)) := (0, (1, 1))
  have hρ : AnalyticAt ℂ (fun p : C(S, ℂ) × (ℂ × C(S, ℂ)) ↦ p.2.1) a :=
    analyticAt_fst.comp analyticAt_snd
  have hg : AnalyticAt ℂ (fun p : C(S, ℂ) × (ℂ × C(S, ℂ)) ↦ p.1) a := analyticAt_fst
  have hτ : AnalyticAt ℂ (fun p : C(S, ℂ) × (ℂ × C(S, ℂ)) ↦ p.2.2) a :=
    analyticAt_snd.comp analyticAt_snd
  have ht : AnalyticAt ℂ (fun p : C(S, ℂ) × (ℂ × C(S, ℂ)) ↦
      TreeCritical.residual M ((p.2.1, p.1), p.2.2)) a := by
    exact (TreeAnalytic.residual_analytic M.kernel M.mu (TreeCritical.degree M)
      ((1, 0), 1)).comp_of_eq ((hρ.prod hg).prod hτ) rfl
  have hlam : AnalyticAt ℂ (fun p : C(S, ℂ) × (ℂ × C(S, ℂ)) ↦
      eigenvalue M hM p.2.2 - 1) a :=
    ((eigenvalue_analytic M hM).comp_of_eq hτ rfl).sub analyticAt_const
  exact ht.prod hlam

theorem criticalResidual_base (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    criticalResidual M hM (0, (1, 1)) = (0, 0) := by
  simp only [criticalResidual, TreeCritical.critical_base, eigenvalue_base, sub_self]

theorem criticalResidual_fderiv_unknown (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    fderiv ℂ (fun q : ℂ × C(S, ℂ) ↦ criticalResidual M hM (0, q)) (1, 1) =
      criticalBaseDerivative M hM := by
  let K := M.kernel.complexActionCLM M.mu
  let d := TreeCritical.degree M
  let a : ℂ × C(S, ℂ) := (1, 1)
  have hsnd := hasFDerivAt_snd (𝕜 := ℂ) (p := a)
  have hfst := hasFDerivAt_fst (𝕜 := ℂ) (p := a)
  have hinner := (K.hasFDerivAt.comp a hsnd).const_add (-d)
  have hexp := (hasFDerivAt_exp (𝕂 := ℂ) (x := -d + K 1)).comp a hinner
  have hfirst := hsnd.sub (hfst.smul hexp)
  have hsecond := ((eigenvalue_analytic M hM).hasStrictFDerivAt.hasFDerivAt.comp a hsnd).sub_const 1
  have h := (hfirst.prodMk hsecond).fderiv
  convert h using 1
  · congr 1
    funext q
    simp only [criticalResidual, TreeCritical.residual, TreeAnalytic.residual, zero_sub]
    rfl
  · ext q <;>
      simp only [criticalBaseDerivative, a, d, K, TreeCritical.degree, Function.comp_apply,
        neg_add_cancel, NormedSpace.exp_zero,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
        sub_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, one_apply_eq_self, one_smul, add_apply,
        ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply] <;> abel

theorem criticalResidual_partial (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    fderiv ℂ (criticalResidual M hM) (0, (1, 1)) ∘L
      ContinuousLinearMap.inr ℂ C(S, ℂ) (ℂ × C(S, ℂ)) = criticalBaseDerivative M hM := by
  let a : ℂ × C(S, ℂ) := (1, 1)
  have hj := (hasFDerivAt_const (𝕜 := ℂ) (0 : C(S, ℂ)) a).prodMk (hasFDerivAt_id a)
  have h := ((criticalResidual_analytic M hM).hasStrictFDerivAt.hasFDerivAt.comp a hj).fderiv
  have hinr : ContinuousLinearMap.inr ℂ C(S, ℂ) (ℂ × C(S, ℂ)) =
      ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℂ (ℂ × C(S, ℂ))) := by
    ext q <;> rfl
  rw [hinr, ← h]
  exact criticalResidual_fderiv_unknown M hM

/-- The actual critical pair exists analytically, with no additional operator assumptions. -/
theorem criticalPair_germ (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ ψ : C(S, ℂ) → ℂ × C(S, ℂ), AnalyticAt ℂ ψ 0 ∧ ψ 0 = (1, 1) ∧
      (∀ᶠ g in 𝓝 (0 : C(S, ℂ)),
        (ψ g).2 = (ψ g).1 • NormedSpace.exp
          (g - TreeCritical.degree M + M.kernel.complexActionCLM M.mu (ψ g).2) ∧
        eigenvalue M hM (ψ g).2 = 1) ∧
      (∀ᶠ p in 𝓝 ((0 : C(S, ℂ)), (1, (1 : C(S, ℂ)))),
        criticalResidual M hM p = (0, 0) ↔ ψ p.1 = p.2) := by
  let f := criticalResidual M hM
  let a : C(S, ℂ) × (ℂ × C(S, ℂ)) := (0, (1, 1))
  have hc : ContDiffAt ℂ ω f a := (criticalResidual_analytic M hM).contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hi : (fderiv ℂ f a ∘L ContinuousLinearMap.inr ℂ C(S, ℂ) (ℂ × C(S, ℂ))).IsInvertible := by
    rw [criticalResidual_partial]
    exact criticalBaseDerivative_invertible M hM
  refine ⟨hc.implicitFunction hn hi, (hc.contDiffAt_implicitFunction hn hi).analyticAt,
    hc.implicitFunction_apply_self hn hi, ?_, ?_⟩
  · filter_upwards [hc.eventually_apply_implicitFunction hn hi] with g hg
    have hzero : f a = (0, 0) := criticalResidual_base M hM
    rw [hzero] at hg
    have hfirst := congrArg Prod.fst hg
    have hsecond := congrArg Prod.snd hg
    exact ⟨sub_eq_zero.mp hfirst, sub_eq_zero.mp hsecond⟩
  · have h := hc.eventually_apply_eq_iff_implicitFunction hn hi
    have hzero : f a = (0, 0) := criticalResidual_base M hM
    simpa only [hzero] using h

theorem complexAction_star (M : CompactBJRModel S) (f : C(S, ℂ)) :
    M.kernel.complexActionCLM M.mu (star f) = star (M.kernel.complexActionCLM M.mu f) := by
  ext x
  simp only [ContinuousKernel.complexActionCLM_apply, ContinuousKernel.complexAction_apply,
    ContinuousMap.star_apply, Complex.star_def]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [map_mul, Complex.conj_ofReal]

theorem perronFunction_star (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    star (M.complexPerronFunction hM) = M.complexPerronFunction hM := by
  ext x
  simp

theorem perronFunctional_star (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℂ)) :
    M.normalizedPerronFunctional hM (star f) = star (M.normalizedPerronFunctional hM f) := by
  simp only [CompactBJRModel.normalizedPerronFunctional, smul_apply, smul_eq_mul,
    CompactBJRModel.weightedIntegralComplexCLM_apply,
    CompactBJRModel.weightedIntegralComplex, ContinuousMap.star_apply, Complex.star_def,
    map_mul, map_inv₀, Complex.conj_ofReal]
  congr 1
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with y
  simp

theorem eigenResidual_star (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (p : C(S, ℂ) × (ℂ × C(S, ℂ))) :
    eigenResidual (M.kernel.complexActionCLM M.mu) (M.normalizedPerronFunctional hM)
      (star p) =
    star (eigenResidual (M.kernel.complexActionCLM M.mu)
      (M.normalizedPerronFunctional hM) p) := by
  simp only [eigenResidual, Prod.star_def, star_sub, star_smul, star_one]
  rw [← star_mul', complexAction_star, perronFunctional_star]

theorem eigenpair_star (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ τ in 𝓝 (1 : C(S, ℂ)),
      eigenpair M hM (star τ) = star (eigenpair M hM τ) := by
  have hs := Classical.choose_spec (PerronWright.eigenpair_germ M hM)
  rw [← eigenpair] at hs
  have hc : Filter.Tendsto (fun τ : C(S, ℂ) ↦ (star τ, star (eigenpair M hM τ)))
      (𝓝 1) (𝓝 (1, (1, M.complexPerronFunction hM))) := by
    simpa only [id_eq, hs.2.1, Prod.star_def, star_one, perronFunction_star] using
      (continuousAt_id.star.tendsto.prodMk_nhds hs.1.continuousAt.star.tendsto)
  filter_upwards [hs.2.2.1, hc.eventually hs.2.2.2] with τ heq hu
  apply hu.mp
  have hz : eigenResidual (M.kernel.complexActionCLM M.mu)
      (M.normalizedPerronFunctional hM) (τ, eigenpair M hM τ) = (0, 0) :=
    Prod.ext (sub_eq_zero.mpr heq.1) (sub_eq_zero.mpr heq.2)
  change eigenResidual (M.kernel.complexActionCLM M.mu)
    (M.normalizedPerronFunctional hM) (star (τ, eigenpair M hM τ)) = (0, 0)
  rw [eigenResidual_star, hz]
  simp only [Prod.star_def, star_zero]

theorem eigenvalue_star (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ τ in 𝓝 (1 : C(S, ℂ)),
      eigenvalue M hM (star τ) = star (eigenvalue M hM τ) := by
  filter_upwards [eigenpair_star M hM] with τ hτ
  exact congrArg Prod.fst hτ

theorem degree_star (M : CompactBJRModel S) : star (TreeCritical.degree M) =
    TreeCritical.degree M := by
  rw [TreeCritical.degree, ← complexAction_star, star_one]

theorem treeResidual_star (M : CompactBJRModel S)
    (p : (ℂ × C(S, ℂ)) × C(S, ℂ)) :
    TreeCritical.residual M (star p) = star (TreeCritical.residual M p) := by
  simp only [TreeCritical.residual, TreeAnalytic.residual, Prod.star_def, star_sub,
    star_add, star_smul, NormedSpace.star_exp, degree_star, ← complexAction_star]

def criticalPair (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    C(S, ℂ) → ℂ × C(S, ℂ) := Classical.choose (criticalPair_germ M hM)

theorem criticalPair_star (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ g in 𝓝 (0 : C(S, ℂ)),
      criticalPair M hM (star g) = star (criticalPair M hM g) := by
  have hs := Classical.choose_spec (criticalPair_germ M hM)
  rw [← criticalPair] at hs
  have hc : Filter.Tendsto (fun g : C(S, ℂ) ↦ (star g, star (criticalPair M hM g)))
      (𝓝 0) (𝓝 (0, (1, 1))) := by
    simpa only [id_eq, hs.2.1, Prod.star_def, star_zero, star_one] using
      (continuousAt_id.star.tendsto.prodMk_nhds hs.1.continuousAt.star.tendsto)
  have ht : Filter.Tendsto (fun g ↦ (criticalPair M hM g).2) (𝓝 0) (𝓝 1) := by
    simpa only [hs.2.1] using hs.1.continuousAt.snd.tendsto
  filter_upwards [hs.2.2.1, hc.eventually hs.2.2.2,
    ht.eventually (eigenvalue_star M hM)] with g heq hu hlam
  apply hu.mp
  apply Prod.ext
  · change TreeCritical.residual M (star (((criticalPair M hM g).1, g),
        (criticalPair M hM g).2)) = 0
    rw [treeResidual_star]
    have hz : TreeCritical.residual M (((criticalPair M hM g).1, g),
        (criticalPair M hM g).2) = 0 := sub_eq_zero.mpr heq.1
    rw [hz, star_zero]
  · change eigenvalue M hM (star (criticalPair M hM g).2) - 1 = 0
    rw [hlam, heq.2, star_one, sub_self]

theorem re_pos_of_norm_sub_one_lt (z : ℂ) (hz : ‖z - 1‖ < 1) : 0 < z.re := by
  have hr := lt_of_le_of_lt (Complex.abs_re_le_norm (z - 1)) hz
  simp only [Complex.sub_re, Complex.one_re] at hr
  have hl := (abs_lt.mp hr).1
  linarith

/-- The actual analytic critical pair is real and strictly positive for every sufficiently
small real field, uniformly over the compact type space. -/
theorem criticalPair_real_positive (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ g in 𝓝 (0 : C(S, ℂ)), star g = g →
      (criticalPair M hM g).1.im = 0 ∧ 0 < (criticalPair M hM g).1.re ∧
      ∀ x, ((criticalPair M hM g).2 x).im = 0 ∧
        0 < ((criticalPair M hM g).2 x).re := by
  have hs := Classical.choose_spec (criticalPair_germ M hM)
  rw [← criticalPair] at hs
  have hρ : Filter.Tendsto (fun g ↦ (criticalPair M hM g).1) (𝓝 0) (𝓝 1) := by
    simpa only [hs.2.1] using hs.1.continuousAt.fst.tendsto
  have hτ : Filter.Tendsto (fun g ↦ (criticalPair M hM g).2) (𝓝 0) (𝓝 1) := by
    simpa only [hs.2.1] using hs.1.continuousAt.snd.tendsto
  filter_upwards [criticalPair_star M hM,
    Metric.tendsto_nhds.mp hρ 1 zero_lt_one,
    Metric.tendsto_nhds.mp hτ 1 zero_lt_one] with g hg hr ht
  intro hreal
  rw [hreal] at hg
  refine ⟨Complex.conj_eq_iff_im.mp (congrArg Prod.fst hg.symm),
    re_pos_of_norm_sub_one_lt _ (by simpa only [dist_eq_norm] using hr), ?_⟩
  intro x
  refine ⟨Complex.conj_eq_iff_im.mp (congrArg (fun q : ℂ × C(S, ℂ) ↦ q.2 x) hg.symm), ?_⟩
  apply re_pos_of_norm_sub_one_lt
  have hnorm := ((criticalPair M hM g).2 - 1).norm_coe_le_norm x
  exact lt_of_le_of_lt hnorm (by simpa only [dist_eq_norm] using ht)

/-- An explicit common radius for the real positive critical pair. -/
theorem criticalPair_real_positive_radius (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : C(S, ℂ), ‖g‖ < ε → star g = g →
      (criticalPair M hM g).1.im = 0 ∧ 0 < (criticalPair M hM g).1.re ∧
      ∀ x, ((criticalPair M hM g).2 x).im = 0 ∧
        0 < ((criticalPair M hM g).2 x).re := by
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp (criticalPair_real_positive M hM)
  exact ⟨ε, hε, fun g hg ↦ h (by simpa only [dist_zero_right] using hg)⟩

end PerronWright.CriticalPair
