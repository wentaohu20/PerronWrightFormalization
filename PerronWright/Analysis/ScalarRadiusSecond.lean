import PerronWright.Analysis.ScalarFieldSecond

open MeasureTheory PerronWright
open scoped Topology

noncomputable section

namespace PerronWright.ScalarRadiusSecond

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

def scalarRadius (M : CompactBJRModel S) (hM : M.IsRegularCritical) (t : ℂ) : ℂ :=
  RadiusResponse.radius M hM (ScalarFieldResponse.scalarFieldComplex M t)

def scalarProfile (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (t : ℂ) : C(S, ℂ) :=
  RadiusResponse.profile M hM (ScalarFieldResponse.scalarFieldComplex M t)

theorem scalarRadius_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (scalarRadius M hM) 1 := by
  exact (RadiusResponse.radius_analytic M hM).comp_of_eq
    (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M)
    (ScalarFieldResponse.scalarFieldComplex_one M)

theorem scalarProfile_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (scalarProfile M hM) 1 := by
  exact (RadiusResponse.profile_analytic M hM).comp_of_eq
    (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M)
    (ScalarFieldResponse.scalarFieldComplex_one M)

@[simp] theorem scalarRadius_one (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    scalarRadius M hM 1 = 1 := by
  simp [scalarRadius, RadiusResponse.radius_base]

@[simp] theorem scalarProfile_one (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    scalarProfile M hM 1 = 1 := by
  simp [scalarProfile, RadiusResponse.profile_base]

theorem scalarRadius_deriv_one (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    deriv (scalarRadius M hM) 1 = 0 :=
  ScalarFieldResponse.criticalRadius_scalar_deriv_zero M hM

theorem scalar_tree_equation (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ t in 𝓝 (1 : ℂ),
      scalarProfile M hM t = scalarRadius M hM t • NormedSpace.exp
        (ScalarFieldResponse.scalarFieldComplex M t - TreeCritical.degree M +
          M.kernel.complexActionCLM M.mu (scalarProfile M hM t)) := by
  have ht : Filter.Tendsto (ScalarFieldResponse.scalarFieldComplex M) (𝓝 1)
      (𝓝 (0 : C(S, ℂ))) := by
    simpa [ScalarFieldResponse.scalarFieldComplex_one] using
      (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M).continuousAt.tendsto
  have heq := ht.eventually (Classical.choose_spec
    (CriticalPair.criticalPair_germ M hM)).2.2.1
  filter_upwards [heq] with t h
  exact h.1

theorem scalar_critical_equation (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ t in 𝓝 (1 : ℂ),
      CriticalPair.eigenvalue M hM (scalarProfile M hM t) = 1 := by
  have ht : Filter.Tendsto (ScalarFieldResponse.scalarFieldComplex M) (𝓝 1)
      (𝓝 (0 : C(S, ℂ))) := by
    simpa [ScalarFieldResponse.scalarFieldComplex_one] using
      (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M).continuousAt.tendsto
  have heq := ht.eventually (Classical.choose_spec
    (CriticalPair.criticalPair_germ M hM)).2.2.1
  filter_upwards [heq] with t h
  exact h.2

def scalarExp (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (t : ℂ) : C(S, ℂ) :=
  NormedSpace.exp (ScalarFieldResponse.scalarFieldComplex M t - TreeCritical.degree M +
    M.kernel.complexActionCLM M.mu (scalarProfile M hM t))

theorem scalarExp_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (scalarExp M hM) 1 := by
  unfold scalarExp
  have hinner : AnalyticAt ℂ (fun t : ℂ =>
      ScalarFieldResponse.scalarFieldComplex M t - TreeCritical.degree M +
        M.kernel.complexActionCLM M.mu (scalarProfile M hM t)) 1 :=
    ((ScalarFieldResponse.scalarFieldComplex_analyticAt_one M).sub analyticAt_const).add
      ((M.kernel.complexActionCLM M.mu).analyticAt _ |>.comp
        (scalarProfile_analytic M hM))
  exact (NormedSpace.exp_analytic _).comp hinner

@[simp] theorem scalarExp_one (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    scalarExp M hM 1 = 1 := by
  simp [scalarExp, TreeCritical.degree, ScalarFieldResponse.scalarFieldComplex_one]

theorem scalarExp_hasDerivAt (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (t : ℂ) (hg : AnalyticAt ℂ (ScalarFieldResponse.scalarFieldComplex M) t)
    (hU : AnalyticAt ℂ (scalarProfile M hM) t) :
    HasDerivAt (scalarExp M hM)
      (scalarExp M hM t *
        (deriv (ScalarFieldResponse.scalarFieldComplex M) t +
          M.kernel.complexActionCLM M.mu (deriv (scalarProfile M hM) t))) t := by
  let K := M.kernel.complexActionCLM M.mu
  let d := TreeCritical.degree M
  let U := scalarProfile M hM
  let g := ScalarFieldResponse.scalarFieldComplex M
  have hinner : HasDerivAt (fun s : ℂ => g s - d + K (U s))
      (deriv g t + K (deriv U t)) t :=
    ((hg.hasStrictDerivAt.hasDerivAt.sub_const d).add
      (K.hasFDerivAt.comp_hasDerivAt t hU.hasStrictDerivAt.hasDerivAt))
  have hexp := (hasFDerivAt_exp (𝕂 := ℂ) (x := g t - d + K (U t))).comp_hasDerivAt t hinner
  change HasDerivAt (NormedSpace.exp ∘ fun s : ℂ => g s - d + K (U s))
    (NormedSpace.exp (g t - d + K (U t)) * (deriv g t + K (deriv U t))) t
  have hcoeff : ((NormedSpace.exp (g t - d + K (U t)) •
      (1 : C(S, ℂ) →L[ℂ] C(S, ℂ))) (deriv g t + K (deriv U t))) =
      NormedSpace.exp (g t - d + K (U t)) * (deriv g t + K (deriv U t)) := by
    ext x
    simp only [smul_apply, one_apply_eq_self, smul_eq_mul, ContinuousMap.mul_apply]
  exact hexp.congr_deriv hcoeff

theorem scalarExp_deriv_one (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    deriv (scalarExp M hM) 1 =
      (1 - TreeCritical.degree M) +
        M.kernel.complexActionCLM M.mu (deriv (scalarProfile M hM) 1) := by
  have h := (scalarExp_hasDerivAt M hM 1
    (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M)
    (scalarProfile_analytic M hM)).deriv
  rw [scalarExp_one, (ScalarFieldResponse.scalarFieldComplex_hasDerivAt_one M).deriv] at h
  simpa only [one_mul] using h

theorem scalarProfile_first_equation (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    deriv (scalarProfile M hM) 1 =
      (1 - TreeCritical.degree M) +
        M.kernel.complexActionCLM M.mu (deriv (scalarProfile M hM) 1) := by
  have heq : scalarProfile M hM =ᶠ[𝓝 (1 : ℂ)]
      (fun t => scalarRadius M hM t • scalarExp M hM t) := scalar_tree_equation M hM
  have hd := heq.deriv_eq (𝕜 := ℂ)
  have hp := (scalarRadius_analytic M hM).hasStrictDerivAt.hasDerivAt.smul
    (scalarExp_hasDerivAt M hM 1
      (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M)
      (scalarProfile_analytic M hM))
  change deriv (scalarProfile M hM) 1 =
    deriv (scalarRadius M hM • scalarExp M hM) 1 at hd
  rw [hp.deriv] at hd
  rw [scalarRadius_one, scalarExp_one, scalarRadius_deriv_one,
    (ScalarFieldResponse.scalarFieldComplex_hasDerivAt_one M).deriv] at hd
  simpa only [zero_smul, zero_add, add_zero, one_smul, one_mul] using hd

theorem scalarProfile_critical_deriv_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    (fderiv ℂ (CriticalPair.eigenvalue M hM) 1)
      (deriv (scalarProfile M hM) 1) = 0 := by
  have heq : (fun t => CriticalPair.eigenvalue M hM (scalarProfile M hM t))
      =ᶠ[𝓝 (1 : ℂ)] (fun _ => (1 : ℂ)) := scalar_critical_equation M hM
  have hd := heq.deriv_eq (𝕜 := ℂ)
  have houter : HasFDerivAt (CriticalPair.eigenvalue M hM)
      (fderiv ℂ (CriticalPair.eigenvalue M hM) 1) (scalarProfile M hM 1) := by
    simpa only [scalarProfile_one] using
      (CriticalPair.eigenvalue_analytic M hM).hasStrictFDerivAt.hasFDerivAt
  have hc := houter.comp_hasDerivAt 1
    (scalarProfile_analytic M hM).hasStrictDerivAt.hasDerivAt
  change deriv (CriticalPair.eigenvalue M hM ∘ scalarProfile M hM) 1 =
    deriv (fun _ : ℂ => (1 : ℂ)) 1 at hd
  rw [hc.deriv] at hd
  simpa only [scalarProfile_one, deriv_const] using hd

/-- The critical scalar perturbation selects this precise tangent in type space. -/
theorem scalarProfile_deriv_one (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    deriv (scalarProfile M hM) 1 =
      (1 : C(S, ℂ)) -
        ((M.alpha hM : ℂ) / (M.beta hM : ℂ)) • M.complexPerronFunction hM := by
  let K := M.kernel.complexActionCLM M.mu
  let U := deriv (scalarProfile M hM) 1
  let u := M.complexPerronFunction hM
  let ell := M.normalizedPerronFunctional hM
  let D := fderiv ℂ (CriticalPair.eigenvalue M hM) 1
  have hfirst := scalarProfile_first_equation M hM
  have hK1 : K (1 : C(S, ℂ)) = TreeCritical.degree M := rfl
  have hfix : K (U - 1) = U - 1 := by
    rw [map_sub, hK1]
    change K U - TreeCritical.degree M = U - 1
    change U = 1 - TreeCritical.degree M + K U at hfirst
    linear_combination -hfirst
  have hproj := M.complex_fixed_eq_perronFunctional_smul hM (U - 1) hfix
  let c := ell (U - 1)
  have hU : U = 1 + c • u := by
    change U - 1 = c • u at hproj
    apply sub_eq_iff_eq_add.mp at hproj
    rw [hproj]
    abel
  have hD1 : D (1 : C(S, ℂ)) = 1 := by
    change (fderiv ℂ (CriticalPair.eigenvalue M hM) 1) 1 = 1
    rw [CriticalPair.eigenvalue_fderiv, one_mul,
      M.normalizedPerronFunctional_perronFunction]
  have hDu : D u = (M.beta hM : ℂ) / (M.alpha hM : ℂ) :=
    CriticalPair.eigenvalue_fderiv_perron M hM
  have hc := scalarProfile_critical_deriv_zero M hM
  change D U = 0 at hc
  rw [hU, map_add, map_smul, smul_eq_mul, hD1, hDu] at hc
  have ha : (M.alpha hM : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (M.alpha_pos hM).ne'
  have hb : (M.beta hM : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (M.beta_pos hM).ne'
  have hmul : c * (M.beta hM : ℂ) = -(M.alpha hM : ℂ) := by
    field_simp [ha] at hc
    linear_combination hc
  have hcval : c = -((M.alpha hM : ℂ) / (M.beta hM : ℂ)) := by
    simpa only [neg_div] using (eq_div_iff hb).mpr hmul
  change U = 1 - ((M.alpha hM : ℂ) / (M.beta hM : ℂ)) • u
  rw [hU, hcval, neg_smul]
  rfl

theorem scalarExp_deriv_one_eq_profile_deriv (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    deriv (scalarExp M hM) 1 = deriv (scalarProfile M hM) 1 :=
  (scalarExp_deriv_one M hM).trans (scalarProfile_first_equation M hM).symm

theorem scalar_tree_first_derivative (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ t in 𝓝 (1 : ℂ),
      deriv (scalarProfile M hM) t =
        deriv (scalarRadius M hM) t • scalarExp M hM t +
          scalarRadius M hM t •
            (scalarExp M hM t *
              (deriv (ScalarFieldResponse.scalarFieldComplex M) t +
                M.kernel.complexActionCLM M.mu (deriv (scalarProfile M hM) t))) := by
  have heq : scalarProfile M hM =ᶠ[𝓝 (1 : ℂ)]
      (fun t => scalarRadius M hM t • scalarExp M hM t) := scalar_tree_equation M hM
  filter_upwards [heq.eventuallyEq_nhds,
    (scalarRadius_analytic M hM).eventually_analyticAt,
    (scalarProfile_analytic M hM).eventually_analyticAt,
    (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M).eventually_analyticAt]
    with t heq_t hR_t hU_t hg_t
  have hp := hR_t.hasStrictDerivAt.hasDerivAt.smul
    (scalarExp_hasDerivAt M hM t hg_t hU_t)
  have hd := heq_t.deriv_eq
  change deriv (scalarProfile M hM) t =
    deriv (scalarRadius M hM • scalarExp M hM) t at hd
  rw [hp.deriv] at hd
  simpa only [add_comm] using hd

/-- The exact second derivative of the actual tree equation along the scalar field. -/
theorem scalar_tree_second_equation (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    deriv (deriv (scalarProfile M hM)) 1 =
      deriv (deriv (scalarRadius M hM)) 1 • (1 : C(S, ℂ)) +
        deriv (scalarProfile M hM) 1 ^ 2 - 1 +
          M.kernel.complexActionCLM M.mu
            (deriv (deriv (scalarProfile M hM)) 1) := by
  let R := scalarRadius M hM
  let U := scalarProfile M hM
  let g := ScalarFieldResponse.scalarFieldComplex M
  let E := scalarExp M hM
  let K := M.kernel.complexActionCLM M.mu
  have hUa := (scalarProfile_analytic M hM).deriv
  have hRa := (scalarRadius_analytic M hM).deriv
  have hga := (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M).deriv
  have hR := (scalarRadius_analytic M hM).hasStrictDerivAt.hasDerivAt
  have hU' := hUa.hasStrictDerivAt.hasDerivAt
  have hR' := hRa.hasStrictDerivAt.hasDerivAt
  have hg' := hga.hasStrictDerivAt.hasDerivAt
  have hE := scalarExp_hasDerivAt M hM 1
    (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M)
    (scalarProfile_analytic M hM)
  have hKU' := K.hasFDerivAt.comp_hasDerivAt 1 hU'
  have hA := hg'.add hKU'
  have hprod := hE.mul hA
  have hfirst := hR'.smul hE
  have hsecond := hR.smul hprod
  have hrhs := hfirst.add hsecond
  have heq : (deriv U) =ᶠ[𝓝 (1 : ℂ)]
      (fun t => deriv R t • E t + R t •
        (E t * (deriv g t + K (deriv U t)))) :=
    scalar_tree_first_derivative M hM
  have hd := heq.deriv_eq (𝕜 := ℂ)
  change deriv (deriv U) 1 =
    deriv ((deriv R) • E + R • (E * (deriv g + K ∘ deriv U))) 1 at hd
  rw [hrhs.deriv] at hd
  have hg1 : deriv g 1 = (1 : C(S, ℂ)) - TreeCritical.degree M :=
    (ScalarFieldResponse.scalarFieldComplex_hasDerivAt_one M).deriv
  have hA1 : deriv g 1 + K (deriv U 1) = deriv U 1 := by
    rw [hg1]
    exact (scalarProfile_first_equation M hM).symm
  have hg2 : deriv (deriv g) 1 = -(1 : C(S, ℂ)) :=
    ScalarFieldResponse.scalarFieldComplex_second_deriv_one M
  rw [scalarRadius_one, scalarRadius_deriv_one, scalarExp_one,
    hA1, show (deriv g + K ∘ deriv U) 1 = deriv U 1 by exact hA1,
    hg2] at hd
  simp only [zero_smul, zero_add, one_smul, one_mul,
    neg_add_eq_sub] at hd
  convert hd using 1
  ring

theorem weighted_profile_deriv_sq (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    M.weightedIntegralComplex hM (deriv (scalarProfile M hM) 1 ^ 2) =
      1 - (M.alpha hM : ℂ) ^ 2 / (M.beta hM : ℂ) := by
  let u := M.complexPerronFunction hM
  let a : ℂ := (M.alpha hM : ℂ) / (M.beta hM : ℂ)
  have hv := scalarProfile_deriv_one M hM
  have hsquare : ((1 : C(S, ℂ)) - a • u) ^ 2 =
      1 - (2 * a) • u + a ^ 2 • u ^ 2 := by
    ext x
    simp only [ContinuousMap.pow_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
      ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    ring
  rw [hv, hsquare]
  change M.weightedIntegralComplexCLM hM
    (1 - (2 * a) • u + a ^ 2 • u ^ 2) = _
  rw [map_add, map_sub, map_smul, map_smul]
  change M.weightedIntegralComplex hM 1 -
    (2 * a) * M.weightedIntegralComplex hM u +
    a ^ 2 * M.weightedIntegralComplex hM (u ^ 2) = _
  rw [FoldCoefficients.weightedIntegralComplex_one,
    M.weightedIntegralComplex_perronFunction,
    FoldCoefficients.weightedIntegralComplex_perron_sq]
  have hb : (M.beta hM : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (M.beta_pos hM).ne'
  dsimp [a]
  field_simp
  ring

/-- Exact second response of the actual analytic critical radius along the paper's
scalar field (g_t=(\log t)\mathbf 1-(t-1)d). -/
theorem scalarRadius_second_deriv_one (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    deriv (deriv (scalarRadius M hM)) 1 =
      (M.alpha hM : ℂ) ^ 2 / (M.beta hM : ℂ) := by
  have h := congrArg (M.weightedIntegralComplexCLM hM)
    (scalar_tree_second_equation M hM)
  simp only [map_add, map_sub, map_smul, smul_eq_mul,
    ContinuousKernel.complexActionCLM_apply] at h
  change M.weightedIntegralComplex hM (deriv (deriv (scalarProfile M hM)) 1) =
    deriv (deriv (scalarRadius M hM)) 1 * M.weightedIntegralComplex hM 1 +
      M.weightedIntegralComplex hM (deriv (scalarProfile M hM) 1 ^ 2) -
      M.weightedIntegralComplex hM 1 +
      M.weightedIntegralComplex hM
        (M.kernel.complexAction M.mu (deriv (deriv (scalarProfile M hM)) 1)) at h
  rw [FoldCoefficients.weightedIntegralComplex_one,
    weighted_profile_deriv_sq, M.weightedIntegralComplex_action] at h
  linear_combination -h


end PerronWright.ScalarRadiusSecond
