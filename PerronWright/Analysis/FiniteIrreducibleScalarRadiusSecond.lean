import PerronWright.Analysis.FiniteIrreducibleScalarFieldResponse

/-!
# Second scalar response for the literal finite irreducible model

Twice differentiating the actual critical tree equation and applying the
proved finite Perron functional gives rho''(1) = alpha^2 / beta. Neither
spectral primitivity nor a second-response interface is assumed.
-/

open MeasureTheory PerronWright
open scoped Topology

noncomputable section

namespace PerronWright.FiniteIrreducibleScalarRadiusSecond

open FiniteIrreducibleScalarFieldResponse

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

theorem scalar_tree_equation (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∀ᶠ t in 𝓝 (1 : ℂ),
      scalarProfile M hM t = scalarRadius M hM t • NormedSpace.exp
        (scalarField M t - TreeCritical.degree M.bjrModel +
          M.complexOperator (scalarProfile M hM t)) := by
  have ht : Filter.Tendsto (scalarField M) (𝓝 1)
      (𝓝 (0 : C(S, ℂ))) := by
    simpa [scalarField_one] using
      (scalarField_analytic M).continuousAt.tendsto
  have heq := ht.eventually (Classical.choose_spec
    (FiniteIrreducibleCriticalPair.criticalPair_germ M hM)).2.2.1
  filter_upwards [heq] with t h
  exact h.1

def scalarExp (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (t : ℂ) : C(S, ℂ) :=
  NormedSpace.exp (scalarField M t - TreeCritical.degree M.bjrModel +
    M.complexOperator (scalarProfile M hM t))

theorem scalarExp_analytic (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    AnalyticAt ℂ (scalarExp M hM) 1 := by
  unfold scalarExp
  have hinner : AnalyticAt ℂ (fun t : ℂ =>
      scalarField M t - TreeCritical.degree M.bjrModel +
        M.complexOperator (scalarProfile M hM t)) 1 :=
    ((scalarField_analytic M).sub analyticAt_const).add
      ((M.complexOperator).analyticAt _ |>.comp
        (scalarProfile_analytic M hM))
  exact (NormedSpace.exp_analytic _).comp hinner

@[simp] theorem scalarExp_one (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    scalarExp M hM 1 = 1 := by
  simp [scalarExp, TreeCritical.degree, scalarField_one,
    FiniteIrreducibleModel.complexOperator, ContinuousKernel.complexActionCLM_apply]

theorem scalarExp_hasDerivAt (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (t : ℂ) (hg : AnalyticAt ℂ (scalarField M) t)
    (hU : AnalyticAt ℂ (scalarProfile M hM) t) :
    HasDerivAt (scalarExp M hM)
      (scalarExp M hM t *
        (deriv (scalarField M) t +
          M.complexOperator (deriv (scalarProfile M hM) t))) t := by
  let K := M.complexOperator
  let d := TreeCritical.degree M.bjrModel
  let U := scalarProfile M hM
  let g := scalarField M
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

theorem scalarExp_deriv_one (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    deriv (scalarExp M hM) 1 =
      (1 - TreeCritical.degree M.bjrModel) +
        M.complexOperator (deriv (scalarProfile M hM) 1) := by
  have h := (scalarExp_hasDerivAt M hM 1
    (scalarField_analytic M)
    (scalarProfile_analytic M hM)).deriv
  rw [scalarExp_one, (scalarField_hasDerivAt_one M).deriv] at h
  simpa only [one_mul] using h

theorem scalarExp_deriv_one_eq_profile_deriv (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    deriv (scalarExp M hM) 1 = deriv (scalarProfile M hM) 1 :=
  (scalarExp_deriv_one M hM).trans (scalarProfile_first_equation M hM).symm

theorem scalar_tree_first_derivative (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ t in 𝓝 (1 : ℂ),
      deriv (scalarProfile M hM) t =
        deriv (scalarRadius M hM) t • scalarExp M hM t +
          scalarRadius M hM t •
            (scalarExp M hM t *
              (deriv (scalarField M) t +
                M.complexOperator (deriv (scalarProfile M hM) t))) := by
  have heq : scalarProfile M hM =ᶠ[𝓝 (1 : ℂ)]
      (fun t => scalarRadius M hM t • scalarExp M hM t) := scalar_tree_equation M hM
  filter_upwards [heq.eventuallyEq_nhds,
    (scalarRadius_analytic M hM).eventually_analyticAt,
    (scalarProfile_analytic M hM).eventually_analyticAt,
    (scalarField_analytic M).eventually_analyticAt]
    with t heq_t hR_t hU_t hg_t
  have hp := hR_t.hasStrictDerivAt.hasDerivAt.smul
    (scalarExp_hasDerivAt M hM t hg_t hU_t)
  have hd := heq_t.deriv_eq
  change deriv (scalarProfile M hM) t =
    deriv (scalarRadius M hM • scalarExp M hM) t at hd
  rw [hp.deriv] at hd
  simpa only [add_comm] using hd

/-- The exact second derivative of the actual tree equation along the scalar field. -/
theorem scalar_tree_second_equation (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    deriv (deriv (scalarProfile M hM)) 1 =
      deriv (deriv (scalarRadius M hM)) 1 • (1 : C(S, ℂ)) +
        deriv (scalarProfile M hM) 1 ^ 2 - 1 +
          M.complexOperator
            (deriv (deriv (scalarProfile M hM)) 1) := by
  let R := scalarRadius M hM
  let U := scalarProfile M hM
  let g := scalarField M
  let E := scalarExp M hM
  let K := M.complexOperator
  have hUa := (scalarProfile_analytic M hM).deriv
  have hRa := (scalarRadius_analytic M hM).deriv
  have hga := (scalarField_analytic M).deriv
  have hR := (scalarRadius_analytic M hM).hasStrictDerivAt.hasDerivAt
  have hU' := hUa.hasStrictDerivAt.hasDerivAt
  have hR' := hRa.hasStrictDerivAt.hasDerivAt
  have hg' := hga.hasStrictDerivAt.hasDerivAt
  have hE := scalarExp_hasDerivAt M hM 1
    (scalarField_analytic M)
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
  have hg1 : deriv g 1 = (1 : C(S, ℂ)) - TreeCritical.degree M.bjrModel :=
    (scalarField_hasDerivAt_one M).deriv
  have hA1 : deriv g 1 + K (deriv U 1) = deriv U 1 := by
    rw [hg1]
    exact (scalarProfile_first_equation M hM).symm
  have hg2 : deriv (deriv g) 1 = -(1 : C(S, ℂ)) :=
    ScalarFieldResponse.scalarFieldComplex_second_deriv_one M.bjrModel
  rw [scalarRadius_one, scalarRadius_deriv_one, scalarExp_one,
    hA1, show (deriv g + K ∘ deriv U) 1 = deriv U 1 by exact hA1,
    hg2] at hd
  simp only [zero_smul, zero_add, one_smul, one_mul,
    neg_add_eq_sub] at hd
  convert hd using 1
  ring

theorem weighted_profile_deriv_sq (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    M.weightedFunctional hM (deriv (scalarProfile M hM) 1 ^ 2) =
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
  change M.weightedFunctional hM
    (1 - (2 * a) • u + a ^ 2 • u ^ 2) = _
  rw [map_add, map_sub, map_smul, map_smul]
  change M.weightedFunctional hM 1 -
    (2 * a) * M.weightedFunctional hM u +
    a ^ 2 * M.weightedFunctional hM (u ^ 2) = _
  rw [FiniteIrreducibleModel.weightedFunctional_one,
    M.weightedFunctional_perronFunction,
    FiniteIrreducibleModel.weightedFunctional_perron_sq]
  have hb : (M.beta hM : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (M.beta_pos hM).ne'
  dsimp [a]
  field_simp
  ring

/-- Exact second response of the actual analytic critical radius along the paper's
scalar field (g_t=(\log t)\mathbf 1-(t-1)d). -/
theorem scalarRadius_second_deriv_one (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    deriv (deriv (scalarRadius M hM)) 1 =
      (M.alpha hM : ℂ) ^ 2 / (M.beta hM : ℂ) := by
  have h := congrArg (M.weightedFunctional hM)
    (scalar_tree_second_equation M hM)
  simp only [map_add, map_sub, map_smul, smul_eq_mul] at h
  change M.weightedFunctional hM (deriv (deriv (scalarProfile M hM)) 1) =
    deriv (deriv (scalarRadius M hM)) 1 * M.weightedFunctional hM 1 +
      M.weightedFunctional hM (deriv (scalarProfile M hM) 1 ^ 2) -
      M.weightedFunctional hM 1 +
      M.weightedFunctional hM
        (M.complexOperator (deriv (deriv (scalarProfile M hM)) 1)) at h
  rw [FiniteIrreducibleModel.weightedFunctional_one,
    weighted_profile_deriv_sq, M.weightedFunctional_action] at h
  linear_combination -h



end PerronWright.FiniteIrreducibleScalarRadiusSecond
