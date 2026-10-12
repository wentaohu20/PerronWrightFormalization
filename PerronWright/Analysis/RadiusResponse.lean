import PerronWright.Analysis.CriticalPair

/-!
# First field response of the analytic critical radius

The radius and profile are the two components of the actual analytic critical pair.
Differentiating its tree equation and applying the normalized left Perron functional
gives the exact first derivative of the radius.  Identification with the convergence
radius of the least-tree branch is a separate, subsequent result.
-/

open MeasureTheory
open scoped Topology

noncomputable section

namespace PerronWright.RadiusResponse

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The scalar component of the analytic critical pair. -/
def radius (M : CompactBJRModel S) (hM : M.IsRegularCritical) (g : C(S, ℂ)) : ℂ :=
  (CriticalPair.criticalPair M hM g).1

/-- The type profile of the analytic critical pair. -/
def profile (M : CompactBJRModel S) (hM : M.IsRegularCritical) (g : C(S, ℂ)) : C(S, ℂ) :=
  (CriticalPair.criticalPair M hM g).2

theorem radius_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (radius M hM) 0 :=
  analyticAt_fst.comp (Classical.choose_spec (CriticalPair.criticalPair_germ M hM)).1

theorem profile_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (profile M hM) 0 :=
  analyticAt_snd.comp (Classical.choose_spec (CriticalPair.criticalPair_germ M hM)).1

theorem radius_base (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    radius M hM 0 = 1 :=
  congrArg Prod.fst (Classical.choose_spec (CriticalPair.criticalPair_germ M hM)).2.1

theorem profile_base (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    profile M hM 0 = 1 :=
  congrArg Prod.snd (Classical.choose_spec (CriticalPair.criticalPair_germ M hM)).2.1

/-- The first critical-radius response in normalized Perron-functional form. -/
theorem radius_fderiv (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (h : C(S, ℂ)) :
    (fderiv ℂ (radius M hM) 0) h =
      -(M.alpha hM : ℂ) * M.normalizedPerronFunctional hM h := by
  have hs := Classical.choose_spec (CriticalPair.criticalPair_germ M hM)
  rw [← CriticalPair.criticalPair] at hs
  have hρ := radius_analytic M hM
  have hτ := profile_analytic M hM
  have hρ0 := radius_base M hM
  have hτ0 := profile_base M hM
  let K := M.kernel.complexActionCLM M.mu
  let d := TreeCritical.degree M
  have hinner := ((hasFDerivAt_id (𝕜 := ℂ) (0 : C(S, ℂ))).sub_const d).add
    (K.hasFDerivAt.comp 0 hτ.hasStrictFDerivAt.hasFDerivAt)
  have hexp := (hasFDerivAt_exp (𝕂 := ℂ)
    (x := (0 : C(S, ℂ)) - d + K (profile M hM 0))).comp 0 hinner
  have hrhs := hρ.hasStrictFDerivAt.hasFDerivAt.smul hexp
  have heq : profile M hM =ᶠ[𝓝 0]
      (fun g ↦ radius M hM g • NormedSpace.exp (g - d + K (profile M hM g))) := by
    filter_upwards [hs.2.2.1] with g hg
    exact hg.1
  have hder := (heq.fderiv_eq (𝕜 := ℂ)).trans hrhs.fderiv
  have hv := congrArg (fun A : C(S, ℂ) →L[ℂ] C(S, ℂ) ↦ A h) hder
  simp only [Function.comp_apply, Pi.add_apply, id_eq, hρ0, hτ0, zero_sub, d,
    TreeCritical.degree, K, neg_add_cancel,
    NormedSpace.exp_zero, one_smul, add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, one_apply_eq_self] at hv
  have hp := congrArg (M.normalizedPerronFunctional hM) hv
  simp only [map_add, map_smul, ContinuousKernel.complexActionCLM_apply,
    M.normalizedPerronFunctional_action,
    FoldCoefficients.normalizedPerronFunctional_one, smul_eq_mul] at hp
  have ha : (M.alpha hM : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (M.alpha_pos hM).ne'
  field_simp at hp
  linear_combination -hp

/-- The first critical-radius response is the negative Perron-weighted integral. -/
theorem radius_fderiv_integral (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (h : C(S, ℂ)) :
    (fderiv ℂ (radius M hM) 0) h = -M.weightedIntegralComplex hM h := by
  rw [radius_fderiv]
  change -(M.alpha hM : ℂ) *
    ((M.alpha hM : ℂ)⁻¹ * M.weightedIntegralComplex hM h) = _
  have ha : (M.alpha hM : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (M.alpha_pos hM).ne'
  rw [← mul_assoc, neg_mul, mul_inv_cancel₀ ha, neg_one_mul]

end PerronWright.RadiusResponse
