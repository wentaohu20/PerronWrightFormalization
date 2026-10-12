import PerronWright.Analysis.FiniteIrreducibleCriticalPair

/-!
# First field response of the analytic critical radius

The radius and profile are the two components of the actual analytic critical pair.
Differentiating its tree equation and applying the normalized left Perron functional
gives the exact first derivative of the radius.  Identification with the convergence
radius of the least-tree branch is a separate, subsequent result.
-/

open MeasureTheory
open scoped Topology BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleRadiusResponse

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The scalar component of the analytic critical pair. -/
def radius (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) (g : C(S, ℂ)) : ℂ :=
  (FiniteIrreducibleCriticalPair.criticalPair M hcrit g).1

/-- The type profile of the analytic critical pair. -/
def profile (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) (g : C(S, ℂ)) : C(S, ℂ) :=
  (FiniteIrreducibleCriticalPair.criticalPair M hcrit g).2

theorem radius_analytic (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    AnalyticAt ℂ (radius M hcrit) 0 :=
  analyticAt_fst.comp (Classical.choose_spec (FiniteIrreducibleCriticalPair.criticalPair_germ M hcrit)).1

theorem profile_analytic (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    AnalyticAt ℂ (profile M hcrit) 0 :=
  analyticAt_snd.comp (Classical.choose_spec (FiniteIrreducibleCriticalPair.criticalPair_germ M hcrit)).1

theorem radius_base (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    radius M hcrit 0 = 1 :=
  congrArg Prod.fst (Classical.choose_spec (FiniteIrreducibleCriticalPair.criticalPair_germ M hcrit)).2.1

theorem profile_base (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    profile M hcrit 0 = 1 :=
  congrArg Prod.snd (Classical.choose_spec (FiniteIrreducibleCriticalPair.criticalPair_germ M hcrit)).2.1

/-- The first critical-radius response in normalized Perron-functional form. -/
theorem radius_fderiv (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (h : C(S, ℂ)) :
    (fderiv ℂ (radius M hcrit) 0) h =
      -(M.alpha hcrit : ℂ) * M.normalizedPerronFunctional hcrit h := by
  have hs := Classical.choose_spec (FiniteIrreducibleCriticalPair.criticalPair_germ M hcrit)
  rw [← FiniteIrreducibleCriticalPair.criticalPair] at hs
  have hρ := radius_analytic M hcrit
  have hτ := profile_analytic M hcrit
  have hρ0 := radius_base M hcrit
  have hτ0 := profile_base M hcrit
  let K := M.complexOperator
  let d := TreeCritical.degree M.bjrModel
  have hinner := ((hasFDerivAt_id (𝕜 := ℂ) (0 : C(S, ℂ))).sub_const d).add
    (K.hasFDerivAt.comp 0 hτ.hasStrictFDerivAt.hasFDerivAt)
  have hexp := (hasFDerivAt_exp (𝕂 := ℂ)
    (x := (0 : C(S, ℂ)) - d + K (profile M hcrit 0))).comp 0 hinner
  have hrhs := hρ.hasStrictFDerivAt.hasFDerivAt.smul hexp
  have heq : profile M hcrit =ᶠ[𝓝 0]
      (fun g ↦ radius M hcrit g • NormedSpace.exp (g - d + K (profile M hcrit g))) := by
    filter_upwards [hs.2.2.1] with g hg
    exact hg.1
  have hder := (heq.fderiv_eq (𝕜 := ℂ)).trans hrhs.fderiv
  have hv := congrArg (fun A : C(S, ℂ) →L[ℂ] C(S, ℂ) ↦ A h) hder
  simp only [Function.comp_apply, Pi.add_apply, id_eq, hρ0, hτ0, zero_sub, d,
    TreeCritical.degree, K, FiniteIrreducibleModel.complexOperator,
    FiniteIrreducibleModel.bjrModel, neg_add_cancel,
    NormedSpace.exp_zero, one_smul, add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, one_apply_eq_self] at hv
  change (fderiv ℂ (profile M hcrit) 0) h =
    h + M.complexOperator ((fderiv ℂ (profile M hcrit) 0) h) +
      (fderiv ℂ (radius M hcrit) 0) h • 1 at hv
  have hp := congrArg (M.normalizedPerronFunctional hcrit) hv
  simp only [map_add, map_smul,
    M.normalizedPerronFunctional_action,
    FiniteIrreducibleModel.normalizedPerronFunctional_one, smul_eq_mul] at hp
  have ha : (M.alpha hcrit : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (M.alpha_pos hcrit).ne'
  field_simp at hp
  linear_combination -hp

/-- The first critical-radius response is the negative Perron-weighted integral. -/
theorem radius_fderiv_weighted (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (h : C(S, ℂ)) :
    (fderiv ℂ (radius M hcrit) 0) h = -M.weightedFunctional hcrit h := by
  rw [radius_fderiv]
  change -(M.alpha hcrit : ℂ) *
    ((M.alpha hcrit : ℂ)⁻¹ * M.weightedFunctional hcrit h) = _
  have ha : (M.alpha hcrit : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (M.alpha_pos hcrit).ne'
  rw [← mul_assoc, neg_mul, mul_inv_cancel₀ ha, neg_one_mul]

theorem radius_fderiv_sum (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (h : C(S, ℂ)) :
    (fderiv ℂ (radius M hcrit) 0) h =
      -(∑ a, (M.weight a * M.perronFunction hcrit a : ℝ) * h a) := by
  rw [radius_fderiv_weighted, M.weightedFunctional_apply]

/-- Linearization of the actual critical tree equation, in every field direction. -/
theorem profile_fderiv_tree (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (h : C(S, ℂ)) :
    (fderiv ℂ (profile M hcrit) 0) h =
      h + M.complexOperator ((fderiv ℂ (profile M hcrit) 0) h) +
        (fderiv ℂ (radius M hcrit) 0) h • 1 := by
  have hs := Classical.choose_spec (FiniteIrreducibleCriticalPair.criticalPair_germ M hcrit)
  rw [← FiniteIrreducibleCriticalPair.criticalPair] at hs
  have hρ := radius_analytic M hcrit
  have hτ := profile_analytic M hcrit
  have hρ0 := radius_base M hcrit
  have hτ0 := profile_base M hcrit
  let K := M.complexOperator
  let d := TreeCritical.degree M.bjrModel
  have hinner := ((hasFDerivAt_id (𝕜 := ℂ) (0 : C(S, ℂ))).sub_const d).add
    (K.hasFDerivAt.comp 0 hτ.hasStrictFDerivAt.hasFDerivAt)
  have hexp := (hasFDerivAt_exp (𝕂 := ℂ)
    (x := (0 : C(S, ℂ)) - d + K (profile M hcrit 0))).comp 0 hinner
  have hrhs := hρ.hasStrictFDerivAt.hasFDerivAt.smul hexp
  have heq : profile M hcrit =ᶠ[𝓝 0]
      (fun g ↦ radius M hcrit g • NormedSpace.exp (g - d + K (profile M hcrit g))) := by
    filter_upwards [hs.2.2.1] with g hg
    exact hg.1
  have hder := (heq.fderiv_eq (𝕜 := ℂ)).trans hrhs.fderiv
  have hv := congrArg (fun A : C(S, ℂ) →L[ℂ] C(S, ℂ) ↦ A h) hder
  simp only [Function.comp_apply, Pi.add_apply, id_eq, hρ0, hτ0, zero_sub, d,
    TreeCritical.degree, K, FiniteIrreducibleModel.complexOperator,
    FiniteIrreducibleModel.bjrModel, neg_add_cancel,
    NormedSpace.exp_zero, one_smul, add_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, one_apply_eq_self] at hv
  change (fderiv ℂ (profile M hcrit) 0) h =
    h + M.complexOperator ((fderiv ℂ (profile M hcrit) 0) h) +
      (fderiv ℂ (radius M hcrit) 0) h • 1 at hv
  exact hv

/-- The derivative of the profile has the Fredholm-compatible tree source. -/
theorem profile_fderiv_complement_equation (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (h : C(S, ℂ)) :
    (fderiv ℂ (profile M hcrit) 0) h -
      M.complexOperator ((fderiv ℂ (profile M hcrit) 0) h) =
        h - M.weightedFunctional hcrit h • 1 := by
  have hv := profile_fderiv_tree M hcrit h
  rw [radius_fderiv_weighted, neg_smul] at hv
  linear_combination hv

/-- Differentiation of the genuine eigenvalue-one constraint. -/
theorem profile_fderiv_eigenvalue_constraint (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (h : C(S, ℂ)) :
    (fderiv ℂ (FiniteIrreducibleCriticalPair.eigenvalue M hcrit) 1)
      ((fderiv ℂ (profile M hcrit) 0) h) = 0 := by
  have hs := Classical.choose_spec (FiniteIrreducibleCriticalPair.criticalPair_germ M hcrit)
  rw [← FiniteIrreducibleCriticalPair.criticalPair] at hs
  have heq : (fun g ↦ FiniteIrreducibleCriticalPair.eigenvalue M hcrit
      (profile M hcrit g)) =ᶠ[𝓝 0] (fun _ ↦ (1 : ℂ)) := by
    filter_upwards [hs.2.2.1] with g hg
    exact hg.2
  have heig := (FiniteIrreducibleCriticalPair.eigenvalue_analytic M hcrit).hasStrictFDerivAt.hasFDerivAt
  rw [← profile_base M hcrit] at heig
  have hd := heig.comp 0 (profile_analytic M hcrit).hasStrictFDerivAt.hasFDerivAt
  have hz := heq.fderiv_eq (𝕜 := ℂ)
  simp only [fderiv_fun_const] at hz
  have he := congrArg (fun A : C(S, ℂ) →L[ℂ] ℂ ↦ A h) (hd.fderiv.symm.trans hz)
  simpa only [profile_base, ContinuousLinearMap.comp_apply, Pi.zero_apply, zero_apply]
    using he


end PerronWright.FiniteIrreducibleRadiusResponse


