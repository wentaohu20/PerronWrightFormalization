import PerronWright.Analysis.FiniteIrreducibleFieldFold

open MeasureTheory PerronWright
open scoped Topology ContDiff

noncomputable section

namespace PerronWright.FiniteIrreducibleFieldCurvature

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The centered curve has the exact Perron tangent in the local scalar coordinate. -/
theorem centeredFoldCurve_tangent (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    deriv (fun s : ℂ ↦ FiniteIrreducibleFieldFold.centeredFoldCurve M hM (0, s)) 0 =
      (0, M.complexPerronFunction hM) := by
  have hc : FiniteIrreducibleFieldFold.criticalCoordinate M hM 0 = 0 :=
    FiniteIrreducibleFieldFold.criticalCoordinate_base M hM
  have hinner : HasDerivAt
      (fun s : ℂ ↦ ((0 : C(S, ℂ)), FiniteIrreducibleFieldFold.criticalCoordinate M hM 0 + s))
      ((0 : C(S, ℂ)), 1) 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : C(S, ℂ))).prodMk
      ((hasDerivAt_id (0 : ℂ)).const_add _)
  have houter : HasFDerivAt (FiniteIrreducibleFieldFold.foldCurve M hM)
      (fderiv ℂ (FiniteIrreducibleFieldFold.foldCurve M hM) (0, 0))
      ((0 : C(S, ℂ)), FiniteIrreducibleFieldFold.criticalCoordinate M hM 0 + 0) := by
    simpa only [hc, zero_add] using
      (FiniteIrreducibleFieldFold.foldCurve_analytic M hM).hasStrictFDerivAt.hasFDerivAt
  have hcomp := houter.comp_hasDerivAt 0 hinner
  have hfun : (fun s : ℂ ↦ FiniteIrreducibleFieldFold.centeredFoldCurve M hM (0, s)) =
      (fun s : ℂ ↦ FiniteIrreducibleFieldFold.foldCurve M hM
        (0, FiniteIrreducibleFieldFold.criticalCoordinate M hM 0 + s)) := rfl
  rw [hfun]
  simpa only [Function.comp_def] using
    hcomp.deriv.trans (FiniteIrreducibleFieldFold.foldCurve_tangent M hM)

def radiusSlice (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (s : ℂ) : ℂ :=
  (FiniteIrreducibleFieldFold.foldCurve M hM (0, s)).1

def profileSlice (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (s : ℂ) : C(S, ℂ) :=
  (FiniteIrreducibleFieldFold.foldCurve M hM (0, s)).2

theorem foldSlice_analytic (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    AnalyticAt ℂ (fun s : ℂ ↦ FiniteIrreducibleFieldFold.foldCurve M hM (0, s)) 0 := by
  have hj : AnalyticAt ℂ (fun s : ℂ ↦ ((0 : C(S, ℂ)), s)) 0 :=
    analyticAt_const.prod analyticAt_id
  exact (FiniteIrreducibleFieldFold.foldCurve_analytic M hM).comp_of_eq hj rfl

theorem radiusSlice_analytic (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    AnalyticAt ℂ (radiusSlice M hM) 0 :=
  analyticAt_fst.comp (foldSlice_analytic M hM)

theorem profileSlice_analytic (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    AnalyticAt ℂ (profileSlice M hM) 0 :=
  analyticAt_snd.comp (foldSlice_analytic M hM)

theorem radiusSlice_base (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    radiusSlice M hM 0 = 1 :=
  congrArg Prod.fst (FiniteIrreducibleFieldFold.foldCurve_base M hM)

theorem profileSlice_base (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    profileSlice M hM 0 = 1 :=
  congrArg Prod.snd (FiniteIrreducibleFieldFold.foldCurve_base M hM)

theorem radiusSlice_deriv (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    deriv (radiusSlice M hM) 0 = 0 := by
  have h := FiniteIrreducibleFieldFold.foldCurve_tangent M hM
  have hj : HasDerivAt (fun s : ℂ ↦ ((0 : C(S, ℂ)), s))
      ((0 : C(S, ℂ)), 1) 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : C(S, ℂ))).prodMk (hasDerivAt_id (0 : ℂ))
  have houter := (FiniteIrreducibleFieldFold.foldCurve_analytic M hM).hasStrictFDerivAt.hasFDerivAt
  have hcomp := houter.comp_hasDerivAt 0 hj
  have hfder : deriv (fun s : ℂ ↦ FiniteIrreducibleFieldFold.foldCurve M hM (0, s)) 0 =
      (0, M.complexPerronFunction hM) := by
    simpa only [Function.comp_def] using hcomp.deriv.trans h
  have hfst := (hasFDerivAt_fst (𝕜 := ℂ) (p := FiniteIrreducibleFieldFold.foldCurve M hM (0, 0))).comp_hasDerivAt
    0 hcomp
  have hd := hfst.deriv
  change deriv (radiusSlice M hM) 0 =
    ((fderiv ℂ (FiniteIrreducibleFieldFold.foldCurve M hM) (0, 0)) (0, 1)).1 at hd
  rw [FiniteIrreducibleFieldFold.foldCurve_tangent] at hd
  exact hd

theorem profileSlice_deriv (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    deriv (profileSlice M hM) 0 = M.complexPerronFunction hM := by
  have h := FiniteIrreducibleFieldFold.foldCurve_tangent M hM
  have hj : HasDerivAt (fun s : ℂ ↦ ((0 : C(S, ℂ)), s))
      ((0 : C(S, ℂ)), 1) 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : C(S, ℂ))).prodMk (hasDerivAt_id (0 : ℂ))
  have houter := (FiniteIrreducibleFieldFold.foldCurve_analytic M hM).hasStrictFDerivAt.hasFDerivAt
  have hcomp := houter.comp_hasDerivAt 0 hj
  have hfder : deriv (fun s : ℂ ↦ FiniteIrreducibleFieldFold.foldCurve M hM (0, s)) 0 =
      (0, M.complexPerronFunction hM) := by
    simpa only [Function.comp_def] using hcomp.deriv.trans h
  have hsnd := (hasFDerivAt_snd (𝕜 := ℂ) (p := FiniteIrreducibleFieldFold.foldCurve M hM (0, 0))).comp_hasDerivAt
    0 hcomp
  have hd := hsnd.deriv
  change deriv (profileSlice M hM) 0 =
    ((fderiv ℂ (FiniteIrreducibleFieldFold.foldCurve M hM) (0, 0)) (0, 1)).2 at hd
  rw [FiniteIrreducibleFieldFold.foldCurve_tangent] at hd
  exact hd

/-- The actual tree equation along the local zero-field fold curve. -/
theorem foldSlice_equation (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∀ᶠ s in 𝓝 (0 : ℂ),
      profileSlice M hM s =
        radiusSlice M hM s • NormedSpace.exp
          (-TreeCritical.degree M.bjrModel + M.complexOperator (profileSlice M hM s)) := by
  have hj : Filter.Tendsto (fun s : ℂ ↦ ((0 : C(S, ℂ)), s))
      (𝓝 0) (𝓝 (0, 0)) :=
    ((analyticAt_const.prod analyticAt_id : AnalyticAt ℂ
      (fun s : ℂ ↦ ((0 : C(S, ℂ)), s)) 0).continuousAt.tendsto)
  filter_upwards [hj.eventually (FiniteIrreducibleFieldFold.foldCurve_equations M hM)] with s hs
  have h := hs.1
  change profileSlice M hM s - radiusSlice M hM s •
    NormedSpace.exp ((0 : C(S, ℂ)) - TreeCritical.degree M.bjrModel +
      M.complexOperator (profileSlice M hM s)) = 0 at h
  simpa only [zero_sub] using sub_eq_zero.mp h

def expSlice (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (s : ℂ) : C(S, ℂ) :=
  NormedSpace.exp (-TreeCritical.degree M.bjrModel +
    M.complexOperator (profileSlice M hM s))

theorem expSlice_analytic (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    AnalyticAt ℂ (expSlice M hM) 0 := by
  unfold expSlice
  have hinner : AnalyticAt ℂ (fun s : ℂ ↦ -TreeCritical.degree M.bjrModel +
      M.complexOperator (profileSlice M hM s)) 0 :=
    analyticAt_const.add
      ((M.complexOperator).analyticAt _ |>.comp
        (profileSlice_analytic M hM))
  exact (NormedSpace.exp_analytic _).comp hinner

theorem expSlice_base (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    expSlice M hM 0 = 1 := by
  simp only [expSlice, profileSlice_base, TreeCritical.degree, FiniteIrreducibleModel.bjrModel,
    FiniteIrreducibleModel.complexOperator, neg_add_cancel, NormedSpace.exp_zero]

theorem expSlice_hasDerivAt (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (s : ℂ) (hU : AnalyticAt ℂ (profileSlice M hM) s) :
    HasDerivAt (expSlice M hM)
      (expSlice M hM s * M.complexOperator
        (deriv (profileSlice M hM) s)) s := by
  let K := M.complexOperator
  let d := TreeCritical.degree M.bjrModel
  let U := profileSlice M hM
  have hinner : HasDerivAt (fun t : ℂ ↦ -d + K (U t))
      (K (deriv U s)) s :=
    ((K.hasFDerivAt.comp_hasDerivAt s hU.hasStrictDerivAt.hasDerivAt).const_add (-d))
  have hexp := (hasFDerivAt_exp (𝕂 := ℂ) (x := -d + K (U s))).comp_hasDerivAt s hinner
  change HasDerivAt (NormedSpace.exp ∘ fun t : ℂ ↦ -d + K (U t))
    (NormedSpace.exp (-d + K (U s)) * K (deriv U s)) s
  have hcoeff : ((NormedSpace.exp (-d + K (U s)) •
      (1 : C(S, ℂ) →L[ℂ] C(S, ℂ))) (K (deriv U s))) =
      NormedSpace.exp (-d + K (U s)) * K (deriv U s) := by
    ext x
    simp only [smul_apply, one_apply_eq_self, smul_eq_mul, ContinuousMap.mul_apply]
  exact hexp.congr_deriv hcoeff

theorem expSlice_deriv_base (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    deriv (expSlice M hM) 0 = M.complexPerronFunction hM := by
  have h := (expSlice_hasDerivAt M hM 0 (profileSlice_analytic M hM)).deriv
  rw [expSlice_base, profileSlice_deriv, M.complexPerronFunction_fixed] at h
  simpa only [one_mul] using h

theorem foldSlice_first_derivative (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∀ᶠ s in 𝓝 (0 : ℂ),
      deriv (profileSlice M hM) s =
        deriv (radiusSlice M hM) s • expSlice M hM s +
          radiusSlice M hM s •
            (expSlice M hM s * M.complexOperator
              (deriv (profileSlice M hM) s)) := by
  have heq : profileSlice M hM =ᶠ[𝓝 (0 : ℂ)]
      (fun s ↦ radiusSlice M hM s • expSlice M hM s) :=
    foldSlice_equation M hM
  filter_upwards [heq.eventuallyEq_nhds,
      (radiusSlice_analytic M hM).eventually_analyticAt,
      (profileSlice_analytic M hM).eventually_analyticAt] with s heq_s hz_s hU_s
  have hprod := hz_s.hasStrictDerivAt.hasDerivAt.smul
    (expSlice_hasDerivAt M hM s hU_s)
  have hd := heq_s.deriv_eq
  change deriv (profileSlice M hM) s =
    deriv (radiusSlice M hM • expSlice M hM) s at hd
  rw [hprod.deriv] at hd
  simpa only [add_comm] using hd

/-- Twice differentiating the actual fold curve equation at the base point. -/
theorem foldSlice_second_equation (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    deriv (deriv (profileSlice M hM)) 0 =
      deriv (deriv (radiusSlice M hM)) 0 • (1 : C(S, ℂ)) +
        M.complexPerronFunction hM ^ 2 +
        M.complexOperator (deriv (deriv (profileSlice M hM)) 0) := by
  let z := radiusSlice M hM
  let U := profileSlice M hM
  let E := expSlice M hM
  let K := M.complexOperator
  have hUa := (profileSlice_analytic M hM).deriv
  have hza := (radiusSlice_analytic M hM).deriv
  have hEa := expSlice_analytic M hM
  have hz0 := (radiusSlice_analytic M hM).hasStrictDerivAt.hasDerivAt
  have hU' := hUa.hasStrictDerivAt.hasDerivAt
  have hz' := hza.hasStrictDerivAt.hasDerivAt
  have hE := (expSlice_hasDerivAt M hM 0 (profileSlice_analytic M hM))
  have hKU' := K.hasFDerivAt.comp_hasDerivAt 0 hU'
  have hprod := hE.mul hKU'
  have hfirst := hz'.smul hE
  have hsecond := hz0.smul hprod
  have hrhs := hfirst.add hsecond
  have heq : (deriv U) =ᶠ[𝓝 (0 : ℂ)]
      (fun s ↦ deriv z s • E s + z s • (E s * K (deriv U s))) :=
    foldSlice_first_derivative M hM
  have hd := heq.deriv_eq (𝕜 := ℂ)
  have hfun : (fun s ↦ deriv z s • E s + z s • (E s * K (deriv U s))) =
      (deriv z • E + z • (E * K ∘ deriv U)) := by
    funext s
    rfl
  rw [hfun, hrhs.deriv] at hd
  rw [radiusSlice_base, radiusSlice_deriv, profileSlice_deriv,
    expSlice_base, M.complexPerronFunction_fixed] at hd
  simp only [Function.comp_apply] at hd
  rw [profileSlice_deriv, M.complexPerronFunction_fixed] at hd
  simpa only [zero_smul, one_smul, zero_add, add_zero, one_mul,
    ← pow_two, add_assoc, U, K] using hd

/-- The exact local fold curvature from the original compact kernel model. -/
theorem radiusSlice_second_deriv (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    deriv (deriv (radiusSlice M hM)) 0 = -(M.beta hM : ℂ) := by
  have h := congrArg (M.normalizedPerronFunctional hM)
    (foldSlice_second_equation M hM)
  simp only [map_add, map_smul, smul_eq_mul,
    M.normalizedPerronFunctional_action,
    FiniteIrreducibleModel.normalizedPerronFunctional_one,
    FiniteIrreducibleModel.normalizedPerronFunctional_perron_sq] at h
  have ha : (M.alpha hM : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (M.alpha_pos hM).ne'
  field_simp at h
  linear_combination -h

end PerronWright.FiniteIrreducibleFieldCurvature
