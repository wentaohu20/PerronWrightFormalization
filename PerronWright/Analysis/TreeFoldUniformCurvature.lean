import PerronWright.Analysis.TreeFoldUniformField

open PerronWright
open Filter Topology

noncomputable section

namespace PerronWright.TreeFoldUniformCurvature


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def verticalSecond (f : E × ℂ → ℂ) (g : E) : ℂ :=
  (fderiv ℂ (fderiv ℂ f) (g, 0)) (0, 1) (0, 1)

omit [CompleteSpace E] in
theorem verticalSecond_analyticAt {f : E × ℂ → ℂ}
    (hf : AnalyticAt ℂ f (0, 0)) :
    AnalyticAt ℂ (verticalSecond f) 0 := by
  have h2 : AnalyticAt ℂ (fderiv ℂ (fderiv ℂ f)) (0, 0) := hf.fderiv.fderiv
  have hsec : AnalyticAt ℂ (fun g : E ↦ (g, (0 : ℂ))) 0 := by fun_prop
  have hev1 : AnalyticAt ℂ
      (fun q : E × ℂ ↦ (fderiv ℂ (fderiv ℂ f) q) (0, 1)) (0, 0) := by
    exact ((ContinuousLinearMap.apply ℂ _ ((0 : E), (1 : ℂ))).analyticAt
      (fderiv ℂ (fderiv ℂ f) (0, 0))).comp_of_eq h2 rfl
  have hev2 : AnalyticAt ℂ
      (fun q : E × ℂ ↦ ((fderiv ℂ (fderiv ℂ f) q) (0, 1)) (0, 1)) (0, 0) := by
    exact ((ContinuousLinearMap.apply ℂ _ ((0 : E), (1 : ℂ))).analyticAt
      ((fderiv ℂ (fderiv ℂ f) (0, 0)) (0, 1))).comp_of_eq hev1 rfl
  exact hev2.comp_of_eq hsec rfl

omit [CompleteSpace E] in
theorem verticalSecond_eq_slice_second_deriv {f : E × ℂ → ℂ} {g : E}
    (hf : AnalyticAt ℂ f (g, 0)) :
    verticalSecond f g = deriv (deriv (fun t : ℂ ↦ f (g, t))) 0 := by
  let line : ℂ → E × ℂ := fun t ↦ (g, t)
  have hline (t : ℂ) : HasDerivAt line (0, 1) t := by
    exact (hasDerivAt_const t g).prodMk (hasDerivAt_id t)
  have hline0 : line 0 = (g, 0) := rfl
  have hfa : ∀ᶠ q : E × ℂ in 𝓝 (g, 0), AnalyticAt ℂ f q := hf.eventually_analyticAt
  have hft : ∀ᶠ t : ℂ in 𝓝 0, AnalyticAt ℂ f (line t) :=
    (hline 0).continuousAt.eventually hfa
  have hslice : ∀ᶠ t : ℂ in 𝓝 0,
      deriv (fun s : ℂ ↦ f (g, s)) t = (fderiv ℂ f (g, t)) (0, 1) := by
    filter_upwards [hft] with t hft
    have hchain := fderiv_comp_deriv t hft.differentiableAt (hline t).differentiableAt
    simpa [line, Function.comp_def, (hline t).deriv] using hchain
  have hdf : AnalyticAt ℂ (fderiv ℂ f) (g, 0) := hf.fderiv
  have hdfderiv : deriv (fun t : ℂ ↦ (fderiv ℂ f (g, t)) (0, 1)) 0 =
      (fderiv ℂ (fderiv ℂ f) (g, 0)) (0, 1) (0, 1) := by
    let ev : ((E × ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ :=
      ContinuousLinearMap.apply ℂ ℂ (0, 1)
    have hdev : HasFDerivAt (fun q : E × ℂ ↦ ev (fderiv ℂ f q))
        (ev.comp (fderiv ℂ (fderiv ℂ f) (g, 0))) (g, 0) :=
      ev.hasFDerivAt.comp _ hdf.differentiableAt.hasFDerivAt
    have hchain := hdev.comp_hasDerivAt 0 (hline 0)
    simpa [line, ev, Function.comp_def] using hchain.deriv
  rw [Filter.EventuallyEq.deriv_eq hslice, hdfderiv]
  rfl

section CompactKernel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private def centeredRadius (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (q : C(S, ℂ) × ℂ) : ℂ :=
  (TreeFold.centeredFoldCurve M hM q).1

private theorem centeredRadius_analyticAt (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (centeredRadius M hM) (0, 0) :=
  analyticAt_fst.comp (TreeFold.centeredFoldCurve_analytic M hM)

theorem centeredRadius_verticalSecond_analyticAt (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (verticalSecond (centeredRadius M hM)) 0 :=
  verticalSecond_analyticAt (centeredRadius_analyticAt M hM)

theorem centeredRadius_verticalSecond_base (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    verticalSecond (centeredRadius M hM) 0 = -(M.beta hM : ℂ) := by
  rw [verticalSecond_eq_slice_second_deriv (centeredRadius_analyticAt M hM)]
  have hslice : (fun t : ℂ ↦ centeredRadius M hM (0, t)) =
      TreeFoldCurvature.radiusSlice M hM := by
    funext t
    simp [centeredRadius, TreeFold.centeredFoldCurve,
      TreeFold.criticalCoordinate_base, TreeFoldCurvature.radiusSlice]
  rw [hslice, TreeFoldCurvature.radiusSlice_second_deriv]

theorem centeredRadius_verticalSecond_ne_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      verticalSecond (centeredRadius M hM) g ≠ 0 := by
  have hβ : (M.beta hM : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (M.beta_pos hM).ne'
  apply (centeredRadius_verticalSecond_analyticAt M hM).continuousAt.eventually_ne
  rw [centeredRadius_verticalSecond_base]
  exact neg_ne_zero.mpr hβ

/-- Each sufficiently small complex field has a genuine nondegenerate
quadratic fold factor. The factor is analytic in the scalar coordinate at
each field; no joint analyticity in the field is asserted here. -/
theorem centered_radius_pointwise_nondegenerate_factor (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
        ∀ t : ℂ,
          RadiusResponse.radius M hM g -
            (TreeFold.centeredFoldCurve M hM (g, t)).1 = t ^ 2 * H t := by
  have hemb : Filter.Tendsto (fun g : C(S, ℂ) ↦ (g, (0 : ℂ)))
      (𝓝 0) (𝓝 (0, 0)) :=
    (analyticAt_id.prod analyticAt_const : AnalyticAt ℂ
      (fun g : C(S, ℂ) ↦ (g, (0 : ℂ))) 0).continuousAt.tendsto
  have hψa := hemb.eventually (TreeFold.centeredFoldCurve_analytic M hM).eventually_analyticAt
  filter_upwards [TreeFoldUniformField.centered_radius_pointwise_quadratic_factor M hM,
    centeredRadius_verticalSecond_ne_zero M hM, hψa] with g hfactor hcurv hψag
  obtain ⟨H, hHa, hH0, hEq⟩ := hfactor
  have hza : AnalyticAt ℂ (centeredRadius M hM) (g, 0) :=
    analyticAt_fst.comp hψag
  rw [verticalSecond_eq_slice_second_deriv hza] at hcurv
  refine ⟨H, hHa, ?_, hEq⟩
  rw [hH0]
  exact div_ne_zero (neg_ne_zero.mpr hcurv) (by norm_num)

end CompactKernel

end PerronWright.TreeFoldUniformCurvature
