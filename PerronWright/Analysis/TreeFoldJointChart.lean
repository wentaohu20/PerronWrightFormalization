import PerronWright.Analysis.TreeFoldJointDivision

open scoped NNReal ENNReal
open Topology

noncomputable section

namespace PerronWright.TreeFoldJointChart

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

omit [MeasurableSpace S] [BorelSpace S] in
theorem joint_fold_coordinate_inverse (B : C(S, ℂ) × ℂ → ℂ)
    (hBa : AnalyticAt ℂ B (0, 0)) (hB0 : B (0, 0) ≠ 0) :
    ∃ V : C(S, ℂ) × ℂ → C(S, ℂ) × ℂ,
      AnalyticAt ℂ V (0, 0) ∧ V (0, 0) = (0, 0) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        (V q).1 = q.1 ∧ (V q).2 * B (V q) = q.2 := by
  let F : C(S, ℂ) × ℂ → C(S, ℂ) × ℂ := fun q => (q.1, q.2 * B q)
  let u : ℂˣ := Units.mk0 (B (0, 0)) hB0
  let i : (C(S, ℂ) × ℂ) ≃L[ℂ] (C(S, ℂ) × ℂ) :=
    (ContinuousLinearEquiv.refl ℂ C(S, ℂ)).prodCongr
      (ContinuousLinearEquiv.unitsEquivAut ℂ u)
  have hFa : AnalyticAt ℂ F (0, 0) :=
    analyticAt_fst.prod (analyticAt_snd.mul hBa)
  have hFd : HasFDerivAt F i.toContinuousLinearMap (0, 0) := by
    have hfirst : HasFDerivAt (fun q : C(S, ℂ) × ℂ => q.1)
        (ContinuousLinearMap.fst ℂ C(S, ℂ) ℂ) (0, 0) := hasFDerivAt_fst
    have hsecond : HasFDerivAt (fun q : C(S, ℂ) × ℂ => q.2 * B q)
        _ (0, 0) := (hasFDerivAt_snd).mul hBa.differentiableAt.hasFDerivAt
    have hsecond' : HasFDerivAt (fun q : C(S, ℂ) × ℂ => q.2 * B q)
        (B (0, 0) • ContinuousLinearMap.snd ℂ C(S, ℂ) ℂ) (0, 0) :=
      hsecond.congr_fderiv (by
        apply ContinuousLinearMap.ext
        intro q
        simp)
    have heq : i.toContinuousLinearMap =
        (ContinuousLinearMap.fst ℂ C(S, ℂ) ℂ).prod
          (B (0, 0) • ContinuousLinearMap.snd ℂ C(S, ℂ) ℂ) := by
      apply ContinuousLinearMap.ext
      intro q
      apply Prod.ext <;> simp [i, u,
        ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]
    exact (hfirst.prodMk hsecond').congr_fderiv heq.symm
  have hFstrict : HasStrictFDerivAt F i.toContinuousLinearMap (0, 0) := by
    simpa only [hFd.fderiv] using hFa.hasStrictFDerivAt
  let R := hFstrict.toOpenPartialHomeomorph F
  have hsource : (0, 0) ∈ R.source :=
    hFstrict.mem_toOpenPartialHomeomorph_source
  have hRa : AnalyticAt ℂ R.symm (0, 0) := by
    have h := R.analyticAt_symm' (i := i) hsource hFa ?_
    · simpa [F, R] using h
    · exact hFd.fderiv
  let V : C(S, ℂ) × ℂ → C(S, ℂ) × ℂ := R.symm
  have hV0 : V (0, 0) = (0, 0) := by
    simpa only [show R (0, 0) = (0, 0) by simp [R, F]] using
      R.left_inv hsource
  refine ⟨V, hRa, hV0, ?_⟩
  have hright : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), R (R.symm q) = q := by
    simpa only [show R (0, 0) = (0, 0) by simp [R, F]] using
      R.eventually_right_inverse' hsource
  filter_upwards [hright] with q hq
  have hq' : F (V q) = q := hq
  exact Prod.mk.inj hq'

omit [MeasurableSpace S] [BorelSpace S] in
theorem joint_fold_coordinate_inverse_vertical_derivative
    (B : C(S, ℂ) × ℂ → ℂ) (V : C(S, ℂ) × ℂ → C(S, ℂ) × ℂ)
    (hBa : AnalyticAt ℂ B (0, 0)) (hB0 : B (0, 0) ≠ 0)
    (hVa : AnalyticAt ℂ V (0, 0)) (hV0 : V (0, 0) = (0, 0))
    (hVinv : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      (V q).1 = q.1 ∧ (V q).2 * B (V q) = q.2) :
    deriv (fun X : ℂ => (V (0, X)).2) 0 = (B (0, 0))⁻¹ := by
  have hsection : AnalyticAt ℂ (fun X : ℂ => ((0 : C(S, ℂ)), X)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hVs : AnalyticAt ℂ (fun X : ℂ => V (0, X)) 0 :=
    hVa.comp_of_eq hsection rfl
  have hvs : AnalyticAt ℂ (fun X : ℂ => (V (0, X)).2) 0 :=
    analyticAt_snd.comp hVs
  have hbs : AnalyticAt ℂ (fun X : ℂ => B (V (0, X))) 0 :=
    hBa.comp_of_eq hVs hV0
  have hinv : (fun X : ℂ => (V (0, X)).2 * B (V (0, X))) =ᶠ[𝓝 0] id := by
    filter_upwards [hsection.continuousAt.tendsto.eventually hVinv] with X hX
    exact hX.2
  have hp := hvs.differentiableAt.hasDerivAt.mul hbs.differentiableAt.hasDerivAt
  have hp' : deriv (fun X : ℂ => (V (0, X)).2 * B (V (0, X))) 0 =
      deriv (fun X : ℂ => (V (0, X)).2) 0 * B (0, 0) := by
    have heq : ((fun X : ℂ => (V (0, X)).2) *
        (fun X : ℂ => B (V (0, X)))) =
        (fun X : ℂ => (V (0, X)).2 * B (V (0, X))) := rfl
    simpa only [heq, hV0, Prod.snd_zero, zero_mul, add_zero] using hp.deriv
  have hderiv := hinv.deriv_eq
  rw [hp', deriv_id] at hderiv
  exact (mul_eq_one_iff_eq_inv₀ hB0).mp hderiv

theorem joint_normalized_square_root (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (H : C(S, ℂ) × ℂ → ℂ)
    (hHa : AnalyticAt ℂ H (0, 0))
    (hH0 : H (0, 0) = (M.beta hM : ℂ) / 2) :
    ∃ B : C(S, ℂ) × ℂ → ℂ,
      AnalyticAt ℂ B (0, 0) ∧
      B (0, 0) = (FoldCoefficients.gamma M hM : ℂ)⁻¹ ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        RadiusResponse.radius M hM q.1 * B q ^ 2 = H q := by
  let β : ℂ := M.beta hM
  let γ : ℂ := FoldCoefficients.gamma M hM
  let ρ : C(S, ℂ) × ℂ → ℂ := fun q => RadiusResponse.radius M hM q.1
  have hρa : AnalyticAt ℂ ρ (0, 0) := by
    have hfst : AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ => q.1) (0, 0) := analyticAt_fst
    exact (RadiusResponse.radius_analytic M hM).comp_of_eq hfst rfl
  have hρ0 : ρ (0, 0) = 1 := RadiusResponse.radius_base M hM
  have hβ : β ≠ 0 := Complex.ofReal_ne_zero.mpr (M.beta_pos hM).ne'
  have hγ : γ ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (FoldCoefficients.gamma_pos M hM).ne'
  have hγβ : γ ^ 2 * β = 2 := by
    change (FoldCoefficients.gamma M hM : ℂ) ^ 2 * (M.beta hM : ℂ) = 2
    exact_mod_cast FoldCoefficients.gamma_sq_mul_beta M hM
  have hscale : γ⁻¹ ^ 2 * (2 / β) = 1 := by
    field_simp [hγ, hβ]
    exact hγβ.symm
  let Q : C(S, ℂ) × ℂ → ℂ := fun q => H q * (2 / β) / ρ q
  have hQa : AnalyticAt ℂ Q (0, 0) :=
    (hHa.mul analyticAt_const).div hρa (by rw [hρ0]; exact one_ne_zero)
  have hQ0 : Q (0, 0) = 1 := by
    change H (0, 0) * (2 / β) / ρ (0, 0) = 1
    rw [hH0, hρ0]
    change (β / 2) * (2 / β) / 1 = 1
    field_simp [hβ]
  have hQslit : Q (0, 0) ∈ Complex.slitPlane := by
    rw [hQ0]
    exact Complex.one_mem_slitPlane
  let B : C(S, ℂ) × ℂ → ℂ := fun q =>
    γ⁻¹ * Complex.exp (Complex.log (Q q) / 2)
  have hBa : AnalyticAt ℂ B (0, 0) := by
    apply analyticAt_const.mul
    exact ((hQa.clog hQslit).div_const).cexp'
  have hB0 : B (0, 0) = γ⁻¹ := by simp [B, hQ0]
  refine ⟨B, hBa, hB0, ?_⟩
  have hQnz : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), Q q ≠ 0 := by
    have := hQa.continuousAt.eventually_ne (by rw [hQ0]; exact one_ne_zero)
    simpa using this
  have hρnz : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), ρ q ≠ 0 := by
    have := hρa.continuousAt.eventually_ne (by rw [hρ0]; exact one_ne_zero)
    simpa using this
  filter_upwards [hQnz, hρnz] with q hq hρq
  have hsqexp : (Complex.exp (Complex.log (Q q) / 2)) ^ 2 =
      Complex.exp (Complex.log (Q q)) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have hBsq : B q ^ 2 = γ⁻¹ ^ 2 * Q q := by
    calc
      B q ^ 2 = γ⁻¹ ^ 2 * (Complex.exp (Complex.log (Q q) / 2)) ^ 2 := by
        simp only [B, mul_pow]
      _ = γ⁻¹ ^ 2 * Q q := by rw [hsqexp, Complex.exp_log hq]
  rw [hBsq]
  change ρ q * (γ⁻¹ ^ 2 * (H q * (2 / β) / ρ q)) = H q
  calc
    ρ q * (γ⁻¹ ^ 2 * (H q * (2 / β) / ρ q)) =
        (γ⁻¹ ^ 2 * (2 / β)) * H q := by
          field_simp [hρq]
    _ = H q := by rw [hscale, one_mul]

theorem actual_joint_field_fold_chart (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃ T : C(S, ℂ) × ℂ → C(S, ℂ),
      AnalyticAt ℂ T (0, 0) ∧ T (0, 0) = 1 ∧
      deriv (fun X : ℂ => T (0, X)) 0 =
        (-(FoldCoefficients.gamma M hM : ℂ)) • M.complexPerronFunction hM ∧
      (∀ᶠ g : C(S, ℂ) in 𝓝 0,
        T (g, 0) = RadiusResponse.profile M hM g) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        TreeCritical.residual M
          ((RadiusResponse.radius M hM q.1 * (1 - q.2 ^ 2), q.1), T q) = 0 := by
  obtain ⟨H, hHa, hH0, hFactor⟩ :=
    TreeFoldJointDivision.centered_radius_joint_quadratic_factor_base M hM
  obtain ⟨B, hBa, hB0, hBsq⟩ :=
    joint_normalized_square_root M hM H hHa hH0
  have hBn : B (0, 0) ≠ 0 := by
    rw [hB0]
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (FoldCoefficients.gamma_pos M hM).ne')
  obtain ⟨V, hVa, hV0, hVinv⟩ := joint_fold_coordinate_inverse B hBa hBn
  let N : C(S, ℂ) × ℂ → C(S, ℂ) × ℂ := fun q => (q.1, -q.2)
  have hNa : AnalyticAt ℂ N (0, 0) := analyticAt_fst.prod analyticAt_snd.neg
  have hN0 : N (0, 0) = (0, 0) := by simp [N]
  have hNV : AnalyticAt ℂ (fun q => V (N q)) (0, 0) :=
    hVa.comp_of_eq hNa hN0
  have hNV0 : V (N (0, 0)) = (0, 0) := by rw [hN0, hV0]
  let T : C(S, ℂ) × ℂ → C(S, ℂ) := fun q =>
    (TreeFold.centeredFoldCurve M hM (V (N q))).2
  have hTa : AnalyticAt ℂ T (0, 0) :=
    analyticAt_snd.comp ((TreeFold.centeredFoldCurve_analytic M hM).comp_of_eq
      hNV hNV0)
  have hT0 : T (0, 0) = 1 := by
    have hc := (TreeFold.centeredFoldCurve_critical M hM).self_of_nhds
    simp only [T, hN0, hV0, hc]
    exact RadiusResponse.profile_base M hM
  have hTd : deriv (fun X : ℂ => T (0, X)) 0 =
      (-(FoldCoefficients.gamma M hM : ℂ)) • M.complexPerronFunction hM := by
    let γ : ℂ := FoldCoefficients.gamma M hM
    let v : ℂ → ℂ := fun X => (V (0, X)).2
    have hva : AnalyticAt ℂ v 0 := by
      have hs : AnalyticAt ℂ (fun X : ℂ => ((0 : C(S, ℂ)), X)) 0 :=
        analyticAt_const.prod analyticAt_id
      exact analyticAt_snd.comp (hVa.comp_of_eq hs rfl)
    have hvd : deriv v 0 = γ := by
      rw [joint_fold_coordinate_inverse_vertical_derivative B V hBa hBn hVa hV0 hVinv,
        hB0, inv_inv]
    let s : ℂ → ℂ := fun X => v (-X)
    have hs0 : s 0 = 0 := by simp [s, v, hV0]
    have hsd : HasDerivAt s (-γ) 0 := by
      have hv : HasDerivAt v γ 0 := by
        have h := hva.hasStrictDerivAt.hasDerivAt
        rwa [hvd] at h
      have hneg : HasDerivAt (fun X : ℂ => -X) (-1) 0 :=
        (hasDerivAt_id (0 : ℂ)).neg
      have hv' : HasDerivAt v γ (-(0 : ℂ)) := by simpa only [neg_zero] using hv
      have hc := hv'.comp 0 hneg
      simpa only [s, Function.comp_def, mul_neg, mul_one] using hc
    have hp : HasDerivAt (TreeFoldCurvature.profileSlice M hM)
        (M.complexPerronFunction hM) 0 := by
      have h := (TreeFoldCurvature.profileSlice_analytic M hM).hasStrictDerivAt.hasDerivAt
      rw [TreeFoldCurvature.profileSlice_deriv M hM] at h
      exact h
    have hp' : HasDerivAt (fun X : ℂ =>
        TreeFoldCurvature.profileSlice M hM (s X))
        ((-γ) • M.complexPerronFunction hM) 0 := by
      have hp0 : HasDerivAt (TreeFoldCurvature.profileSlice M hM)
          (M.complexPerronFunction hM) (s 0) := by simpa only [hs0] using hp
      have h := hp0.scomp 0 hsd
      simpa only [hs0, Function.comp_def] using h
    have hnegsec : AnalyticAt ℂ (fun X : ℂ => ((0 : C(S, ℂ)), -X)) 0 :=
      analyticAt_const.prod analyticAt_id.neg
    have hnegsect : Filter.Tendsto (fun X : ℂ => ((0 : C(S, ℂ)), -X))
        (𝓝 0) (𝓝 (0, 0)) := by
      simpa only [neg_zero] using hnegsec.continuousAt.tendsto
    have hVsec : ∀ᶠ X : ℂ in 𝓝 0, (V (0, -X)).1 = 0 := by
      filter_upwards [hnegsect.eventually hVinv] with X hX
      exact hX.1
    have heq : (fun X : ℂ => T (0, X)) =ᶠ[𝓝 0]
        (fun X => TreeFoldCurvature.profileSlice M hM (s X)) := by
      filter_upwards [hVsec] with X hX
      simp only [T, N, s, v, TreeFold.centeredFoldCurve,
        TreeFoldCurvature.profileSlice, hX, TreeFold.criticalCoordinate_base,
        zero_add]
    rw [heq.deriv_eq]
    exact hp'.deriv
  have hNt : Filter.Tendsto N (𝓝 (0, 0)) (𝓝 (0, 0)) := by
    simpa only [hN0] using hNa.continuousAt.tendsto
  have hNVt : Filter.Tendsto (fun q => V (N q)) (𝓝 (0, 0)) (𝓝 (0, 0)) := by
    simpa only [hNV0] using hNV.continuousAt.tendsto
  have hBne : ∀ᶠ p : C(S, ℂ) × ℂ in 𝓝 (0, 0), B p ≠ 0 :=
    hBa.continuousAt.eventually_ne hBn
  have haxisInput : Filter.Tendsto
      (fun g : C(S, ℂ) => N (g, 0)) (𝓝 0) (𝓝 (0, 0)) := by
    have hemb : Filter.Tendsto (fun g : C(S, ℂ) => (g, (0 : ℂ)))
        (𝓝 0) (𝓝 (0, 0)) :=
      (analyticAt_id.prod analyticAt_const : AnalyticAt ℂ
        (fun g : C(S, ℂ) => (g, (0 : ℂ))) 0).continuousAt.tendsto
    exact hNt.comp hemb
  have haxisMap : Filter.Tendsto
      (fun g : C(S, ℂ) => V (N (g, 0))) (𝓝 0) (𝓝 (0, 0)) := by
    have hemb : Filter.Tendsto (fun g : C(S, ℂ) => (g, (0 : ℂ)))
        (𝓝 0) (𝓝 (0, 0)) :=
      (analyticAt_id.prod analyticAt_const : AnalyticAt ℂ
        (fun g : C(S, ℂ) => (g, (0 : ℂ))) 0).continuousAt.tendsto
    exact hNVt.comp hemb
  have hTaxis : ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      T (g, 0) = RadiusResponse.profile M hM g := by
    filter_upwards [haxisInput.eventually hVinv, haxisMap.eventually hBne,
      TreeFold.centeredFoldCurve_critical M hM] with g hVi hBvg hcrit
    have hp2 : (V (N (g, 0))).2 = 0 := by
      have hm : (V (N (g, 0))).2 * B (V (N (g, 0))) = 0 := by
        simpa only [N, neg_zero] using hVi.2
      exact (mul_eq_zero.mp hm).resolve_right hBvg
    have hp : V (N (g, 0)) = (g, 0) := by
      apply Prod.ext
      · simpa only [N, neg_zero] using hVi.1
      · exact hp2
    change (TreeFold.centeredFoldCurve M hM (V (N (g, 0)))).2 = _
    rw [hp, hcrit]
    rfl
  refine ⟨T, hTa, hT0, hTd, hTaxis, ?_⟩
  have hVinv' := hNt.eventually hVinv
  have hFactor' := hNVt.eventually hFactor
  have hBsq' := hNVt.eventually hBsq
  have hEq' := hNVt.eventually
    (TreeFoldUniformField.centeredFoldCurve_equations M hM)
  filter_upwards [hVinv', hFactor', hBsq', hEq'] with q hVi hFa hBs hEq
  let p := V (N q)
  have hp1 : p.1 = q.1 := by simpa only [N] using hVi.1
  have hp2 : p.2 * B p = -q.2 := by simpa only [N] using hVi.2
  have hz : (TreeFold.centeredFoldCurve M hM p).1 =
      RadiusResponse.radius M hM q.1 * (1 - q.2 ^ 2) := by
    change RadiusResponse.radius M hM p.1 -
      (TreeFold.centeredFoldCurve M hM p).1 = p.2 ^ 2 * H p at hFa
    change RadiusResponse.radius M hM p.1 * B p ^ 2 = H p at hBs
    rw [hp1] at hFa hBs
    have hdef : RadiusResponse.radius M hM q.1 -
        (TreeFold.centeredFoldCurve M hM p).1 =
        RadiusResponse.radius M hM q.1 * q.2 ^ 2 := by
      calc
        _ = p.2 ^ 2 * H p := hFa
        _ = RadiusResponse.radius M hM q.1 * (p.2 * B p) ^ 2 := by
          rw [← hBs]
          ring
        _ = RadiusResponse.radius M hM q.1 * q.2 ^ 2 := by rw [hp2]; ring
    linear_combination -hdef
  have hres := hEq.1
  change TreeCritical.residual M (((TreeFold.centeredFoldCurve M hM p).1, p.1), T q) = 0 at hres
  rw [hz, hp1] at hres
  exact hres


end PerronWright.TreeFoldJointChart
