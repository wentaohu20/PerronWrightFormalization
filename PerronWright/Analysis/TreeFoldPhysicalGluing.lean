import PerronWright.Analysis.TreeFoldJointChart
import PerronWright.Analysis.TreePhysicalBranch

/-! Local bilateral gluing of the jointly analytic field fold chart with the
physical least tree branch on the positive real square-root slice. -/

open Topology Filter
noncomputable section

namespace PerronWright.TreeFoldPhysicalGluing

open PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

omit [MeasurableSpace S] [BorelSpace S] in
theorem joint_fold_coordinate_inverse_bilateral (B : C(S, ℂ) × ℂ → ℂ)
    (hBa : AnalyticAt ℂ B (0, 0)) (hB0 : B (0, 0) ≠ 0) :
    ∃ V : C(S, ℂ) × ℂ → C(S, ℂ) × ℂ,
      AnalyticAt ℂ V (0, 0) ∧ V (0, 0) = (0, 0) ∧
      (∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        (V q).1 = q.1 ∧ (V q).2 * B (V q) = q.2) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        V (q.1, q.2 * B q) = q := by
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
  refine ⟨V, hRa, hV0, ?_, ?_⟩
  have hright : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), R (R.symm q) = q := by
    simpa only [show R (0, 0) = (0, 0) by simp [R, F]] using
      R.eventually_right_inverse' hsource
  · filter_upwards [hright] with q hq
    have hq' : F (V q) = q := hq
    exact Prod.mk.inj hq'
  · exact R.eventually_left_inverse hsource

theorem actual_joint_chart_fold_overlap (M : PerronWright.CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃ (B : C(S, ℂ) × ℂ → ℂ) (T : C(S, ℂ) × ℂ → C(S, ℂ)),
      AnalyticAt ℂ B (0, 0) ∧
      B (0, 0) = (PerronWright.FoldCoefficients.gamma M hM : ℂ)⁻¹ ∧
      AnalyticAt ℂ T (0, 0) ∧ T (0, 0) = 1 ∧
      deriv (fun X : ℂ => T (0, X)) 0 =
        (-(PerronWright.FoldCoefficients.gamma M hM : ℂ)) •
          M.complexPerronFunction hM ∧
      (∀ᶠ g : C(S, ℂ) in nhds 0,
        T (g, 0) = PerronWright.RadiusResponse.profile M hM g) ∧
      (∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        T (q.1, -(q.2 * B q)) =
          (PerronWright.TreeFold.centeredFoldCurve M hM q).2) ∧
      (∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        PerronWright.RadiusResponse.radius M hM q.1 * (q.2 * B q) ^ 2 =
          PerronWright.RadiusResponse.radius M hM q.1 -
            (PerronWright.TreeFold.centeredFoldCurve M hM q).1) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        PerronWright.TreeCritical.residual M
          ((PerronWright.RadiusResponse.radius M hM q.1 * (1 - q.2 ^ 2), q.1),
            T q) = 0 := by
  obtain ⟨H, hHa, hH0, hFactor⟩ :=
    PerronWright.TreeFoldJointDivision.centered_radius_joint_quadratic_factor_base M hM
  obtain ⟨B, hBa, hB0, hBsq⟩ :=
    PerronWright.TreeFoldJointChart.joint_normalized_square_root M hM H hHa hH0
  have hBn : B (0, 0) ≠ 0 := by
    rw [hB0]
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (PerronWright.FoldCoefficients.gamma_pos M hM).ne')
  obtain ⟨V, hVa, hV0, hVinv, hVleft⟩ :=
    joint_fold_coordinate_inverse_bilateral B hBa hBn
  let N : C(S, ℂ) × ℂ → C(S, ℂ) × ℂ := fun q => (q.1, -q.2)
  have hNa : AnalyticAt ℂ N (0, 0) := analyticAt_fst.prod analyticAt_snd.neg
  have hN0 : N (0, 0) = (0, 0) := by simp [N]
  have hNV : AnalyticAt ℂ (fun q => V (N q)) (0, 0) :=
    hVa.comp_of_eq hNa hN0
  have hNV0 : V (N (0, 0)) = (0, 0) := by rw [hN0, hV0]
  let T : C(S, ℂ) × ℂ → C(S, ℂ) := fun q =>
    (PerronWright.TreeFold.centeredFoldCurve M hM (V (N q))).2
  have hTa : AnalyticAt ℂ T (0, 0) :=
    analyticAt_snd.comp
      ((PerronWright.TreeFold.centeredFoldCurve_analytic M hM).comp_of_eq hNV hNV0)
  have hT0 : T (0, 0) = 1 := by
    have hc := (PerronWright.TreeFold.centeredFoldCurve_critical M hM).self_of_nhds
    simp only [T, hN0, hV0, hc]
    exact PerronWright.RadiusResponse.profile_base M hM
  have hTd : deriv (fun X : ℂ => T (0, X)) 0 =
      (-(PerronWright.FoldCoefficients.gamma M hM : ℂ)) •
        M.complexPerronFunction hM := by
    let γ : ℂ := PerronWright.FoldCoefficients.gamma M hM
    let v : ℂ → ℂ := fun X => (V (0, X)).2
    have hva : AnalyticAt ℂ v 0 := by
      have hs : AnalyticAt ℂ (fun X : ℂ => ((0 : C(S, ℂ)), X)) 0 :=
        analyticAt_const.prod analyticAt_id
      exact analyticAt_snd.comp (hVa.comp_of_eq hs rfl)
    have hvd : deriv v 0 = γ := by
      rw [PerronWright.TreeFoldJointChart.joint_fold_coordinate_inverse_vertical_derivative
        B V hBa hBn hVa hV0 hVinv, hB0, inv_inv]
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
    have hp : HasDerivAt
        (PerronWright.TreeFoldCurvature.profileSlice M hM)
        (M.complexPerronFunction hM) 0 := by
      have h :=
        (PerronWright.TreeFoldCurvature.profileSlice_analytic M hM).hasStrictDerivAt.hasDerivAt
      rw [PerronWright.TreeFoldCurvature.profileSlice_deriv M hM] at h
      exact h
    have hp' : HasDerivAt (fun X : ℂ =>
        PerronWright.TreeFoldCurvature.profileSlice M hM (s X))
        ((-γ) • M.complexPerronFunction hM) 0 := by
      have hp0 : HasDerivAt
          (PerronWright.TreeFoldCurvature.profileSlice M hM)
          (M.complexPerronFunction hM) (s 0) := by
        simpa only [hs0] using hp
      have h := hp0.scomp 0 hsd
      simpa only [hs0, Function.comp_def] using h
    have hnegsec : AnalyticAt ℂ
        (fun X : ℂ => ((0 : C(S, ℂ)), -X)) 0 :=
      analyticAt_const.prod analyticAt_id.neg
    have hnegsect : Filter.Tendsto
        (fun X : ℂ => ((0 : C(S, ℂ)), -X))
        (nhds 0) (nhds (0, 0)) := by
      simpa only [neg_zero] using hnegsec.continuousAt.tendsto
    have hVsec : ∀ᶠ X : ℂ in nhds 0, (V (0, -X)).1 = 0 := by
      filter_upwards [hnegsect.eventually hVinv] with X hX
      exact hX.1
    have heq : (fun X : ℂ => T (0, X)) =ᶠ[nhds 0]
        (fun X => PerronWright.TreeFoldCurvature.profileSlice M hM (s X)) := by
      filter_upwards [hVsec] with X hX
      simp only [T, N, s, v, PerronWright.TreeFold.centeredFoldCurve,
        PerronWright.TreeFoldCurvature.profileSlice, hX,
        PerronWright.TreeFold.criticalCoordinate_base, zero_add]
    rw [heq.deriv_eq]
    exact hp'.deriv
  have hNt : Filter.Tendsto N (𝓝 (0, 0)) (𝓝 (0, 0)) := by
    simpa only [hN0] using hNa.continuousAt.tendsto
  have hNVt : Filter.Tendsto (fun q => V (N q))
      (𝓝 (0, 0)) (𝓝 (0, 0)) := by
    simpa only [hNV0] using hNV.continuousAt.tendsto
  have hBne : ∀ᶠ p : C(S, ℂ) × ℂ in nhds (0, 0), B p ≠ 0 :=
    hBa.continuousAt.eventually_ne hBn
  have haxisInput : Filter.Tendsto
      (fun g : C(S, ℂ) => N (g, 0)) (nhds 0) (nhds (0, 0)) := by
    have hemb : Filter.Tendsto (fun g : C(S, ℂ) => (g, (0 : ℂ)))
        (nhds 0) (nhds (0, 0)) :=
      (analyticAt_id.prod analyticAt_const : AnalyticAt ℂ
        (fun g : C(S, ℂ) => (g, (0 : ℂ))) 0).continuousAt.tendsto
    exact hNt.comp hemb
  have haxisMap : Filter.Tendsto
      (fun g : C(S, ℂ) => V (N (g, 0))) (nhds 0) (nhds (0, 0)) := by
    have hemb : Filter.Tendsto (fun g : C(S, ℂ) => (g, (0 : ℂ)))
        (nhds 0) (nhds (0, 0)) :=
      (analyticAt_id.prod analyticAt_const : AnalyticAt ℂ
        (fun g : C(S, ℂ) => (g, (0 : ℂ))) 0).continuousAt.tendsto
    exact hNVt.comp hemb
  have hTaxis : ∀ᶠ g : C(S, ℂ) in nhds 0,
      T (g, 0) = PerronWright.RadiusResponse.profile M hM g := by
    filter_upwards [haxisInput.eventually hVinv, haxisMap.eventually hBne,
      PerronWright.TreeFold.centeredFoldCurve_critical M hM]
      with g hVi hBvg hcrit
    have hp2 : (V (N (g, 0))).2 = 0 := by
      have hm : (V (N (g, 0))).2 * B (V (N (g, 0))) = 0 := by
        simpa only [N, neg_zero] using hVi.2
      exact (mul_eq_zero.mp hm).resolve_right hBvg
    have hp : V (N (g, 0)) = (g, 0) := by
      apply Prod.ext
      · simpa only [N, neg_zero] using hVi.1
      · exact hp2
    change (PerronWright.TreeFold.centeredFoldCurve M hM
      (V (N (g, 0)))).2 = _
    rw [hp, hcrit]
    rfl
  refine ⟨B, T, hBa, hB0, hTa, hT0, hTd, hTaxis, ?_, ?_, ?_⟩
  · filter_upwards [hVleft] with q hq
    change (PerronWright.TreeFold.centeredFoldCurve M hM
      (V (q.1, -(-(q.2 * B q))))).2 = _
    simpa only [neg_neg] using
      congrArg (fun p : C(S, ℂ) × ℂ =>
        (PerronWright.TreeFold.centeredFoldCurve M hM p).2) hq
  · filter_upwards [hFactor, hBsq] with q hf hb
    calc
      PerronWright.RadiusResponse.radius M hM q.1 * (q.2 * B q) ^ 2 =
          q.2 ^ 2 * (PerronWright.RadiusResponse.radius M hM q.1 * B q ^ 2) := by ring
      _ = PerronWright.RadiusResponse.radius M hM q.1 -
          (PerronWright.TreeFold.centeredFoldCurve M hM q).1 := by
            rw [hb]
            exact hf.symm
  · have hVinv' := hNt.eventually hVinv
    have hFactor' := hNVt.eventually hFactor
    have hBsq' := hNVt.eventually hBsq
    have hEq' := hNVt.eventually
      (PerronWright.TreeFoldUniformField.centeredFoldCurve_equations M hM)
    filter_upwards [hVinv', hFactor', hBsq', hEq'] with q hVi hFa hBs hEq
    let p := V (N q)
    have hp1 : p.1 = q.1 := by simpa only [N] using hVi.1
    have hp2 : p.2 * B p = -q.2 := by simpa only [N] using hVi.2
    have hz : (PerronWright.TreeFold.centeredFoldCurve M hM p).1 =
        PerronWright.RadiusResponse.radius M hM q.1 * (1 - q.2 ^ 2) := by
      change PerronWright.RadiusResponse.radius M hM p.1 -
        (PerronWright.TreeFold.centeredFoldCurve M hM p).1 =
          p.2 ^ 2 * H p at hFa
      change PerronWright.RadiusResponse.radius M hM p.1 * B p ^ 2 = H p at hBs
      rw [hp1] at hFa hBs
      have hdef : PerronWright.RadiusResponse.radius M hM q.1 -
          (PerronWright.TreeFold.centeredFoldCurve M hM p).1 =
          PerronWright.RadiusResponse.radius M hM q.1 * q.2 ^ 2 := by
        calc
          _ = p.2 ^ 2 * H p := hFa
          _ = PerronWright.RadiusResponse.radius M hM q.1 *
              (p.2 * B p) ^ 2 := by
                rw [← hBs]
                ring
          _ = PerronWright.RadiusResponse.radius M hM q.1 * q.2 ^ 2 := by
                rw [hp2]
                ring
      linear_combination -hdef
    have hres := hEq.1
    change PerronWright.TreeCritical.residual M
      (((PerronWright.TreeFold.centeredFoldCurve M hM p).1, p.1), T q) = 0 at hres
    rw [hz, hp1] at hres
    exact hres


theorem least_fixed_on_new_joint_chart_near_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ T : C(S, ℂ) × ℂ → C(S, ℂ),
      AnalyticAt ℂ T (0, 0) ∧ T (0, 0) = 1 ∧
      deriv (fun X : ℂ => T (0, X)) 0 =
        (-(FoldCoefficients.gamma M hM : ℂ)) • M.complexPerronFunction hM ∧
      (∀ᶠ g : C(S, ℂ) in nhds 0,
        T (g, 0) = RadiusResponse.profile M hM g) ∧
      (∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        TreeCritical.residual M
          ((RadiusResponse.radius M hM q.1 * (1 - q.2 ^ 2), q.1), T q) = 0) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, 0 ≤ w → w < 1 → |w - 1| < δ →
        ∃ V : C(S, ℝ),
          Filter.Tendsto (M.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
          M.normalizedZeroTreeMap w V = V ∧
          T (0, (Real.sqrt (1 - w) : ℂ)) = TreeRealComplexBridge.complexify V := by
  obtain ⟨B, T, hBa, hB0, hTa, hT0, hTd, hTaxis, hmatch, hdef, hres⟩ :=
    actual_joint_chart_fold_overlap M hM
  have hsection : AnalyticAt ℂ (fun s : ℂ => ((0 : C(S, ℂ)), s)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hBslice : AnalyticAt ℂ (fun s : ℂ => B (0, s)) 0 :=
    hBa.comp_of_eq hsection rfl
  have hmatch0 : ∀ᶠ s : ℂ in 𝓝 0,
      T (0, -(s * B (0, s))) = TreeFoldCurvature.profileSlice M hM s := by
    simpa only [TreeFold.centeredFoldCurve, TreeFold.criticalCoordinate_base,
      zero_add, TreeFoldCurvature.profileSlice] using
      hsection.continuousAt.tendsto.eventually hmatch
  have hdef0 : ∀ᶠ s : ℂ in 𝓝 0,
      (s * B (0, s)) ^ 2 = 1 - TreeFoldCurvature.radiusSlice M hM s := by
    simpa only [RadiusResponse.radius_base, one_mul, TreeFold.centeredFoldCurve,
      TreeFold.criticalCoordinate_base, zero_add,
      TreeFoldCurvature.radiusSlice] using
      hsection.continuousAt.tendsto.eventually hdef
  have hB0re : 0 < (B (0, 0)).re := by
    rw [hB0, ← Complex.ofReal_inv]
    simpa only [Complex.ofReal_re] using
      inv_pos.mpr (FoldCoefficients.gamma_pos M hM)
  have hBre : ContinuousAt (fun s : ℂ => (B (0, s)).re) 0 :=
    Complex.continuous_re.continuousAt.comp hBslice.continuousAt
  have hBpos : ∀ᶠ s in nhds (0 : ℂ), 0 < (B (0, s)).re :=
    hBre.eventually (eventually_gt_nhds hB0re)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp ((hmatch0.and hdef0).and hBpos)
  let ell := M.normalizedPerronFunctional hM
  let η : ℝ := ρ / (2 * (‖ell‖ + 1))
  have hden : 0 < 2 * (‖ell‖ + 1) := by positivity
  have hη : 0 < η := div_pos hρ hden
  have hellηρ : ‖ell‖ * η < ρ := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).2
    nlinarith [norm_nonneg ell, hρ]
  obtain ⟨δ₀, hδ₀, hfold⟩ := M.least_fixed_on_foldCurve_near_one hM
  obtain ⟨δ₁, hδ₁, hnear⟩ := M.normalizedZeroTreeIter_limit_near_one hM η hη
  refine ⟨T, hTa, hT0, hTd, hTaxis, hres,
    min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro w hw hw1 hclose
  obtain ⟨V, hVlim, hVfix, hfoldEq⟩ :=
    hfold w hw hw1 (hclose.trans_le (min_le_left _ _))
  obtain ⟨W, hWlim, -, hWnorm⟩ :=
    hnear w hw hw1 (hclose.trans_le (min_le_right _ _))
  have hVW : V = W := tendsto_nhds_unique hVlim hWlim
  have hVnorm : ‖V - 1‖ < η := hVW ▸ hWnorm
  let U := TreeRealComplexBridge.complexify V
  let s := ell (U - 1)
  have hsNorm : ‖s‖ < ρ := by
    have hbound : ‖s‖ ≤ ‖ell‖ * ‖U - 1‖ := ell.le_opNorm (U - 1)
    have hUη : ‖U - 1‖ < η :=
      (TreeRealComplexBridge.norm_complexify_sub_one_le V).trans_lt hVnorm
    exact hbound.trans_lt
      ((mul_le_mul_of_nonneg_left hUη.le (norm_nonneg ell)).trans_lt hellηρ)
  have hsball : s ∈ Metric.ball (0 : ℂ) ρ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hsNorm
  have hsmatch_and := hball hsball
  rcases hsmatch_and with ⟨⟨hProfileMatch, hDefMatch⟩, hBspos⟩
  have hradius : TreeFoldCurvature.radiusSlice M hM s = (w : ℂ) :=
    congrArg Prod.fst hfoldEq
  have hprofile : TreeFoldCurvature.profileSlice M hM s = U :=
    congrArg Prod.snd hfoldEq
  let X : ℂ := -(s * B (0, s))
  have hXsq : X ^ 2 = 1 - (w : ℂ) := by
    dsimp [X]
    rw [neg_sq, hDefMatch, hradius]
  have hTX : T (0, X) = U := by
    dsimp [X]
    rw [hProfileMatch, hprofile]
  have hVbounds (x : S) : 0 ≤ V x ∧ V x ≤ 1 := by
    have hpoint : Filter.Tendsto (fun n => M.normalizedZeroTreeIter w n x)
        Filter.atTop (nhds (V x)) :=
      ((continuous_eval_const x).tendsto V).comp hVlim
    exact ⟨ge_of_tendsto' hpoint (fun n =>
        (M.normalizedZeroTreeIter_bounded w hw hw1.le n x).1),
      le_of_tendsto' hpoint (fun n =>
        (M.normalizedZeroTreeIter_bounded w hw hw1.le n x).2)⟩
  obtain ⟨r, hrneg, hsr⟩ :=
    M.physical_perron_coordinate_negative hM w hw hw1 V hVbounds hVfix
  change s = (r : ℂ) at hsr
  rw [hsr] at hBspos
  have hXre : 0 < X.re := by
    dsimp [X]
    rw [hsr]
    simp only [Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [mul_neg_of_neg_of_pos hrneg hBspos]
  have hsqrtSq : ((Real.sqrt (1 - w) : ℂ)) ^ 2 = 1 - (w : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 - w),
      Complex.ofReal_sub, Complex.ofReal_one]
  have hmul : (X - (Real.sqrt (1 - w) : ℂ)) *
      (X + (Real.sqrt (1 - w) : ℂ)) = 0 := by
    calc
      _ = X ^ 2 - (Real.sqrt (1 - w) : ℂ) ^ 2 := by ring
      _ = 0 := by rw [hXsq, hsqrtSq, sub_self]
  have hXeq : X = (Real.sqrt (1 - w) : ℂ) := by
    rcases mul_eq_zero.mp hmul with hminus | hplus
    · exact sub_eq_zero.mp hminus
    · have hxneg : X = -(Real.sqrt (1 - w) : ℂ) := by
        linear_combination hplus
      have hRe := congrArg Complex.re hxneg
      simp only [Complex.neg_re, Complex.ofReal_re] at hRe
      linarith [Real.sqrt_nonneg (1 - w)]
  refine ⟨V, hVlim, hVfix, ?_⟩
  rw [← hXeq]
  exact hTX


end PerronWright.TreeFoldPhysicalGluing
