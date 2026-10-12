import PerronWright.Analysis.TreeRealComplexBridge
import PerronWright.Analysis.TreeEndpointConvergence
import PerronWright.Analysis.TreeFoldSquareRoot

/-!
The least real zero-field tree fixed point is identified with the
positive square-root chart near the critical endpoint. This includes
subcritical ordered uniqueness and convergence to the endpoint as `w ↑ 1`.
-/

open MeasureTheory Filter
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem CompactBJRModel.normalizedZeroTreeMap_ordered_fixed_unique
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1)
    (V W : C(S, ℝ)) (hVW : ∀ x, V x ≤ W x)
    (hW : ∀ x, W x ≤ 1)
    (hVfix : M.normalizedZeroTreeMap w V = V)
    (hWfix : M.normalizedZeroTreeMap w W = W) : V = W := by
  obtain ⟨c, hc, hcu⟩ := M.perronFunction_uniform_pos hM
  let B : ℝ := ‖W - V‖ / c
  have hB : 0 ≤ B := div_nonneg (norm_nonneg _) hc.le
  have hbase (x : S) : W x - V x ≤ B * M.perronFunction hM x := by
    have hnonneg : 0 ≤ W x - V x := sub_nonneg.mpr (hVW x)
    have hnorm : W x - V x ≤ ‖W - V‖ := by
      simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs,
        abs_of_nonneg hnonneg] using (W - V).norm_coe_le_norm x
    calc
      W x - V x ≤ ‖W - V‖ := hnorm
      _ = B * c := by simp [B, ne_of_gt hc]
      _ ≤ B * M.perronFunction hM x := mul_le_mul_of_nonneg_left (hcu x) hB
  have hbound (n : ℕ) (x : S) :
      W x - V x ≤ w ^ n * B * M.perronFunction hM x := by
    induction n generalizing x with
    | zero => simpa using hbase x
    | succ n ih =>
        have hstep := M.normalizedZeroTreeMap_order_lipschitz hM
          w (w ^ n * B) hw V W hVW hW ih x
        rw [hWfix, hVfix] at hstep
        convert hstep using 1
        simp only [pow_succ]
        ac_rfl
  apply ContinuousMap.ext
  intro x
  have hlim : Tendsto
      (fun n : ℕ => w ^ n * B * M.perronFunction hM x) atTop (nhds 0) := by
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one hw hw1).mul_const
      (B * M.perronFunction hM x) using 1
    · funext n
      ac_rfl
    · simp
  have hle : W x - V x ≤ 0 := ge_of_tendsto' hlim (fun n => hbound n x)
  exact le_antisymm (hVW x) (sub_nonpos.mp hle)

theorem CompactBJRModel.normalizedZeroTreeMap_unique_bounded_fixed
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) :
    ∃ V : C(S, ℝ),
      Filter.Tendsto (M.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
      (∀ x, 0 ≤ V x ∧ V x ≤ 1) ∧
      M.normalizedZeroTreeMap w V = V ∧
      ∀ W : C(S, ℝ), (∀ x, 0 ≤ W x ∧ W x ≤ 1) →
        M.normalizedZeroTreeMap w W = W → W = V := by
  obtain ⟨V, hlim, hVbounds, hVfix, hVleast⟩ :=
    M.normalizedZeroTreeIter_least_fixed hM w hw hw1
  refine ⟨V, hlim, hVbounds, hVfix, ?_⟩
  intro W hWbounds hWfix
  exact (M.normalizedZeroTreeMap_ordered_fixed_unique hM w hw hw1 V W
    (hVleast W (fun x => (hWbounds x).1) hWfix)
    (fun x => (hWbounds x).2) hVfix hWfix).symm

omit [MeasurableSpace S] [BorelSpace S] in
private theorem real_exp_apply (f : C(S, ℝ)) (x : S) :
    NormedSpace.exp f x = Real.exp (f x) := by
  simpa only [ContinuousMap.evalAlgHom_apply, ← Real.exp_eq_exp_ℝ] using
    NormedSpace.map_exp (ContinuousMap.evalAlgHom ℝ ℝ x)
      (ContinuousMap.evalCLM ℝ x).continuous f

theorem CompactBJRModel.normalizedZeroTreeMap_eq_smul_exp
    (M : CompactBJRModel S) (w : ℝ) (V : C(S, ℝ)) :
    M.normalizedZeroTreeMap w V =
      w • NormedSpace.exp (M.kernel.actionCLM M.mu (V - 1)) := by
  ext x
  rw [M.normalizedZeroTreeMap_apply, ContinuousMap.smul_apply,
    smul_eq_mul, real_exp_apply]
  rfl

theorem CompactBJRModel.normalizedZeroTreeIter_continuous_parameter
    (M : CompactBJRModel S) (n : ℕ) :
    Continuous (fun w : ℝ => M.normalizedZeroTreeIter w n) := by
  induction n with
  | zero => simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : C(S, ℝ))))
  | succ n ih =>
      have hfun : (fun w : ℝ => M.normalizedZeroTreeIter w (n + 1)) =
          (fun w : ℝ => w • NormedSpace.exp
            (M.kernel.actionCLM M.mu (M.normalizedZeroTreeIter w n - 1))) := by
        funext w
        rw [M.normalizedZeroTreeIter_succ, M.normalizedZeroTreeMap_eq_smul_exp]
      rw [hfun]
      exact continuous_id.smul
        (NormedSpace.exp_continuous.comp
          ((M.kernel.actionCLM M.mu).continuous.comp (ih.sub continuous_const)))

theorem CompactBJRModel.normalizedZeroTreeIter_fixed_gap_norm_le
    (M : CompactBJRModel S) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (V : C(S, ℝ)) (hV : ∀ x, 0 ≤ V x ∧ V x ≤ 1)
    (hfix : M.normalizedZeroTreeMap w V = V) (n : ℕ) :
    ‖V - 1‖ ≤ ‖M.normalizedZeroTreeIter w n - 1‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro x
  have hiter := M.normalizedZeroTreeIter_bounded w hw hw1 n x
  have hiterV := M.normalizedZeroTreeIter_le_fixed w hw V
    (fun y => (hV y).1) hfix n x
  have hleft : ‖(V - 1) x‖ = 1 - V x := by
    simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr (hV x).2)]
    ring
  have hright : ‖(M.normalizedZeroTreeIter w n - 1) x‖ =
      1 - M.normalizedZeroTreeIter w n x := by
    simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr hiter.2)]
    ring
  calc
    ‖(V - 1) x‖ = 1 - V x := hleft
    _ ≤ 1 - M.normalizedZeroTreeIter w n x := by linarith
    _ = ‖(M.normalizedZeroTreeIter w n - 1) x‖ := hright.symm
    _ ≤ ‖M.normalizedZeroTreeIter w n - 1‖ :=
      (M.normalizedZeroTreeIter w n - 1).norm_coe_le_norm x

/-- The physical fixed point joins the critical endpoint from below in the
uniform norm. This does not identify a power-series radius. -/
theorem CompactBJRModel.normalizedZeroTreeIter_limit_near_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ w : ℝ, 0 ≤ w → w < 1 → |w - 1| < δ →
        ∃ V : C(S, ℝ),
          Filter.Tendsto (M.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
          M.normalizedZeroTreeMap w V = V ∧ ‖V - 1‖ < ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hendpoint := M.normalizedZeroTreeIter_one_converges hM
  have hnear : ∀ᶠ n : ℕ in atTop,
      ‖M.normalizedZeroTreeIter 1 n - 1‖ < ε / 2 := by
    filter_upwards [hendpoint.eventually (Metric.ball_mem_nhds _ hε2)] with n hn
    simpa [Metric.mem_ball, dist_eq_norm] using hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hnear
  have hcont : ContinuousAt (fun w : ℝ => M.normalizedZeroTreeIter w N) 1 :=
    (M.normalizedZeroTreeIter_continuous_parameter N).continuousAt
  have hparam : ∀ᶠ w : ℝ in nhds 1,
      ‖M.normalizedZeroTreeIter w N - M.normalizedZeroTreeIter 1 N‖ < ε / 2 := by
    filter_upwards [hcont.eventually (Metric.ball_mem_nhds _ hε2)] with w hw
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp hparam
  refine ⟨δ, hδ, ?_⟩
  intro w hw hw1 hclose
  obtain ⟨V, hVlim, hVbounds, hVfix, -⟩ :=
    M.normalizedZeroTreeIter_least_fixed hM w hw hw1
  refine ⟨V, hVlim, hVfix, ?_⟩
  have hparamw : ‖M.normalizedZeroTreeIter w N -
      M.normalizedZeroTreeIter 1 N‖ < ε / 2 :=
    hδball (by simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hclose)
  have hNbound : ‖M.normalizedZeroTreeIter 1 N - 1‖ < ε / 2 := hN N le_rfl
  calc
    ‖V - 1‖ ≤ ‖M.normalizedZeroTreeIter w N - 1‖ :=
      M.normalizedZeroTreeIter_fixed_gap_norm_le w hw hw1.le V hVbounds hVfix N
    _ ≤ ‖M.normalizedZeroTreeIter w N - M.normalizedZeroTreeIter 1 N‖ +
        ‖M.normalizedZeroTreeIter 1 N - 1‖ := by
          have hsplit : M.normalizedZeroTreeIter w N - 1 =
              (M.normalizedZeroTreeIter w N - M.normalizedZeroTreeIter 1 N) +
                (M.normalizedZeroTreeIter 1 N - 1) := by abel
          rw [hsplit]
          exact norm_add_le _ _
    _ < ε := by linarith

omit [MeasurableSpace S] [BorelSpace S] in
theorem TreeRealComplexBridge.norm_complexify_le
    (V : C(S, ℝ)) : ‖TreeRealComplexBridge.complexify V‖ ≤ ‖V‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro x
  simpa only [TreeRealComplexBridge.complexify_apply, Complex.norm_real] using
    V.norm_coe_le_norm x

omit [MeasurableSpace S] [BorelSpace S] in
theorem TreeRealComplexBridge.norm_complexify_sub_one_le
    (V : C(S, ℝ)) :
    ‖TreeRealComplexBridge.complexify V - 1‖ ≤ ‖V - 1‖ := by
  rw [← TreeRealComplexBridge.complexify_one,
    ← TreeRealComplexBridge.complexify_sub]
  exact TreeRealComplexBridge.norm_complexify_le (V - 1)

/-- Near the critical endpoint, the physical least fixed point lies on the
actual analytic fold curve, in its Perron coordinate. -/
theorem CompactBJRModel.least_fixed_on_foldCurve_near_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, 0 ≤ w → w < 1 → |w - 1| < δ →
      ∃ V : C(S, ℝ),
        Filter.Tendsto (M.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
        M.normalizedZeroTreeMap w V = V ∧
        TreeFold.foldCurve M hM
          (0, M.normalizedPerronFunctional hM
            (TreeRealComplexBridge.complexify V - 1)) =
          ((w : ℂ), TreeRealComplexBridge.complexify V) := by
  let ell := M.normalizedPerronFunctional hM
  have hlocal : ∀ᶠ (p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ))) in nhds
      (((0 : C(S, ℂ)), (0 : ℂ)), ((1 : ℂ), (1 : C(S, ℂ)))),
      TreeFold.foldResidual M hM p = (0, 0) ↔
        TreeFold.foldCurve M hM p.1 = p.2 := by
    simpa only [TreeFold.foldCurve] using
      (Classical.choose_spec (TreeFold.foldCurve_germ M hM)).2.2.2
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  let η : ℝ := ρ / (2 * (‖ell‖ + 1))
  have hden : 0 < 2 * (‖ell‖ + 1) := by positivity
  have hη : 0 < η := div_pos hρ hden
  have hηρ : η < ρ := by
    dsimp [η]
    apply (div_lt_iff₀ hden).2
    nlinarith [norm_nonneg ell]
  have hellηρ : ‖ell‖ * η < ρ := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).2
    nlinarith [norm_nonneg ell, hρ]
  obtain ⟨δ₀, hδ₀, hnear⟩ := M.normalizedZeroTreeIter_limit_near_one hM η hη
  refine ⟨min δ₀ η, lt_min hδ₀ hη, ?_⟩
  intro w hw hw1 hclose
  obtain ⟨V, hVlim, hVfix, hVnorm⟩ :=
    hnear w hw hw1 (hclose.trans_le (min_le_left _ _))
  refine ⟨V, hVlim, hVfix, ?_⟩
  let U := TreeRealComplexBridge.complexify V
  let s := ell (U - 1)
  have hUnorm : ‖U - 1‖ < ρ :=
    (TreeRealComplexBridge.norm_complexify_sub_one_le V).trans_lt
      (hVnorm.trans hηρ)
  have hsNorm : ‖s‖ < ρ := by
    have hbound : ‖s‖ ≤ ‖ell‖ * ‖U - 1‖ := ell.le_opNorm (U - 1)
    have hUη : ‖U - 1‖ < η :=
      (TreeRealComplexBridge.norm_complexify_sub_one_le V).trans_lt hVnorm
    exact hbound.trans_lt ((mul_le_mul_of_nonneg_left hUη.le (norm_nonneg ell)).trans_lt hellηρ)
  have hwNorm : ‖(w : ℂ) - 1‖ < ρ := by
    have hwη : |w - 1| < η := hclose.trans_le (min_le_right _ _)
    simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using
      hwη.trans hηρ
  have hpball :
      (((0 : C(S, ℂ)), s), ((w : ℂ), U)) ∈
        Metric.ball ((((0 : C(S, ℂ)), (0 : ℂ)),
          ((1 : ℂ), (1 : C(S, ℂ))))) ρ := by
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    exact max_lt (max_lt hρ (by simpa only [dist_zero_right] using hsNorm))
      (max_lt (by simpa only [dist_eq_norm] using hwNorm)
        (by simpa only [dist_eq_norm] using hUnorm))
  have hres : TreeCritical.residual M (((w : ℂ), 0), U) = 0 :=
    (TreeRealComplexBridge.normalizedZeroTreeMap_fixed_iff_residual_zero M w V).mp hVfix
  have hfoldzero : TreeFold.foldResidual M hM
      (((0 : C(S, ℂ)), s), ((w : ℂ), U)) = (0, 0) := by
    apply Prod.ext
    · exact hres
    · change ell U - ell 1 - ell (U - 1) = 0
      rw [map_sub]
      ring
  exact (hball hpball).mp hfoldzero

/-- A square-root chart for the existing fold curve, with the local inverse
property exposed so that real fixed points can be matched to the chart. -/
theorem TreeFoldSquareRoot.fold_chart_left_inverse
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (T : ℂ → C(S, ℂ)) (B : ℂ → ℂ),
      AnalyticAt ℂ T 0 ∧ T 0 = 1 ∧
      deriv T 0 = (-(FoldCoefficients.gamma M hM : ℂ)) •
        M.complexPerronFunction hM ∧
      (∀ᶠ X in nhds (0 : ℂ),
        T X = (1 - X ^ 2) • NormedSpace.exp
          (-TreeCritical.degree M + M.kernel.complexActionCLM M.mu (T X))) ∧
      AnalyticAt ℂ B 0 ∧
      B 0 = (FoldCoefficients.gamma M hM : ℂ)⁻¹ ∧
      (∀ᶠ s in nhds (0 : ℂ),
        T (-(s * B s)) = TreeFoldCurvature.profileSlice M hM s ∧
        (s * B s) ^ 2 = 1 - TreeFoldCurvature.radiusSlice M hM s) := by
  obtain ⟨H, hHa, hH0, hFactor⟩ :=
    TreeFoldSquareRoot.radius_deficit_factorization M hM
  obtain ⟨B, hBa, hB0, hBsq⟩ :=
    TreeFoldSquareRoot.analytic_square_root_of_quadratic_factor M hM H hHa hH0
  let Q : ℂ → ℂ := id * B
  have hQa : AnalyticAt ℂ Q 0 := analyticAt_id.mul hBa
  have hQ0 : Q 0 = 0 := by simp [Q]
  have hQderiv : HasStrictDerivAt Q
      (FoldCoefficients.gamma M hM : ℂ)⁻¹ 0 := by
    simpa only [Q, hB0, id_eq, one_mul, zero_mul, add_zero] using
      (hasStrictDerivAt_id (0 : ℂ)).mul hBa.hasStrictDerivAt
  have hQd : deriv Q 0 = (FoldCoefficients.gamma M hM : ℂ)⁻¹ :=
    hQderiv.hasDerivAt.deriv
  have hγ : (FoldCoefficients.gamma M hM : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (FoldCoefficients.gamma_pos M hM).ne'
  have hQdne : deriv Q 0 ≠ 0 := by rw [hQd]; exact inv_ne_zero hγ
  let σ : ℂ → ℂ := hQa.hasStrictDerivAt.localInverse Q (deriv Q 0) 0 hQdne
  have hσa : AnalyticAt ℂ σ 0 := by
    have h := hQa.analyticAt_localInverse hQdne
    simpa only [hQ0] using h
  have hσ0 : σ 0 = 0 := by
    have h := (hQa.hasStrictDerivAt.eventually_left_inverse hQdne).self_of_nhds
    simpa only [hQ0] using h
  have hleft : ∀ᶠ s in nhds (0 : ℂ), σ (Q s) = s :=
    hQa.hasStrictDerivAt.eventually_left_inverse hQdne
  let T : ℂ → C(S, ℂ) := fun X =>
    TreeFoldCurvature.profileSlice M hM (σ (-X))
  have hTa : AnalyticAt ℂ T 0 := by
    have hneg : AnalyticAt ℂ (fun X : ℂ => -X) 0 := analyticAt_id.neg
    have hinner : AnalyticAt ℂ (fun X : ℂ => σ (-X)) 0 := by
      have hσa' : AnalyticAt ℂ σ (-(0 : ℂ)) := by simpa using hσa
      simpa only [Function.comp_def] using hσa'.comp hneg
    exact (TreeFoldCurvature.profileSlice_analytic M hM).comp_of_eq hinner
      (by simpa using hσ0)
  have hT0 : T 0 = 1 := by
    simpa only [T, neg_zero, hσ0] using TreeFoldCurvature.profileSlice_base M hM
  have hσd : deriv σ 0 = (FoldCoefficients.gamma M hM : ℂ) := by
    have h := (hQa.hasStrictDerivAt.to_localInverse hQdne).hasDerivAt.deriv
    simpa only [hQ0, hQd, inv_inv] using h
  have hnegd : HasDerivAt (fun X : ℂ => -X) (-1) 0 :=
    (hasDerivAt_id (0 : ℂ)).neg
  have hσnegd : HasDerivAt (fun X : ℂ => σ (-X))
      (-(FoldCoefficients.gamma M hM : ℂ)) 0 := by
    have hσhas := hσa.hasStrictDerivAt.hasDerivAt
    rw [hσd] at hσhas
    have hσhas' : HasDerivAt σ (FoldCoefficients.gamma M hM : ℂ)
        (-(0 : ℂ)) := by simpa using hσhas
    have h := hσhas'.comp 0 hnegd
    simpa only [Function.comp_def, mul_neg, mul_one] using h
  have hTd : deriv T 0 = (-(FoldCoefficients.gamma M hM : ℂ)) •
      M.complexPerronFunction hM := by
    have hp := (TreeFoldCurvature.profileSlice_analytic M hM).hasStrictDerivAt.hasDerivAt
    rw [TreeFoldCurvature.profileSlice_deriv] at hp
    have hp' : HasDerivAt (TreeFoldCurvature.profileSlice M hM)
        (M.complexPerronFunction hM) (σ (-(0 : ℂ))) := by
      simpa only [neg_zero, hσ0] using hp
    have h := hp'.scomp 0 hσnegd
    simpa only [T, Function.comp_def, hσ0, neg_zero] using h.deriv
  have hnegT : Filter.Tendsto (fun X : ℂ => -X) (nhds 0) (nhds 0) := by
    simpa only [neg_zero] using
      (continuous_neg.continuousAt : ContinuousAt (fun X : ℂ => -X) 0).tendsto
  have hσT : Filter.Tendsto (fun X : ℂ => σ (-X)) (nhds 0) (nhds 0) := by
    simpa only [hσ0, Function.comp_def] using hσa.continuousAt.tendsto.comp hnegT
  have hright : ∀ᶠ X in nhds (0 : ℂ), Q (σ X) = X := by
    simpa only [hQ0] using hQa.hasStrictDerivAt.eventually_right_inverse hQdne
  have hchart : ∀ᶠ X in nhds (0 : ℂ),
      T X = (1 - X ^ 2) • NormedSpace.exp
        (-TreeCritical.degree M + M.kernel.complexActionCLM M.mu (T X)) := by
    filter_upwards [hnegT.eventually hright, hσT.eventually hBsq,
      hσT.eventually (TreeFoldCurvature.foldSlice_equation M hM)]
      with X hInv hBs hFs
    have hQneg : σ (-X) * B (σ (-X)) = -X := by simpa [Q] using hInv
    have hz : TreeFoldCurvature.radiusSlice M hM (σ (-X)) = 1 - X ^ 2 := by
      have hh : 1 - TreeFoldCurvature.radiusSlice M hM (σ (-X)) = X ^ 2 := calc
        _ = (σ (-X)) ^ 2 * H (σ (-X)) := hFactor (σ (-X))
        _ = (σ (-X)) ^ 2 * B (σ (-X)) ^ 2 := by rw [hBs]
        _ = (σ (-X) * B (σ (-X))) ^ 2 := by ring
        _ = X ^ 2 := by rw [hQneg]; ring
      linear_combination -hh
    change T X = _ at hFs
    rw [hz] at hFs
    exact hFs
  refine ⟨T, B, hTa, hT0, hTd, hchart, hBa, hB0, ?_⟩
  filter_upwards [hleft, hBsq] with s hsleft hsBsq
  constructor
  · change TreeFoldCurvature.profileSlice M hM (σ (-(-(s * B s)))) = _
    simpa [Q] using
      congrArg (TreeFoldCurvature.profileSlice M hM) hsleft
  · calc
      (s * B s) ^ 2 = s ^ 2 * H s := by rw [mul_pow, hsBsq]
      _ = 1 - TreeFoldCurvature.radiusSlice M hM s := (hFactor s).symm

theorem CompactBJRModel.physical_perron_coordinate_negative
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1)
    (V : C(S, ℝ)) (hV : ∀ x, 0 ≤ V x ∧ V x ≤ 1)
    (hfix : M.normalizedZeroTreeMap w V = V) :
    ∃ r : ℝ, r < 0 ∧
      M.normalizedPerronFunctional hM
        (TreeRealComplexBridge.complexify V - 1) = (r : ℂ) := by
  let u := M.perronFunction hM
  have hVw (x : S) : V x ≤ w := by
    rw [← hfix]
    exact M.normalizedZeroTreeMap_le_w w hw V (fun y => (hV y).2) x
  have hint₁ : Integrable (fun x : S => u x * (V x - 1)) M.mu :=
    (u.continuous.mul (V.continuous.sub continuous_const)).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hint₂ : Integrable (fun x : S => (w - 1) * u x) M.mu :=
    (continuous_const.mul u.continuous).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hI : M.weightedIntegral hM (V - 1) ≤ w - 1 := by
    have h := integral_mono hint₁ hint₂ (fun x => by
      have hp := mul_le_mul_of_nonneg_left (sub_le_sub_right (hVw x) 1)
        (M.perronFunction_pos hM x).le
      calc
        u x * (V x - 1) ≤ u x * (w - 1) := hp
        _ = (w - 1) * u x := mul_comm _ _)
    change (∫ x, u x * (V x - 1) ∂M.mu) ≤ w - 1
    rw [integral_const_mul] at h
    have hu : (∫ x, u x ∂M.mu) = 1 := M.perronFunction_integral hM
    rw [hu, mul_one] at h
    exact h
  have hIneg : M.weightedIntegral hM (V - 1) < 0 :=
    hI.trans_lt (sub_neg.mpr hw1)
  let r : ℝ := M.weightedIntegral hM (V - 1) / M.alpha hM
  have hrneg : r < 0 := div_neg_of_neg_of_pos hIneg (M.alpha_pos hM)
  refine ⟨r, hrneg, ?_⟩
  have hcomplex : M.weightedIntegralComplex hM
      (TreeRealComplexBridge.complexify V - 1) =
      (M.weightedIntegral hM (V - 1) : ℂ) := by
    unfold CompactBJRModel.weightedIntegralComplex CompactBJRModel.weightedIntegral
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply,
      TreeRealComplexBridge.complexify_apply]
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  change (M.alpha hM : ℂ)⁻¹ * M.weightedIntegralComplex hM
    (TreeRealComplexBridge.complexify V - 1) = (r : ℂ)
  rw [hcomplex]
  simp only [r, Complex.ofReal_div]
  ring

/-- The physical fixed point near criticality is the positive-real square-root
slice of the analytic chart. -/
theorem CompactBJRModel.least_fixed_on_square_root_chart_near_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ T : ℂ → C(S, ℂ), AnalyticAt ℂ T 0 ∧ T 0 = 1 ∧
      deriv T 0 = (-(FoldCoefficients.gamma M hM : ℂ)) •
        M.complexPerronFunction hM ∧
      (∀ᶠ X in nhds (0 : ℂ),
        T X = (1 - X ^ 2) • NormedSpace.exp
          (-TreeCritical.degree M + M.kernel.complexActionCLM M.mu (T X))) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, 0 ≤ w → w < 1 → |w - 1| < δ →
        ∃ V : C(S, ℝ),
          Filter.Tendsto (M.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
          M.normalizedZeroTreeMap w V = V ∧
          T (Real.sqrt (1 - w) : ℂ) = TreeRealComplexBridge.complexify V := by
  obtain ⟨T, B, hTa, hT0, hTd, hchart, hBa, hB0, hmatch⟩ :=
    TreeFoldSquareRoot.fold_chart_left_inverse M hM
  have hB0re : 0 < (B 0).re := by
    rw [hB0, ← Complex.ofReal_inv]
    simpa only [Complex.ofReal_re] using
      inv_pos.mpr (FoldCoefficients.gamma_pos M hM)
  have hBre : ContinuousAt (fun s : ℂ => (B s).re) 0 :=
    Complex.continuous_re.continuousAt.comp hBa.continuousAt
  have hBpos : ∀ᶠ s in nhds (0 : ℂ), 0 < (B s).re :=
    hBre.eventually (eventually_gt_nhds hB0re)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hmatch.and hBpos)
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
  refine ⟨T, hTa, hT0, hTd, hchart, min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
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
  rcases hsmatch_and with ⟨hsmatch, hBspos⟩
  have hradius : TreeFoldCurvature.radiusSlice M hM s = (w : ℂ) :=
    congrArg Prod.fst hfoldEq
  have hprofile : TreeFoldCurvature.profileSlice M hM s = U :=
    congrArg Prod.snd hfoldEq
  let X : ℂ := -(s * B s)
  have hXsq : X ^ 2 = 1 - (w : ℂ) := by
    dsimp [X]
    rw [neg_sq, hsmatch.2, hradius]
  have hTX : T X = U := by
    dsimp [X]
    rw [hsmatch.1, hprofile]
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

end PerronWright
