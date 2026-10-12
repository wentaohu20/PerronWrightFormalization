import PerronWright.Analysis.FiniteIrreducibleLeastBranch
import PerronWright.Analysis.FiniteIrreducibleSquareRootFold
import PerronWright.Analysis.FiniteIrreducibleTreeSeries

/-! Matching the genuine finite least-tree branch to the positive square-root fold chart. -/

open MeasureTheory Filter
open scoped BigOperators
noncomputable section

namespace PerronWright

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The physical fixed point joins the critical endpoint from below in the
uniform norm. This does not identify a power-series radius. -/
theorem FiniteIrreducibleModel.normalizedZeroTreeIter_limit_near_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ w : ℝ, 0 ≤ w → w < 1 → |w - 1| < δ →
        ∃ V : C(S, ℝ),
          Filter.Tendsto (M.bjrModel.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
          M.bjrModel.normalizedZeroTreeMap w V = V ∧ ‖V - 1‖ < ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hendpoint := M.normalizedZeroTreeIter_one_converges hM
  have hnear : ∀ᶠ n : ℕ in atTop,
      ‖M.bjrModel.normalizedZeroTreeIter 1 n - 1‖ < ε / 2 := by
    filter_upwards [hendpoint.eventually (Metric.ball_mem_nhds _ hε2)] with n hn
    simpa [Metric.mem_ball, dist_eq_norm] using hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hnear
  have hcont : ContinuousAt (fun w : ℝ => M.bjrModel.normalizedZeroTreeIter w N) 1 :=
    (M.bjrModel.normalizedZeroTreeIter_continuous_parameter N).continuousAt
  have hparam : ∀ᶠ w : ℝ in nhds 1,
      ‖M.bjrModel.normalizedZeroTreeIter w N - M.bjrModel.normalizedZeroTreeIter 1 N‖ < ε / 2 := by
    filter_upwards [hcont.eventually (Metric.ball_mem_nhds _ hε2)] with w hw
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp hparam
  refine ⟨δ, hδ, ?_⟩
  intro w hw hw1 hclose
  obtain ⟨V, hVlim, hVbounds, hVfix, -⟩ :=
    M.normalizedZeroTreeIter_least_fixed w hw hw1.le
  refine ⟨V, hVlim, hVfix, ?_⟩
  have hparamw : ‖M.bjrModel.normalizedZeroTreeIter w N -
      M.bjrModel.normalizedZeroTreeIter 1 N‖ < ε / 2 :=
    hδball (by simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hclose)
  have hNbound : ‖M.bjrModel.normalizedZeroTreeIter 1 N - 1‖ < ε / 2 := hN N le_rfl
  calc
    ‖V - 1‖ ≤ ‖M.bjrModel.normalizedZeroTreeIter w N - 1‖ :=
      M.bjrModel.normalizedZeroTreeIter_fixed_gap_norm_le w hw hw1.le V hVbounds hVfix N
    _ ≤ ‖M.bjrModel.normalizedZeroTreeIter w N - M.bjrModel.normalizedZeroTreeIter 1 N‖ +
        ‖M.bjrModel.normalizedZeroTreeIter 1 N - 1‖ := by
          have hsplit : M.bjrModel.normalizedZeroTreeIter w N - 1 =
              (M.bjrModel.normalizedZeroTreeIter w N - M.bjrModel.normalizedZeroTreeIter 1 N) +
                (M.bjrModel.normalizedZeroTreeIter 1 N - 1) := by abel
          rw [hsplit]
          exact norm_add_le _ _
    _ < ε := by linarith

/-- Near the critical endpoint, the physical least fixed point lies on the
actual analytic fold curve, in its Perron coordinate. -/
theorem FiniteIrreducibleModel.least_fixed_on_foldCurve_near_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, 0 ≤ w → w < 1 → |w - 1| < δ →
      ∃ V : C(S, ℝ),
        Filter.Tendsto (M.bjrModel.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
        M.bjrModel.normalizedZeroTreeMap w V = V ∧
        FiniteIrreducibleFieldFold.foldCurve M hM
          (0, M.normalizedPerronFunctional hM
            (TreeRealComplexBridge.complexify V - 1)) =
          ((w : ℂ), TreeRealComplexBridge.complexify V) := by
  let ell := M.normalizedPerronFunctional hM
  have hlocal : ∀ᶠ (p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ))) in nhds
      (((0 : C(S, ℂ)), (0 : ℂ)), ((1 : ℂ), (1 : C(S, ℂ)))),
      M.foldResidual hM p = (0, 0) ↔
        FiniteIrreducibleFieldFold.foldCurve M hM p.1 = p.2 := by
    simpa only [FiniteIrreducibleFieldFold.foldCurve] using
      (Classical.choose_spec (M.foldCurve_germ hM)).2.2.2
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
  have hres : M.treeResidual (((w : ℂ), 0), U) = 0 :=
    (TreeRealComplexBridge.normalizedZeroTreeMap_fixed_iff_residual_zero M.bjrModel w V).mp hVfix
  have hfoldzero : M.foldResidual hM
      (((0 : C(S, ℂ)), s), ((w : ℂ), U)) = (0, 0) := by
    apply Prod.ext
    · exact hres
    · change ell U - ell 1 - ell (U - 1) = 0
      rw [map_sub]
      ring
  exact (hball hpball).mp hfoldzero

/-- A square-root chart for the existing fold curve, with the local inverse
property exposed so that real fixed points can be matched to the chart. -/
theorem FiniteIrreducibleSquareRootFold.fold_chart_left_inverse
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ (T : ℂ → C(S, ℂ)) (B : ℂ → ℂ),
      AnalyticAt ℂ T 0 ∧ T 0 = 1 ∧
      deriv T 0 = (-(FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ)) •
        M.complexPerronFunction hM ∧
      (∀ᶠ X in nhds (0 : ℂ),
        T X = (1 - X ^ 2) • NormedSpace.exp
          (-TreeCritical.degree M.bjrModel + M.complexOperator (T X))) ∧
      AnalyticAt ℂ B 0 ∧
      B 0 = (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ)⁻¹ ∧
      (∀ᶠ s in nhds (0 : ℂ),
        T (-(s * B s)) = FiniteIrreducibleFieldCurvature.profileSlice M hM s ∧
        (s * B s) ^ 2 = 1 - FiniteIrreducibleFieldCurvature.radiusSlice M hM s) := by
  obtain ⟨H, hHa, hH0, hFactor⟩ :=
    FiniteIrreducibleSquareRootFold.radius_deficit_factorization M hM
  obtain ⟨B, hBa, hB0, hBsq⟩ :=
    FiniteIrreducibleSquareRootFold.analytic_square_root_of_quadratic_factor M hM H hHa hH0
  let Q : ℂ → ℂ := id * B
  have hQa : AnalyticAt ℂ Q 0 := analyticAt_id.mul hBa
  have hQ0 : Q 0 = 0 := by simp [Q]
  have hQderiv : HasStrictDerivAt Q
      (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ)⁻¹ 0 := by
    simpa only [Q, hB0, id_eq, one_mul, zero_mul, add_zero] using
      (hasStrictDerivAt_id (0 : ℂ)).mul hBa.hasStrictDerivAt
  have hQd : deriv Q 0 = (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ)⁻¹ :=
    hQderiv.hasDerivAt.deriv
  have hγ : (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (FiniteIrreducibleFoldCoefficients.gamma_pos M hM).ne'
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
    FiniteIrreducibleFieldCurvature.profileSlice M hM (σ (-X))
  have hTa : AnalyticAt ℂ T 0 := by
    have hneg : AnalyticAt ℂ (fun X : ℂ => -X) 0 := analyticAt_id.neg
    have hinner : AnalyticAt ℂ (fun X : ℂ => σ (-X)) 0 := by
      have hσa' : AnalyticAt ℂ σ (-(0 : ℂ)) := by simpa using hσa
      simpa only [Function.comp_def] using hσa'.comp hneg
    exact (FiniteIrreducibleFieldCurvature.profileSlice_analytic M hM).comp_of_eq hinner
      (by simpa using hσ0)
  have hT0 : T 0 = 1 := by
    simpa only [T, neg_zero, hσ0] using FiniteIrreducibleFieldCurvature.profileSlice_base M hM
  have hσd : deriv σ 0 = (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ) := by
    have h := (hQa.hasStrictDerivAt.to_localInverse hQdne).hasDerivAt.deriv
    simpa only [hQ0, hQd, inv_inv] using h
  have hnegd : HasDerivAt (fun X : ℂ => -X) (-1) 0 :=
    (hasDerivAt_id (0 : ℂ)).neg
  have hσnegd : HasDerivAt (fun X : ℂ => σ (-X))
      (-(FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ)) 0 := by
    have hσhas := hσa.hasStrictDerivAt.hasDerivAt
    rw [hσd] at hσhas
    have hσhas' : HasDerivAt σ (FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ)
        (-(0 : ℂ)) := by simpa using hσhas
    have h := hσhas'.comp 0 hnegd
    simpa only [Function.comp_def, mul_neg, mul_one] using h
  have hTd : deriv T 0 = (-(FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ)) •
      M.complexPerronFunction hM := by
    have hp := (FiniteIrreducibleFieldCurvature.profileSlice_analytic M hM).hasStrictDerivAt.hasDerivAt
    rw [FiniteIrreducibleFieldCurvature.profileSlice_deriv] at hp
    have hp' : HasDerivAt (FiniteIrreducibleFieldCurvature.profileSlice M hM)
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
        (-TreeCritical.degree M.bjrModel + M.complexOperator (T X)) := by
    filter_upwards [hnegT.eventually hright, hσT.eventually hBsq,
      hσT.eventually (FiniteIrreducibleFieldCurvature.foldSlice_equation M hM)]
      with X hInv hBs hFs
    have hQneg : σ (-X) * B (σ (-X)) = -X := by simpa [Q] using hInv
    have hz : FiniteIrreducibleFieldCurvature.radiusSlice M hM (σ (-X)) = 1 - X ^ 2 := by
      have hh : 1 - FiniteIrreducibleFieldCurvature.radiusSlice M hM (σ (-X)) = X ^ 2 := calc
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
  · change FiniteIrreducibleFieldCurvature.profileSlice M hM (σ (-(-(s * B s)))) = _
    simpa [Q] using
      congrArg (FiniteIrreducibleFieldCurvature.profileSlice M hM) hsleft
  · calc
      (s * B s) ^ 2 = s ^ 2 * H s := by rw [mul_pow, hsBsq]
      _ = 1 - FiniteIrreducibleFieldCurvature.radiusSlice M hM s := (hFactor s).symm

theorem FiniteIrreducibleModel.physical_perron_coordinate_negative
    (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) (V : C(S, ℝ))
    (hV : ∀ a, 0 ≤ V a ∧ V a ≤ 1)
    (hfix : M.bjrModel.normalizedZeroTreeMap w V = V) :
    ∃ r : ℝ, r < 0 ∧ M.normalizedPerronFunctional hcrit
      (TreeRealComplexBridge.complexify V - 1) = (r : ℂ) := by
  let I : ℝ := ∑ a, M.weight a * M.perronFunction hcrit a * (V a - 1)
  have hVw (a : S) : V a ≤ w := by
    rw [← hfix]
    exact M.bjrModel.normalizedZeroTreeMap_le_w w hw V (fun b ↦ (hV b).2) a
  have hI : I ≤ w - 1 := by
    calc
      I ≤ ∑ a, M.weight a * M.perronFunction hcrit a * (w - 1) := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hVw a) 1)
          (mul_pos (M.weight_pos a) (M.perronFunction_pos hcrit a)).le
      _ = (w - 1) * M.average (M.perronFunction hcrit) := by
        rw [FiniteIrreducibleModel.average, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = w - 1 := by rw [M.perronFunction_average, mul_one]
  let r := I / M.alpha hcrit
  refine ⟨r, div_neg_of_neg_of_pos (hI.trans_lt (sub_neg.mpr hw1)) (M.alpha_pos hcrit), ?_⟩
  change (M.alpha hcrit : ℂ)⁻¹ * M.weightedFunctional hcrit
    (TreeRealComplexBridge.complexify V - 1) = (r : ℂ)
  have he : M.weightedFunctional hcrit (TreeRealComplexBridge.complexify V - 1) = (I : ℂ) := by
    rw [M.weightedFunctional_apply]
    simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply,
      TreeRealComplexBridge.complexify_apply, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    rfl
  rw [he]
  simp only [r, Complex.ofReal_div]
  ring


/-- The physical fixed point near criticality is the positive-real square-root
slice of the analytic chart. -/
theorem FiniteIrreducibleModel.least_fixed_on_square_root_chart_near_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ T : ℂ → C(S, ℂ), AnalyticAt ℂ T 0 ∧ T 0 = 1 ∧
      deriv T 0 = (-(FiniteIrreducibleFoldCoefficients.gamma M hM : ℂ)) •
        M.complexPerronFunction hM ∧
      (∀ᶠ X in nhds (0 : ℂ),
        T X = (1 - X ^ 2) • NormedSpace.exp
          (-TreeCritical.degree M.bjrModel + M.complexOperator (T X))) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, 0 ≤ w → w < 1 → |w - 1| < δ →
        ∃ V : C(S, ℝ),
          Filter.Tendsto (M.bjrModel.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
          M.bjrModel.normalizedZeroTreeMap w V = V ∧
          T (Real.sqrt (1 - w) : ℂ) = TreeRealComplexBridge.complexify V := by
  obtain ⟨T, B, hTa, hT0, hTd, hchart, hBa, hB0, hmatch⟩ :=
    FiniteIrreducibleSquareRootFold.fold_chart_left_inverse M hM
  have hB0re : 0 < (B 0).re := by
    rw [hB0, ← Complex.ofReal_inv]
    simpa only [Complex.ofReal_re] using
      inv_pos.mpr (FiniteIrreducibleFoldCoefficients.gamma_pos M hM)
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
  have hradius : FiniteIrreducibleFieldCurvature.radiusSlice M hM s = (w : ℂ) :=
    congrArg Prod.fst hfoldEq
  have hprofile : FiniteIrreducibleFieldCurvature.profileSlice M hM s = U :=
    congrArg Prod.snd hfoldEq
  let X : ℂ := -(s * B s)
  have hXsq : X ^ 2 = 1 - (w : ℂ) := by
    dsimp [X]
    rw [neg_sq, hsmatch.2, hradius]
  have hTX : T X = U := by
    dsimp [X]
    rw [hsmatch.1, hprofile]
  have hVbounds (x : S) : 0 ≤ V x ∧ V x ≤ 1 := by
    have hpoint : Filter.Tendsto (fun n => M.bjrModel.normalizedZeroTreeIter w n x)
        Filter.atTop (nhds (V x)) :=
      ((continuous_eval_const x).tendsto V).comp hVlim
    exact ⟨ge_of_tendsto' hpoint (fun n =>
        (M.bjrModel.normalizedZeroTreeIter_bounded w hw hw1.le n x).1),
      le_of_tendsto' hpoint (fun n =>
        (M.bjrModel.normalizedZeroTreeIter_bounded w hw hw1.le n x).2)⟩
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
