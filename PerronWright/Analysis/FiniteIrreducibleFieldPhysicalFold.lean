import PerronWright.Analysis.FiniteIrreducibleFieldSeriesPhysical
import PerronWright.Analysis.FiniteIrreducibleFieldBranchBounds
import PerronWright.Analysis.FiniteIrreducibleJointPhysicalFold

/-!
# The actual nonzero real-field least branch meets the joint analytic fold

The tree series and zero-start least branch are already constructed. Local
fold uniqueness and a proved strictly negative Perron coordinate identify
their positive square-root side at every sufficiently small real field.
The activity window is allowed to depend on the field; no complex-field
global continuation is assumed or claimed.
-/

open Filter Topology
open scoped BigOperators ENNReal
noncomputable section

namespace PerronWright.FiniteIrreducibleFieldPhysicalFold

open PerronWright
variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem fixed_on_centeredFoldCurve_eventually (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ∀ᶠ p : (C(S, ℂ) × ℂ) × C(S, ℂ) in 𝓝 ((0, 1), 1),
      M.treeResidual ((p.1.2, p.1.1), p.2) = 0 →
        FiniteIrreducibleFieldFold.centeredFoldCurve M hcrit
          (p.1.1, M.normalizedPerronFunctional hcrit
            (p.2 - FiniteIrreducibleRadiusResponse.profile M hcrit p.1.1)) =
          (p.1.2, p.2) := by
  let ell := M.normalizedPerronFunctional hcrit
  let j : (C(S, ℂ) × ℂ) × C(S, ℂ) → (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) :=
    fun p ↦ ((p.1.1, ell (p.2 - 1)), (p.1.2, p.2))
  have hj : Continuous j := by fun_prop
  have hj0 : j ((0, 1), 1) = ((0, 0), (1, 1)) := by simp [j]
  have ht : Tendsto j (𝓝 ((0, 1), 1)) (𝓝 ((0, 0), (1, 1))) :=
    hj0 ▸ hj.tendsto ((0, 1), 1)
  have hlocal : ∀ᶠ p in 𝓝 (((0 : C(S, ℂ)), (0 : ℂ)), ((1 : ℂ), (1 : C(S, ℂ)))),
      M.foldResidual hcrit p = (0, 0) ↔
        FiniteIrreducibleFieldFold.foldCurve M hcrit p.1 = p.2 := by
    simpa only [FiniteIrreducibleFieldFold.foldCurve] using
      (Classical.choose_spec (M.foldCurve_germ hcrit)).2.2.2
  filter_upwards [ht.eventually hlocal] with p hp hres
  have hzero : M.foldResidual hcrit (j p) = (0, 0) := by
    apply Prod.ext
    · exact hres
    · change ell p.2 - ell 1 - ell (p.2 - 1) = 0
      rw [map_sub]
      ring
  have he := hp.mp hzero
  change FiniteIrreducibleFieldFold.foldCurve M hcrit (p.1.1,
    FiniteIrreducibleFieldFold.criticalCoordinate M hcrit p.1.1 +
      ell (p.2 - FiniteIrreducibleRadiusResponse.profile M hcrit p.1.1)) = (p.1.2, p.2)
  have hc : FiniteIrreducibleFieldFold.criticalCoordinate M hcrit p.1.1 +
      ell (p.2 - FiniteIrreducibleRadiusResponse.profile M hcrit p.1.1) = ell (p.2 - 1) := by
    rw [FiniteIrreducibleFieldFold.criticalCoordinate, ← map_add]
    congr 1
    abel
  rw [hc]
  exact he

theorem exists_joint_fold_identified_with_real_field_series
    (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∃ T : C(S, ℂ) × ℂ → C(S, ℂ),
      AnalyticAt ℂ T (0, 0) ∧ T (0, 0) = 1 ∧
      deriv (fun X : ℂ ↦ T (0, X)) 0 =
        (-(FiniteIrreducibleFoldCoefficients.gamma M hcrit : ℂ)) • M.complexPerronFunction hcrit ∧
      (∀ᶠ g : C(S, ℂ) in 𝓝 0,
        T (g, 0) = FiniteIrreducibleRadiusResponse.profile M hcrit g) ∧
      (∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        M.treeResidual ((FiniteIrreducibleRadiusResponse.radius M hcrit q.1 * (1 - q.2 ^ 2), q.1),
          T q) = 0) ∧
      ∀ᶠ g : C(S, ℂ) in 𝓝 0, star g = g →
        ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, 0 ≤ w → w < 1 → |w - 1| < δ →
          ∃ V : C(S, ℝ),
            Tendsto (M.fieldTreeIter ((FiniteIrreducibleRadiusResponse.radius M hcrit g).re * w)
              (FiniteIrreducibleModel.realPartMap g)) atTop (𝓝 V) ∧
            M.fieldTreeMap ((FiniteIrreducibleRadiusResponse.radius M hcrit g).re * w)
              (FiniteIrreducibleModel.realPartMap g) V = V ∧
            T (g, (Real.sqrt (1 - w) : ℂ)) = TreeRealComplexBridge.complexify V ∧
            (M.fieldFMS g).sum (FiniteIrreducibleRadiusResponse.radius M hcrit g * (w : ℂ)) =
              TreeRealComplexBridge.complexify V := by
  obtain ⟨B, T, hBa, hB0, hTa, hT0, hTd, hTaxis, hmatch, hdef, hres⟩ :=
    FiniteIrreducibleJointPhysicalFold.actual_joint_chart_fold_overlap M hcrit
  have hB0pos : 0 < (B (0, 0)).re := by
    rw [hB0, ← Complex.ofReal_inv]
    simpa only [Complex.ofReal_re] using
      inv_pos.mpr (FiniteIrreducibleFoldCoefficients.gamma_pos M hcrit)
  have hBpos : ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), 0 < (B q).re :=
    (Complex.continuous_re.continuousAt.comp hBa.continuousAt).eventually
      (eventually_gt_nhds hB0pos)
  obtain ⟨rFold, hrFold, hFoldBall⟩ :=
    Metric.mem_nhds_iff.mp (fixed_on_centeredFoldCurve_eventually M hcrit)
  obtain ⟨rChart, hrChart, hChartBall⟩ :=
    Metric.mem_nhds_iff.mp ((hmatch.and hdef).and hBpos)
  let ell := M.normalizedPerronFunctional hcrit
  let eta : ℝ := min (rFold / 4) (rChart / (2 * (‖ell‖ + 1)))
  have heta : 0 < eta := lt_min (by positivity) (by positivity)
  have h2etaFold : 2 * eta < rFold := by
    have hh : eta ≤ rFold / 4 := min_le_left _ _
    nlinarith
  have hellEtaChart : ‖ell‖ * eta < rChart := by
    have hh : eta ≤ rChart / (2 * (‖ell‖ + 1)) := min_le_right _ _
    have hden : 0 < 2 * (‖ell‖ + 1) := by positivity
    have hb := (le_div_iff₀ hden).mp hh
    nlinarith [norm_nonneg ell]
  have hτnear : ∀ᶠ g in 𝓝 (0 : C(S, ℂ)),
      ‖FiniteIrreducibleRadiusResponse.profile M hcrit g - 1‖ < eta := by
    have ht : Tendsto (FiniteIrreducibleRadiusResponse.profile M hcrit) (𝓝 0) (𝓝 1) := by
      simpa only [FiniteIrreducibleRadiusResponse.profile_base] using
        (FiniteIrreducibleRadiusResponse.profile_analytic M hcrit).continuousAt.tendsto
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp ht eta heta
  have hρnear : ∀ᶠ g in 𝓝 (0 : C(S, ℂ)),
      ‖FiniteIrreducibleRadiusResponse.radius M hcrit g - 1‖ < eta := by
    have ht : Tendsto (FiniteIrreducibleRadiusResponse.radius M hcrit) (𝓝 0) (𝓝 1) := by
      simpa only [FiniteIrreducibleRadiusResponse.radius_base] using
        (FiniteIrreducibleRadiusResponse.radius_analytic M hcrit).continuousAt.tendsto
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp ht eta heta
  have hgsmall : ∀ᶠ g in 𝓝 (0 : C(S, ℂ)), ‖g‖ < min rFold rChart := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨min rFold rChart, lt_min hrFold hrChart, ?_⟩
    intro g hg
    simpa only [dist_zero_right] using hg
  refine ⟨T, hTa, hT0, hTd, hTaxis, hres, ?_⟩
  filter_upwards [M.real_critical_tilt_eventually hcrit, hτnear, hρnear, hgsmall]
    with g hdata hτnorm hρnorm hgnorm
  intro hreal
  obtain ⟨hτ, hρpos, hρim, hτc, hτfix, hcritical⟩ := hdata hreal
  let τ := FiniteIrreducibleModel.realCriticalProfile M hcrit g
  let rho := (FiniteIrreducibleRadiusResponse.radius M hcrit g).re
  let gr := FiniteIrreducibleModel.realPartMap g
  have hρc : (rho : ℂ) = FiniteIrreducibleRadiusResponse.radius M hcrit g := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hρim.symm
  obtain ⟨δN, hδN, hNear⟩ := M.fieldTreeIter_limit_near_critical_profile gr τ hτ rho hτfix hcritical heta
  let δ : ℝ := min δN (eta / (‖FiniteIrreducibleRadiusResponse.radius M hcrit g‖ + 1))
  have hδ : 0 < δ := lt_min hδN (div_pos heta (by positivity))
  refine ⟨δ, hδ, ?_⟩
  intro w hw hw1 hclose
  obtain ⟨V, hVlim, hVbounds, hVfix, -, hSeries⟩ :=
    M.fieldSeries_eq_least_fixedPoint gr τ hτ hρpos.ne' hτfix w hw hw1
  obtain ⟨W, hWlim, -, hWnorm⟩ := hNear w hw hw1 (hclose.trans_le (min_le_left _ _))
  have hVW : V = W := tendsto_nhds_unique hVlim hWlim
  have hVnorm : ‖V - τ‖ < eta := hVW ▸ hWnorm
  let U := TreeRealComplexBridge.complexify V
  let s := ell (U - FiniteIrreducibleRadiusResponse.profile M hcrit g)
  have hUτ : ‖U - FiniteIrreducibleRadiusResponse.profile M hcrit g‖ < eta := by
    rw [← hτc, ← TreeRealComplexBridge.complexify_sub]
    exact (TreeRealComplexBridge.norm_complexify_le (V - τ)).trans_lt hVnorm
  have hUone : ‖U - 1‖ < 2 * eta := by
    calc
      ‖U - 1‖ ≤ ‖U - FiniteIrreducibleRadiusResponse.profile M hcrit g‖ +
          ‖FiniteIrreducibleRadiusResponse.profile M hcrit g - 1‖ := by
            have hs : U - 1 = (U - FiniteIrreducibleRadiusResponse.profile M hcrit g) +
                (FiniteIrreducibleRadiusResponse.profile M hcrit g - 1) := by abel
            rw [hs]
            exact norm_add_le _ _
      _ < 2 * eta := by linarith
  have hsNorm : ‖s‖ < rChart :=
    (ell.le_opNorm _).trans_lt
      ((mul_le_mul_of_nonneg_left hUτ.le (norm_nonneg ell)).trans_lt hellEtaChart)
  have hwEta : |w - 1| < eta / (‖FiniteIrreducibleRadiusResponse.radius M hcrit g‖ + 1) :=
    hclose.trans_le (min_le_right _ _)
  have hwNorm : ‖(w : ℂ) - 1‖ = |w - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hzOne : ‖FiniteIrreducibleRadiusResponse.radius M hcrit g * (w : ℂ) - 1‖ < 2 * eta := by
    have hm : ‖FiniteIrreducibleRadiusResponse.radius M hcrit g‖ * |w - 1| < eta := by
      have hh := (lt_div_iff₀ (by positivity : 0 < ‖FiniteIrreducibleRadiusResponse.radius M hcrit g‖ + 1)).mp hwEta
      nlinarith [abs_nonneg (w - 1)]
    calc
      _ ≤ ‖FiniteIrreducibleRadiusResponse.radius M hcrit g * ((w : ℂ) - 1)‖ +
          ‖FiniteIrreducibleRadiusResponse.radius M hcrit g - 1‖ := by
        have hs : FiniteIrreducibleRadiusResponse.radius M hcrit g * (w : ℂ) - 1 =
            FiniteIrreducibleRadiusResponse.radius M hcrit g * ((w : ℂ) - 1) +
              (FiniteIrreducibleRadiusResponse.radius M hcrit g - 1) := by ring
        rw [hs]
        exact norm_add_le _ _
      _ < 2 * eta := by rw [norm_mul, hwNorm]; linarith
  have hpBall : ((g, FiniteIrreducibleRadiusResponse.radius M hcrit g * (w : ℂ)), U) ∈
      Metric.ball (((0 : C(S, ℂ)), (1 : ℂ)), (1 : C(S, ℂ))) rFold := by
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq]
    simp only [dist_eq_norm, sub_zero]
    exact max_lt (max_lt (hgnorm.trans_le (min_le_left _ _)) (hzOne.trans h2etaFold))
      (hUone.trans h2etaFold)
  have hTree : M.treeResidual ((FiniteIrreducibleRadiusResponse.radius M hcrit g * (w : ℂ), g), U) = 0 := by
    have he := congrArg TreeRealComplexBridge.complexify hVfix
    rw [M.complexify_fieldTreeMap, FiniteIrreducibleModel.complexify_realPartMap_of_star g hreal,
      Complex.ofReal_mul, hρc] at he
    exact sub_eq_zero.mpr he.symm
  have hFold := hFoldBall hpBall hTree
  have hChartArg : (g, s) ∈ Metric.ball ((0 : C(S, ℂ)), (0 : ℂ)) rChart := by
    rw [← ball_prod_same]
    exact ⟨by simpa only [Metric.mem_ball, dist_zero_right] using
      hgnorm.trans_le (min_le_right _ _), by simpa only [Metric.mem_ball, dist_zero_right] using hsNorm⟩
  obtain ⟨⟨hMatch, hDef⟩, hBRe⟩ := hChartBall hChartArg
  have hTx : T (g, -(s * B (g, s))) = U := by
    rw [hMatch]
    exact congrArg Prod.snd hFold
  have hxsq : (-(s * B (g, s))) ^ 2 = 1 - (w : ℂ) := by
    rw [neg_sq]
    have hradius := congrArg Prod.fst hFold
    rw [hradius] at hDef
    have hρne : FiniteIrreducibleRadiusResponse.radius M hcrit g ≠ 0 := by
      rw [← hρc]
      exact Complex.ofReal_ne_zero.mpr hρpos.ne'
    apply mul_left_cancel₀ hρne
    calc
      _ = FiniteIrreducibleRadiusResponse.radius M hcrit g -
          FiniteIrreducibleRadiusResponse.radius M hcrit g * (w : ℂ) := hDef
      _ = _ := by ring
  obtain ⟨r, hrneg, hsr⟩ := M.field_physical_perron_coordinate_negative hcrit gr τ hτ
    hρpos hw hw1 hτfix V (fun a ↦ (hVbounds a).2) hVfix
  have hsReal : s = (r : ℂ) := by
    change ell (U - FiniteIrreducibleRadiusResponse.profile M hcrit g) = _
    rw [← hτc]
    exact hsr
  have hXpos : 0 < (-(s * B (g, s))).re := by
    have hsrRe : s.re = r := congrArg Complex.re hsReal
    have hsrIm : s.im = 0 := congrArg Complex.im hsReal
    simp only [Complex.neg_re, Complex.mul_re, hsrRe, hsrIm, zero_mul, sub_zero]
    nlinarith [mul_neg_of_neg_of_pos hrneg hBRe]
  have hSqrtSq : ((Real.sqrt (1 - w) : ℂ)) ^ 2 = 1 - (w : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 - w),
      Complex.ofReal_sub, Complex.ofReal_one]
  have hproduct : (-(s * B (g, s)) - (Real.sqrt (1 - w) : ℂ)) *
      (-(s * B (g, s)) + (Real.sqrt (1 - w) : ℂ)) = 0 := by
    calc
      _ = (-(s * B (g, s))) ^ 2 - ((Real.sqrt (1 - w) : ℂ)) ^ 2 := by ring
      _ = 0 := by rw [hxsq, hSqrtSq, sub_self]
  have hXeq : -(s * B (g, s)) = (Real.sqrt (1 - w) : ℂ) := by
    rcases mul_eq_zero.mp hproduct with hminus | hplus
    · exact sub_eq_zero.mp hminus
    · have hxneg : -(s * B (g, s)) = -(Real.sqrt (1 - w) : ℂ) := by linear_combination hplus
      have he := congrArg Complex.re hxneg
      simp only [Complex.neg_re, Complex.ofReal_re] at he
      have hpX := hXpos
      simp only [Complex.neg_re] at hpX
      linarith [Real.sqrt_nonneg (1 - w)]
  refine ⟨V, hVlim, hVfix, ?_, ?_⟩
  · rw [← hXeq]
    exact hTx
  · rw [FiniteIrreducibleModel.complexify_realPartMap_of_star g hreal, hρc] at hSeries
    exact hSeries

/-- The actual zero-start branch exists on the whole real subcritical
interval, equals the genuine labelled sum, is least among all nonnegative
fixed points, and reaches the constructed critical profile at the endpoint. -/
theorem real_field_least_branch_eventually
    (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0, star g = g →
      Tendsto (M.fieldTreeIter (FiniteIrreducibleRadiusResponse.radius M hcrit g).re
        (FiniteIrreducibleModel.realPartMap g)) atTop
        (𝓝 (FiniteIrreducibleModel.realCriticalProfile M hcrit g)) ∧
      ∀ w : ℝ, 0 ≤ w → w < 1 →
        ∃ V : C(S, ℝ),
          Tendsto (M.fieldTreeIter ((FiniteIrreducibleRadiusResponse.radius M hcrit g).re * w)
            (FiniteIrreducibleModel.realPartMap g)) atTop (𝓝 V) ∧
          (∀ a, 0 ≤ V a ∧ V a ≤ FiniteIrreducibleModel.realCriticalProfile M hcrit g a) ∧
          M.fieldTreeMap ((FiniteIrreducibleRadiusResponse.radius M hcrit g).re * w)
            (FiniteIrreducibleModel.realPartMap g) V = V ∧
          (∀ W : C(S, ℝ), (∀ a, 0 ≤ W a) →
            M.fieldTreeMap ((FiniteIrreducibleRadiusResponse.radius M hcrit g).re * w)
              (FiniteIrreducibleModel.realPartMap g) W = W → ∀ a, V a ≤ W a) ∧
          (M.fieldFMS g).sum (FiniteIrreducibleRadiusResponse.radius M hcrit g * (w : ℂ)) =
            TreeRealComplexBridge.complexify V := by
  filter_upwards [M.real_critical_tilt_eventually hcrit] with g hg
  intro hreal
  obtain ⟨hτ, hρpos, hρim, -, hfix, hcritical⟩ := hg hreal
  refine ⟨M.fieldTreeIter_critical_converges_of_positive_profile _ _ hτ _ hfix hcritical, ?_⟩
  intro w hw hw1
  obtain ⟨V, hVlim, hVbounds, hVfix, hVleast, hseries⟩ :=
    M.fieldSeries_eq_least_fixedPoint (FiniteIrreducibleModel.realPartMap g)
      (FiniteIrreducibleModel.realCriticalProfile M hcrit g) hτ hρpos.ne' hfix w hw hw1
  have hρc : ((FiniteIrreducibleRadiusResponse.radius M hcrit g).re : ℂ) =
      FiniteIrreducibleRadiusResponse.radius M hcrit g := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hρim.symm
  rw [FiniteIrreducibleModel.complexify_realPartMap_of_star g hreal, hρc] at hseries
  exact ⟨V, hVlim, hVbounds, hVfix, hVleast, hseries⟩

/-- One explicit real-field ball supports both the exact genuine series
radius and the physical positive-square-root overlap with an actual joint
analytic chart. The activity overlap may shrink with the field. -/
theorem exists_real_field_radius_and_joint_physical_fold
    (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∃ (epsilon : ℝ) (T : C(S, ℂ) × ℂ → C(S, ℂ)),
      0 < epsilon ∧ AnalyticAt ℂ T (0, 0) ∧ T (0, 0) = 1 ∧
      deriv (fun X : ℂ ↦ T (0, X)) 0 =
        (-(FiniteIrreducibleFoldCoefficients.gamma M hcrit : ℂ)) • M.complexPerronFunction hcrit ∧
      (∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        M.treeResidual ((FiniteIrreducibleRadiusResponse.radius M hcrit q.1 * (1 - q.2 ^ 2), q.1),
          T q) = 0) ∧
      ∀ g : C(S, ℂ), ‖g‖ < epsilon → star g = g →
        (M.fieldFMS g).radius = ‖FiniteIrreducibleRadiusResponse.radius M hcrit g‖ₑ ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, 0 ≤ w → w < 1 → |w - 1| < δ →
          (M.fieldFMS g).sum (FiniteIrreducibleRadiusResponse.radius M hcrit g * (w : ℂ)) =
            T (g, (Real.sqrt (1 - w) : ℂ)) := by
  obtain ⟨T, hTa, hT0, hTd, -, hres, hphysical⟩ :=
    exists_joint_fold_identified_with_real_field_series M hcrit
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp
    ((M.fieldFMS_radius_eq_critical_radius_real_eventually hcrit).and hphysical)
  refine ⟨epsilon, T, hepsilon, hTa, hT0, hTd, hres, ?_⟩
  intro g hg hreal
  have hgood := hball (by simpa only [Metric.mem_ball, dist_zero_right] using hg)
  refine ⟨hgood.1 hreal, ?_⟩
  obtain ⟨δ, hδ, hmatch⟩ := hgood.2 hreal
  refine ⟨δ, hδ, ?_⟩
  intro w hw hw1 hclose
  obtain ⟨V, -, -, hT, hseries⟩ := hmatch w hw hw1 hclose
  exact hseries.trans hT.symm

end PerronWright.FiniteIrreducibleFieldPhysicalFold
