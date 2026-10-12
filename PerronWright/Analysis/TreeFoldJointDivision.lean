import PerronWright.Analysis.TreeFoldUniformCurvature

open scoped NNReal ENNReal
open Topology

noncomputable section

namespace PerronWright.TreeFoldJointDivision

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private def horiz : (E × ℂ) →L[ℂ] (E × ℂ) :=
  (ContinuousLinearMap.fst ℂ E ℂ).prod 0

private def v : E × ℂ := (0, 1)

private def slopeCoeff (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => E × ℂ) ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => E × ℂ) ℂ :=
  ∑ i : Fin (n + 1),
    (p.curryMid i v).compContinuousLinearMap
      (fun j => if i.succAbove j < i then ContinuousLinearMap.id ℂ (E × ℂ) else horiz)

private theorem horiz_norm_le_one : ‖(horiz : E × ℂ →L[ℂ] E × ℂ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(x.1, (0 : ℂ))‖ ≤ 1 * ‖x‖
  simp only [one_mul, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  exact le_max_left _ _

omit [NormedSpace ℂ E] in
private theorem norm_v : ‖(v : E × ℂ)‖ = 1 := by
  simp [v, Prod.norm_def]

private theorem norm_slopeCoeff_le (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => E × ℂ) ℂ) :
    ‖slopeCoeff n p‖ ≤ (n + 1 : ℝ) * ‖p‖ := by
  classical
  unfold slopeCoeff
  calc
    ‖∑ i : Fin (n + 1),
        (p.curryMid i v).compContinuousLinearMap
          (fun j => if i.succAbove j < i then ContinuousLinearMap.id ℂ (E × ℂ) else horiz)‖
      ≤ ∑ i : Fin (n + 1),
          ‖(p.curryMid i v).compContinuousLinearMap
            (fun j => if i.succAbove j < i then ContinuousLinearMap.id ℂ (E × ℂ) else horiz)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin (n + 1), ‖p‖ := by
      apply Finset.sum_le_sum
      intro i hi
      let L : Fin n → (E × ℂ) →L[ℂ] (E × ℂ) :=
        fun j => if i.succAbove j < i then ContinuousLinearMap.id ℂ (E × ℂ) else horiz
      have hL (j : Fin n) : ‖L j‖ ≤ 1 := by
        dsimp [L]
        split_ifs
        · exact ContinuousLinearMap.norm_id_le
        · exact horiz_norm_le_one
      have hprod : (∏ j : Fin n, ‖L j‖) ≤ 1 := by
        simpa using Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => hL j)
      have hmid : ‖p.curryMid i v‖ ≤ ‖p‖ := by
        calc
          ‖p.curryMid i v‖ ≤ ‖p.curryMid i‖ * ‖v‖ := (p.curryMid i).le_opNorm v
          _ = ‖p‖ := by rw [ContinuousMultilinearMap.norm_curryMid, norm_v, mul_one]
      calc
        ‖(p.curryMid i v).compContinuousLinearMap L‖
            ≤ ‖p.curryMid i v‖ * ∏ j, ‖L j‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ ‖p‖ := by nlinarith [norm_nonneg p, norm_nonneg (p.curryMid i v)]
    _ = (n + 1 : ℝ) * ‖p‖ := by simp

private theorem homogeneous_vertical_difference (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => E × ℂ) ℂ)
    (x : E × ℂ) :
    p (fun _ => x) - p (fun _ => horiz x) =
      x.2 * ∑ i : Fin n,
        p (fun j => if j < i then x else if j = i then v else horiz x) := by
  classical
  have h := p.toMultilinearMap.map_sub_map_piecewise
    (fun _ : Fin n => x) (fun _ : Fin n => horiz x) Finset.univ
  simp only [Finset.piecewise_univ, Finset.mem_univ, forall_const] at h
  change p (fun _ => x) - p (fun _ => horiz x) =
    ∑ i : Fin n,
      p (fun j => if j < i then x else if i = j then x - horiz x else horiz x) at h
  have h' : p (fun _ => x) - p (fun _ => horiz x) =
      ∑ i : Fin n,
        p (fun j => if j < i then x else if j = i then x - horiz x else horiz x) := by
    simpa only [eq_comm] using h
  rw [h', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let m : Fin n → E × ℂ := fun j => if j < i then x else horiz x
  have hterm :
      (fun j : Fin n => if j < i then x else if j = i then x - horiz x else horiz x) =
      Function.update m i (x - horiz x) := by
    funext j
    by_cases hj : j < i
    · simp [m, ne_of_lt hj]
    · by_cases hji : j = i
      · subst j
        simp [m]
      · simp [m, hj, hji]
  have hx : x - horiz x = x.2 • v := by
    ext <;> simp [horiz, v]
  rw [hterm, hx, p.map_update_smul]
  congr 1
  apply congrArg p
  funext j
  by_cases hj : j < i
  · simp [m, ne_of_lt hj]
  · by_cases hji : j = i
    · subst j
      simp [m]
    · simp [m, hj, hji]

private theorem slopeCoeff_apply (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => E × ℂ) ℂ)
    (x : E × ℂ) :
    slopeCoeff n p (fun _ => x) =
      ∑ i : Fin (n + 1),
        p (fun j => if j < i then x else if j = i then v else horiz x) := by
  classical
  unfold slopeCoeff
  simp only [sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.curryMid_apply]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · simp [v]
  · funext j
    simp only [Fin.removeNth, Fin.succAbove_ne]
    by_cases hj : i.succAbove j < i
    · simp [hj]
    · simp [hj, horiz]

private theorem homogeneous_vertical_factor (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => E × ℂ) ℂ)
    (x : E × ℂ) :
    p (fun _ => x) - p (fun _ => horiz x) =
      x.2 * slopeCoeff n p (fun _ => x) := by
  rw [homogeneous_vertical_difference, slopeCoeff_apply]

private def verticalSlopeSeries
    (p : FormalMultilinearSeries ℂ (E × ℂ) ℂ) :
    FormalMultilinearSeries ℂ (E × ℂ) ℂ :=
  fun n => slopeCoeff n (p (n + 1))

private theorem verticalSlopeSeries_radius_pos
    (p : FormalMultilinearSeries ℂ (E × ℂ) ℂ) (hp : 0 < p.radius) :
    0 < (verticalSlopeSeries p).radius := by
  obtain ⟨C, R, hC, hR, hbound⟩ := p.le_mul_pow_of_radius_pos hp
  let r : ℝ≥0 := ⟨1 / (2 * R), le_of_lt (one_div_pos.mpr (mul_pos (by norm_num) hR))⟩
  have hr : 0 < r := one_div_pos.mpr (mul_pos (by norm_num) hR)
  have hC0 : 0 ≤ C * R := le_of_lt (mul_pos hC hR)
  have hrad : (r : ℝ≥0∞) ≤ (verticalSlopeSeries p).radius := by
    apply FormalMultilinearSeries.le_radius_of_bound _ (C * R)
    intro n
    have hnat : (n + 1 : ℝ) ≤ 2 ^ n := by
      exact_mod_cast (by simpa using Nat.choose_succ_le_two_pow n 1)
    have hterm : ‖verticalSlopeSeries p n‖ ≤ C * R * (2 * R) ^ n := by
      calc
        ‖verticalSlopeSeries p n‖ ≤ (n + 1 : ℝ) * ‖p (n + 1)‖ :=
          norm_slopeCoeff_le n (p (n + 1))
        _ ≤ (n + 1 : ℝ) * (C * R ^ (n + 1)) := by gcongr; exact hbound (n + 1)
        _ ≤ 2 ^ n * (C * R ^ (n + 1)) := by gcongr
        _ = C * R * (2 * R) ^ n := by ring
    calc
      ‖verticalSlopeSeries p n‖ * (r : ℝ) ^ n ≤
          (C * R * (2 * R) ^ n) * (r : ℝ) ^ n := by gcongr
      _ = C * R := by
        have htwoR : 2 * R ≠ 0 := ne_of_gt (mul_pos (by norm_num) hR)
        change C * R * (2 * R) ^ n * (1 / (2 * R)) ^ n = C * R
        have hone : (2 * R) * (1 / (2 * R)) = 1 := by field_simp
        rw [mul_assoc, ← mul_pow, hone, one_pow, mul_one]
  exact lt_of_lt_of_le (by exact_mod_cast hr) hrad

private theorem verticalSlopeSeries_sum_identity
    (p : FormalMultilinearSeries ℂ (E × ℂ) ℂ) (x : E × ℂ)
    (hx : x ∈ Metric.eball 0 p.radius)
    (hBx : horiz x ∈ Metric.eball 0 p.radius)
    (hqx : x ∈ Metric.eball 0 (verticalSlopeSeries p).radius) :
    p.sum x - p.sum (horiz x) = x.2 * (verticalSlopeSeries p).sum x := by
  let a : ℕ → ℂ := fun n => p n (fun _ => x)
  let b : ℕ → ℂ := fun n => p n (fun _ => horiz x)
  let c : ℕ → ℂ := fun n => verticalSlopeSeries p n (fun _ => x)
  have ha : Summable a := p.summable hx
  have hb : Summable b := p.summable hBx
  have hc : Summable c := (verticalSlopeSeries p).summable hqx
  have hzero : a 0 - b 0 = 0 := by
    have harg : (fun _ : Fin 0 => x) = (fun _ : Fin 0 => horiz x) :=
      Subsingleton.elim _ _
    simp only [a, b, harg, sub_self]
  have hshift (n : ℕ) : a (n + 1) - b (n + 1) = x.2 * c n :=
    homogeneous_vertical_factor n (p (n + 1)) x
  change (∑' n, a n) - (∑' n, b n) = x.2 * ∑' n, c n
  rw [← ha.tsum_sub hb]
  have hd : Summable (fun n => a n - b n) := ha.sub hb
  rw [hd.tsum_eq_zero_add, hzero, zero_add]
  simp_rw [hshift]
  exact hc.tsum_mul_left x.2

theorem analytic_vertical_division {f : E × ℂ → ℂ}
    (hf : AnalyticAt ℂ f (0, 0))
    (hzero : ∀ᶠ g : E in 𝓝 0, f (g, 0) = 0) :
    ∃ Q : E × ℂ → ℂ, AnalyticAt ℂ Q (0, 0) ∧
      ∀ᶠ x : E × ℂ in 𝓝 (0, 0), f x = x.2 * Q x := by
  obtain ⟨p, r, hfp⟩ := hf
  let q := verticalSlopeSeries p
  have hqp : 0 < q.radius :=
    verticalSlopeSeries_radius_pos p (lt_of_lt_of_le hfp.r_pos hfp.r_le)
  let Q : E × ℂ → ℂ := q.sum
  have hQa : AnalyticAt ℂ Q (0, 0) := (q.hasFPowerSeriesOnBall hqp).analyticAt
  refine ⟨Q, hQa, ?_⟩
  have hball : Metric.eball (0 : E × ℂ) r ∈ 𝓝 (0, 0) :=
    Metric.eball_mem_nhds _ hfp.r_pos
  have hqball : Metric.eball (0 : E × ℂ) q.radius ∈ 𝓝 (0, 0) :=
    Metric.eball_mem_nhds _ hqp
  have hzero' : ∀ᶠ x : E × ℂ in 𝓝 (0, 0), f (horiz x) = 0 := by
    have hfst : Filter.Tendsto (fun x : E × ℂ => x.1) (𝓝 (0, 0)) (𝓝 0) :=
      continuousAt_fst.tendsto
    filter_upwards [hfst.eventually hzero] with x hx
    simpa [horiz] using hx
  filter_upwards [hball, hqball, hzero'] with x hx hqx hz
  have hnorm : ‖horiz x‖ ≤ ‖x‖ := by
    calc
      ‖horiz x‖ ≤ ‖(horiz : E × ℂ →L[ℂ] E × ℂ)‖ * ‖x‖ :=
        (horiz : E × ℂ →L[ℂ] E × ℂ).le_opNorm x
      _ ≤ 1 * ‖x‖ := by gcongr; exact horiz_norm_le_one
      _ = ‖x‖ := one_mul _
  have hBx : horiz x ∈ Metric.eball (0 : E × ℂ) r := by
    rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero] at hx ⊢
    exact lt_of_le_of_lt (enorm_le_iff_norm_le.mpr hnorm) hx
  have hpx : x ∈ Metric.eball (0 : E × ℂ) p.radius :=
    lt_of_lt_of_le hx hfp.r_le
  have hpBx : horiz x ∈ Metric.eball (0 : E × ℂ) p.radius :=
    lt_of_lt_of_le hBx hfp.r_le
  have hfx : f x = p.sum x := by
    simpa only [show ((0 : E), (0 : ℂ)) = (0 : E × ℂ) by rfl, zero_add] using hfp.sum hx
  have hfBx : f (horiz x) = p.sum (horiz x) := by
    simpa only [show ((0 : E), (0 : ℂ)) = (0 : E × ℂ) by rfl, zero_add] using
      hfp.sum hBx
  have hidentity := verticalSlopeSeries_sum_identity p x hpx hpBx hqx
  change f x = x.2 * Q x
  rw [hfx]
  calc
    p.sum x = p.sum x - p.sum (horiz x) := by rw [← hfBx, hz, sub_zero]
    _ = x.2 * Q x := hidentity

theorem analytic_vertical_second_division {f : E × ℂ → ℂ}
    (hf : AnalyticAt ℂ f (0, 0))
    (hzero : ∀ᶠ g : E in 𝓝 0, f (g, 0) = 0)
    (hderiv : ∀ᶠ g : E in 𝓝 0,
      deriv (fun t : ℂ => f (g, t)) 0 = 0) :
    ∃ H : E × ℂ → ℂ, AnalyticAt ℂ H (0, 0) ∧
      ∀ᶠ x : E × ℂ in 𝓝 (0, 0), f x = x.2 ^ 2 * H x := by
  obtain ⟨Q, hQa, hfactor⟩ := analytic_vertical_division hf hzero
  let emb : E → E × ℂ := fun g => (g, 0)
  have hemb : Filter.Tendsto emb (𝓝 0) (𝓝 (0, 0)) := by
    exact ((continuousAt_id : ContinuousAt (fun g : E => g) 0).prodMk
      continuousAt_const).tendsto
  have hQaNear : ∀ᶠ x : E × ℂ in 𝓝 (0, 0), AnalyticAt ℂ Q x :=
    hQa.eventually_analyticAt
  have hzeroQ : ∀ᶠ g : E in 𝓝 0, Q (g, 0) = 0 := by
    filter_upwards [hderiv, hemb.eventually hfactor.eventually_nhds,
      hemb.eventually hQaNear] with g hg hfactor_g hQa_g
    have hembg : Filter.Tendsto (fun t : ℂ => (g, t)) (𝓝 0) (𝓝 (g, 0)) := by
      exact (continuousAt_const.prodMk
        (continuousAt_id : ContinuousAt (fun t : ℂ => t) 0)).tendsto
    have hslice : (fun t : ℂ => f (g, t)) =ᶠ[𝓝 0]
        (fun t : ℂ => t * Q (g, t)) := by
      filter_upwards [hembg.eventually hfactor_g] with t ht
      simpa using ht
    have hQslice : AnalyticAt ℂ (fun t : ℂ => Q (g, t)) 0 :=
      (show AnalyticAt ℂ Q (g, 0) from hQa_g).comp
        (analyticAt_const.prod analyticAt_id)
    have hprod : HasDerivAt (fun t : ℂ => t * Q (g, t)) (Q (g, 0)) 0 := by
      have h := (hasDerivAt_id (0 : ℂ)).mul hQslice.differentiableAt.hasDerivAt
      have heq : (id * fun t : ℂ => Q (g, t)) = (fun t => t * Q (g, t)) := by
        rfl
      simpa only [heq, id_eq, one_mul, zero_mul, add_zero] using h
    have heq := hslice.deriv_eq
    rw [hprod.deriv] at heq
    exact heq.symm.trans hg
  obtain ⟨H, hHa, hQfactor⟩ := analytic_vertical_division hQa hzeroQ
  refine ⟨H, hHa, ?_⟩
  filter_upwards [hfactor, hQfactor] with x hfx hQx
  rw [hfx, hQx]
  ring

end PerronWright.TreeFoldJointDivision

namespace PerronWright.TreeFoldJointDivision

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem centered_radius_joint_quadratic_factor (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃ H : C(S, ℂ) × ℂ → ℂ, AnalyticAt ℂ H (0, 0) ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        RadiusResponse.radius M hM q.1 -
          (TreeFold.centeredFoldCurve M hM q).1 = q.2 ^ 2 * H q := by
  let f : C(S, ℂ) × ℂ → ℂ := fun q =>
    RadiusResponse.radius M hM q.1 -
      (TreeFold.centeredFoldCurve M hM q).1
  have hfa : AnalyticAt ℂ f (0, 0) := by
    have hfst : AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ => q.1) (0, 0) :=
      analyticAt_fst
    exact ((RadiusResponse.radius_analytic M hM).comp_of_eq hfst rfl).sub
      (analyticAt_fst.comp (TreeFold.centeredFoldCurve_analytic M hM))
  have hf0 : ∀ᶠ g : C(S, ℂ) in 𝓝 0, f (g, 0) = 0 := by
    filter_upwards [TreeFold.centeredFoldCurve_critical M hM] with g hg
    change RadiusResponse.radius M hM g -
      (TreeFold.centeredFoldCurve M hM (g, 0)).1 = 0
    rw [hg]
    simp [RadiusResponse.radius]
  have hfd : ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      deriv (fun t : ℂ => f (g, t)) 0 = 0 := by
    filter_upwards [TreeFoldUniformField.centered_radius_deriv_zero M hM] with g hg
    change deriv (fun t : ℂ => RadiusResponse.radius M hM g -
      (TreeFold.centeredFoldCurve M hM (g, t)).1) 0 = 0
    rw [deriv_const_sub]
    simp [hg]
  exact PerronWright.TreeFoldJointDivision.analytic_vertical_second_division hfa hf0 hfd

theorem centered_radius_joint_quadratic_factor_base (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃ H : C(S, ℂ) × ℂ → ℂ, AnalyticAt ℂ H (0, 0) ∧
      H (0, 0) = (M.beta hM : ℂ) / 2 ∧
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        RadiusResponse.radius M hM q.1 -
          (TreeFold.centeredFoldCurve M hM q).1 = q.2 ^ 2 * H q := by
  obtain ⟨H, hHa, hfactor⟩ := centered_radius_joint_quadratic_factor M hM
  obtain ⟨K, hKa, hKbase, hKfactor⟩ :=
    (TreeFoldUniformField.centered_radius_pointwise_quadratic_factor M hM).self_of_nhds
  have hsection : Filter.Tendsto (fun t : ℂ => ((0 : C(S, ℂ)), t))
      (𝓝 0) (𝓝 (0, 0)) :=
    (analyticAt_const.prod analyticAt_id : AnalyticAt ℂ
      (fun t : ℂ => ((0 : C(S, ℂ)), t)) 0).continuousAt.tendsto
  have hslice : ∀ᶠ t : ℂ in 𝓝 0,
      RadiusResponse.radius M hM 0 -
        (TreeFold.centeredFoldCurve M hM (0, t)).1 = t ^ 2 * H (0, t) := by
    simpa using hsection.eventually hfactor
  have hHK : ∀ᶠ t : ℂ in 𝓝[≠] 0, H (0, t) = K t := by
    filter_upwards [hslice.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht ht0
    have hmul : t ^ 2 * H (0, t) = t ^ 2 * K t := ht.symm.trans (hKfactor t)
    exact (mul_left_cancel₀ (pow_ne_zero 2 ht0) hmul)
  have hHslice : AnalyticAt ℂ (fun t : ℂ => H (0, t)) 0 :=
    hHa.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hHatK : H (0, 0) = K 0 :=
    tendsto_nhds_unique_of_eventuallyEq
      (hHslice.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hKa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hHK
  have hcurv : deriv (deriv (fun t : ℂ =>
      (TreeFold.centeredFoldCurve M hM (0, t)).1)) 0 =
      -(M.beta hM : ℂ) := by
    have hsame : (fun t : ℂ => (TreeFold.centeredFoldCurve M hM (0, t)).1) =
        TreeFoldCurvature.radiusSlice M hM := by
      funext t
      simp [TreeFold.centeredFoldCurve, TreeFold.criticalCoordinate_base,
        TreeFoldCurvature.radiusSlice]
    rw [hsame]
    exact TreeFoldCurvature.radiusSlice_second_deriv M hM
  refine ⟨H, hHa, ?_, hfactor⟩
  rw [hHatK, hKbase, hcurv]
  ring

end PerronWright.TreeFoldJointDivision



