import PerronWright.Analysis.TreeFoldJointDivision

open scoped NNReal ENNReal
open Topology

noncomputable section

/-!
Banach-valued vertical analytic division.  This supplies the vector-valued
factorization needed to freeze a jointly analytic pole numerator on the
horizontal parameter slice.
-/

namespace PerronWright.AnalyticVerticalDivision

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

private def horiz : (E × ℂ) →L[ℂ] (E × ℂ) :=
  (ContinuousLinearMap.fst ℂ E ℂ).prod 0

private def v : E × ℂ := (0, 1)

private def slopeCoeff (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => E × ℂ) F) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => E × ℂ) F :=
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

omit [CompleteSpace F] in
private theorem norm_slopeCoeff_le (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => E × ℂ) F) :
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

omit [CompleteSpace F] in
private theorem homogeneous_vertical_difference (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => E × ℂ) F)
    (x : E × ℂ) :
    p (fun _ => x) - p (fun _ => horiz x) =
      x.2 • ∑ i : Fin n,
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
  rw [h', Finset.smul_sum]
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

omit [CompleteSpace F] in
private theorem slopeCoeff_apply (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => E × ℂ) F)
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

omit [CompleteSpace F] in
private theorem homogeneous_vertical_factor (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => E × ℂ) F)
    (x : E × ℂ) :
    p (fun _ => x) - p (fun _ => horiz x) =
      x.2 • slopeCoeff n p (fun _ => x) := by
  rw [homogeneous_vertical_difference, slopeCoeff_apply]

private def verticalSlopeSeries
    (p : FormalMultilinearSeries ℂ (E × ℂ) F) :
    FormalMultilinearSeries ℂ (E × ℂ) F :=
  fun n => slopeCoeff n (p (n + 1))

omit [CompleteSpace F] in
private theorem verticalSlopeSeries_radius_pos
    (p : FormalMultilinearSeries ℂ (E × ℂ) F) (hp : 0 < p.radius) :
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
    (p : FormalMultilinearSeries ℂ (E × ℂ) F) (x : E × ℂ)
    (hx : x ∈ Metric.eball 0 p.radius)
    (hBx : horiz x ∈ Metric.eball 0 p.radius)
    (hqx : x ∈ Metric.eball 0 (verticalSlopeSeries p).radius) :
    p.sum x - p.sum (horiz x) = x.2 • (verticalSlopeSeries p).sum x := by
  let a : ℕ → F := fun n => p n (fun _ => x)
  let b : ℕ → F := fun n => p n (fun _ => horiz x)
  let c : ℕ → F := fun n => verticalSlopeSeries p n (fun _ => x)
  have ha : Summable a := p.summable hx
  have hb : Summable b := p.summable hBx
  have hc : Summable c := (verticalSlopeSeries p).summable hqx
  have hzero : a 0 - b 0 = 0 := by
    have harg : (fun _ : Fin 0 => x) = (fun _ : Fin 0 => horiz x) :=
      Subsingleton.elim _ _
    simp only [a, b, harg, sub_self]
  have hshift (n : ℕ) : a (n + 1) - b (n + 1) = x.2 • c n :=
    homogeneous_vertical_factor n (p (n + 1)) x
  change (∑' n, a n) - (∑' n, b n) = x.2 • ∑' n, c n
  rw [← ha.tsum_sub hb]
  have hd : Summable (fun n => a n - b n) := ha.sub hb
  rw [hd.tsum_eq_zero_add, hzero, zero_add]
  simp_rw [hshift]
  exact hc.tsum_const_smul x.2

/-- Banach-valued analytic division by the vertical coordinate, with no vanishing
assumption: subtract the restriction to the horizontal slice first. -/
theorem analytic_vertical_difference_division {f : E × ℂ → F}
    (hf : AnalyticAt ℂ f (0, 0)) :
    ∃ Q : E × ℂ → F, AnalyticAt ℂ Q (0, 0) ∧
      ∀ᶠ x : E × ℂ in 𝓝 (0, 0),
        f x - f (x.1, 0) = x.2 • Q x := by
  obtain ⟨p, r, hfp⟩ := hf
  let q := verticalSlopeSeries p
  have hqp : 0 < q.radius :=
    verticalSlopeSeries_radius_pos p (lt_of_lt_of_le hfp.r_pos hfp.r_le)
  let Q : E × ℂ → F := q.sum
  have hQa : AnalyticAt ℂ Q (0, 0) := (q.hasFPowerSeriesOnBall hqp).analyticAt
  refine ⟨Q, hQa, ?_⟩
  have hball : Metric.eball (0 : E × ℂ) r ∈ 𝓝 (0, 0) :=
    Metric.eball_mem_nhds _ hfp.r_pos
  have hqball : Metric.eball (0 : E × ℂ) q.radius ∈ 𝓝 (0, 0) :=
    Metric.eball_mem_nhds _ hqp
  filter_upwards [hball, hqball] with x hx hqx
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
  have hfbase : f (x.1, 0) = p.sum (horiz x) := by
    simpa [horiz] using hfBx
  rw [hfx, hfbase]
  exact verticalSlopeSeries_sum_identity p x hpx hpBx hqx

/-- Banach-valued analytic division by the vertical coordinate, under local
vanishing on the horizontal slice. -/
theorem analytic_vertical_division_smul {f : E × ℂ → F}
    (hf : AnalyticAt ℂ f (0, 0))
    (hzero : ∀ᶠ g : E in 𝓝 0, f (g, 0) = 0) :
    ∃ Q : E × ℂ → F, AnalyticAt ℂ Q (0, 0) ∧
      ∀ᶠ x : E × ℂ in 𝓝 (0, 0), f x = x.2 • Q x := by
  obtain ⟨Q, hQa, hfactor⟩ := analytic_vertical_difference_division hf
  refine ⟨Q, hQa, ?_⟩
  have hzero' : ∀ᶠ x : E × ℂ in 𝓝 (0, 0), f (x.1, 0) = 0 := by
    have hfst : Filter.Tendsto (fun x : E × ℂ => x.1) (𝓝 (0, 0)) (𝓝 0) :=
      continuousAt_fst.tendsto
    exact hfst.eventually hzero
  filter_upwards [hfactor, hzero'] with x hx hz
  simpa [hz] using hx

end PerronWright.AnalyticVerticalDivision
