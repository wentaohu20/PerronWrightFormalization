import PerronWright.Probability.BrownianPalmTimeDepthElimination

/-! # Literal anchor-time and completed-length Tonelli exchange

The start time is nonnegative, but neither the source measure nor the
nonnegative kernel needs to be finite. The actual moving window is reduced
to its Lebesgue length; no Palm or excursion-law identity is assumed.
-/

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedExcursionAnchorTimeExchange

open BrownianPalmTimeDepthElimination

variable {Z : Type*} [MeasurableSpace Z]

private theorem tail_eq_positive_window (s : ℝ≥0) (F : ℝ → ℝ≥0∞) (t : ℝ) :
    (if (s : ℝ) < t then ∫⁻ l in Ioi (t-(s : ℝ)), F l else 0) =
      ∫⁻ l in Ioi (0 : ℝ),
        if (s : ℝ) < t ∧ t < (s : ℝ)+(Real.toNNReal l : ℝ) then F l else 0 := by
  by_cases ht : (s : ℝ) < t
  · rw [if_pos ht,← lintegral_indicator measurableSet_Ioi,
      ← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro l
    simp only [indicator_apply,mem_Ioi]
    by_cases hl : 0 < l
    · rw [if_pos hl,Real.coe_toNNReal _ hl.le]
      have he : t-(s : ℝ) < l ↔ t < (s : ℝ)+l := by constructor <;> intro h <;> linarith
      simp only [ht,true_and,he]
    · have hn : ¬t-(s : ℝ) < l := by linarith
      simp only [if_neg hl,if_neg hn]
  · rw [if_neg ht]
    symm
    simpa only [ht,false_and,if_false] using
      (lintegral_zero : (∫⁻ l in Ioi (0 : ℝ), (0 : ℝ≥0∞)) = 0)

theorem measurable_joint_anchorKernel (s : Z → ℝ≥0) (K : Z × ℝ → ℝ≥0∞)
    (hs : Measurable s) (hK : Measurable K) :
    Measurable (fun q : ℝ × Z ↦
      if (s q.2 : ℝ) < q.1 then ∫⁻ l in Ioi (q.1-(s q.2 : ℝ)), K (q.2,l) else 0) := by
  have hm : Measurable (fun q : (ℝ × Z) × ℝ ↦
      if (s q.1.2 : ℝ) < q.1.1 ∧ q.1.1 < (s q.1.2 : ℝ)+(Real.toNNReal q.2 : ℝ)
        then K (q.1.2,q.2) else 0) := by
    have hstart : Measurable (fun q : (ℝ × Z) × ℝ ↦ (s q.1.2 : ℝ)) :=
      ((hs.comp measurable_snd).comp measurable_fst).coe_nnreal_real
    have ht : Measurable (fun q : (ℝ × Z) × ℝ ↦ q.1.1) := measurable_fst.comp measurable_fst
    have hl : Measurable (fun q : (ℝ × Z) × ℝ ↦ (Real.toNNReal q.2 : ℝ)) :=
      measurable_snd.real_toNNReal.coe_nnreal_real
    exact (hK.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).ite
      ((measurableSet_lt hstart ht).inter (measurableSet_lt ht (hstart.add hl))) measurable_const
  have hi := hm.lintegral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))
  convert hi using 1
  funext q
  exact tail_eq_positive_window (s q.2) (fun l ↦ K (q.2,l)) q.1

theorem anchor_time_lintegral (μ : Measure Z) [SFinite μ]
    (s : Z → ℝ≥0) (K : Z × ℝ → ℝ≥0∞) (hs : Measurable s) (hK : Measurable K) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ z,
      if (s z : ℝ) < t then ∫⁻ l in Ioi (t-(s z : ℝ)), K (z,l) else 0 ∂μ) =
      ∫⁻ z, (∫⁻ l : ℝ in Ioi (0 : ℝ), ENNReal.ofReal l * K (z,l)) ∂μ := by
  let ν : Measure (Z × ℝ) := μ.prod (volume.restrict (Ioi (0 : ℝ)))
  let start : Z × ℝ → ℝ≥0 := fun q ↦ s q.1
  let length : Z × ℝ → ℝ≥0 := fun q ↦ Real.toNNReal q.2
  have hstart : Measurable start := hs.comp measurable_fst
  have hlength : Measurable length := measurable_snd.real_toNNReal
  have hwindow := measurable_joint_timeWindow start length K hstart hlength hK
  have hwindow_t (t : ℝ) : Measurable (timeWindow start length K t) :=
    hwindow.comp (measurable_const.prodMk measurable_id)
  have hinner (t : ℝ) :
      (∫⁻ z, if (s z : ℝ) < t then ∫⁻ l in Ioi (t-(s z : ℝ)), K (z,l) else 0 ∂μ) =
        ∫⁻ q, timeWindow start length K t q ∂ν := by
    rw [lintegral_prod _ (hwindow_t t).aemeasurable]
    apply lintegral_congr
    intro z
    exact tail_eq_positive_window (s z) (fun l ↦ K (z,l)) t
  have hout (t : ℝ) (ht : t ∉ Ioi (0 : ℝ)) :
      (∫⁻ q, timeWindow start length K t q ∂ν) = 0 := by
    have hneg : t ≤ 0 := le_of_not_gt ht
    have he : (fun q ↦ timeWindow start length K t q) = fun _ ↦ (0 : ℝ≥0∞) := by
      funext q
      have hn : ¬(start q : ℝ) < t := by have h := (start q).coe_nonneg; linarith
      simp only [timeWindow,hn,false_and,if_false]
    rw [he,lintegral_zero]
  simp_rw [hinner]
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ q, timeWindow start length K t q ∂ν := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem ht]
      · rw [indicator_of_notMem ht,hout t ht]
    _ = ∫⁻ q, (length q : ℝ≥0∞)*K q ∂ν :=
      timeWindow_source_lintegral ν start length K hstart hlength hK
    _ = _ := by
      change (∫⁻ q : Z × ℝ, (length q : ℝ≥0∞)*K q
        ∂μ.prod (volume.restrict (Ioi (0 : ℝ)))) = _
      rw [lintegral_prod (fun q : Z × ℝ ↦ (length q : ℝ≥0∞)*K q)
        (hlength.coe_nnreal_ennreal.mul hK).aemeasurable]
      apply lintegral_congr
      intro z
      apply lintegral_congr
      intro l
      rfl

theorem anchor_time_inverse_length_lintegral (μ : Measure Z) [SFinite μ]
    (s : Z → ℝ≥0) (K : Z × ℝ → ℝ≥0∞) (hs : Measurable s) (hK : Measurable K) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ z,
      if (s z : ℝ) < t then ∫⁻ l in Ioi (t-(s z : ℝ)), K (z,l)/ENNReal.ofReal l else 0 ∂μ) =
      ∫⁻ z, (∫⁻ l : ℝ in Ioi (0 : ℝ), K (z,l)) ∂μ := by
  have hdiv : Measurable (fun q : Z × ℝ ↦ K q/ENNReal.ofReal q.2) :=
    hK.div measurable_snd.ennreal_ofReal
  rw [anchor_time_lintegral μ s _ hs hdiv]
  apply lintegral_congr
  intro z
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
  have hp : ENNReal.ofReal l ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hl)
  rw [div_eq_mul_inv,mul_comm (K (z,l)),← mul_assoc,
    ENNReal.mul_inv_cancel hp ENNReal.ofReal_ne_top,one_mul]

end PerronWright.BrownianCompletedExcursionAnchorTimeExchange
