import PerronWright.Probability.BrownianCompletedExcursionAnchorTimeExchange
import PerronWright.Probability.BrownianParabolicPassageStoppedTiltParameterMixture

/-! # Actual parabolic passage source: eliminating the anchor time

The depth-dependent source is the literal stopped parabolic driver law.
The moving positive-time window and inverse length are removed by the
proved Lebesgue/Tonelli identity, not by an assumed Palm identity.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianActualPassageAnchorExchange

open BrownianPathLaw BrownianParabolicFirstPassageStoppedTiltFull
open BrownianParabolicPassageStoppedTiltParameterMixture
open BrownianCompletedExcursionAnchorTimeExchange

private theorem actual_depth_source_lintegral (lambda : ℝ)
    (Φ : ℝ × (ℝ≥0 × Path) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ a : ℝ in Ioi 0, ∫⁻ p : ℝ≥0 × Path, Φ (a,p)
      ∂pathLaw.map (actualDriverPassagePast lambda (-a))) =
      ∫⁻ z : ℝ × Path, Φ (parameterDriverPassagePast
        (fun _ : ℝ ↦ lambda) (fun a : ℝ ↦ -a) z)
        ∂(volume.restrict (Ioi (0 : ℝ))).prod pathLaw := by
  have hQ := measurable_parameterDriverPassagePast
    (lambda := fun _ : ℝ ↦ lambda) (level := fun a : ℝ ↦ -a)
    measurable_const measurable_id.neg
  rw [lintegral_prod (fun z : ℝ × Path ↦ Φ (parameterDriverPassagePast
    (fun _ : ℝ ↦ lambda) (fun a : ℝ ↦ -a) z)) (hΦ.comp hQ).aemeasurable]
  apply lintegral_congr
  intro a
  have hm : Measurable (fun p : ℝ≥0 × Path ↦ Φ (a,p)) :=
    hΦ.comp (measurable_const.prodMk measurable_id)
  exact lintegral_map hm (measurable_actualDriverPassagePast lambda (-a))

private theorem real_anchor_eq_nn_anchor (s : ℝ≥0) (F : ℝ → ℝ≥0∞)
    (t : ℝ) (ht : 0 ≤ t) :
    (if (s : ℝ) < t then ∫⁻ l in Ioi (t-(s : ℝ)), F l else 0) =
      if s < Real.toNNReal t then
        ∫⁻ l in Ioi ((Real.toNNReal t-s : ℝ≥0) : ℝ), F l else 0 := by
  have he : s < Real.toNNReal t ↔ (s : ℝ) < t := by
    rw [← NNReal.coe_lt_coe,Real.coe_toNNReal t ht]
  by_cases h : s < Real.toNNReal t
  · rw [if_pos h,if_pos (he.mp h),NNReal.coe_sub h.le,Real.coe_toNNReal t ht]
  · rw [if_neg h,if_neg (mt he.mpr h)]

theorem actual_passage_anchor_inverse_length_lintegral (lambda : ℝ)
    (K : (ℝ × (ℝ≥0 × Path)) × ℝ → ℝ≥0∞) (hK : Measurable K) :
    (∫⁻ t : ℝ in Ioi 0, ∫⁻ a : ℝ in Ioi 0,
      ∫⁻ p : ℝ≥0 × Path in {p | p.1 < Real.toNNReal t},
        (∫⁻ l : ℝ in Ioi ((Real.toNNReal t-p.1 : ℝ≥0) : ℝ),
          K ((a,p),l)/ENNReal.ofReal l)
        ∂pathLaw.map (actualDriverPassagePast lambda (-a))) =
      ∫⁻ a : ℝ in Ioi 0, ∫⁻ p : ℝ≥0 × Path,
        (∫⁻ l : ℝ in Ioi 0, K ((a,p),l))
        ∂pathLaw.map (actualDriverPassagePast lambda (-a)) := by
  let μ : Measure (ℝ × Path) := (volume.restrict (Ioi (0 : ℝ))).prod pathLaw
  let Q : ℝ × Path → ℝ × (ℝ≥0 × Path) :=
    parameterDriverPassagePast (fun _ : ℝ ↦ lambda) (fun a : ℝ ↦ -a)
  have hQ : Measurable Q :=
    measurable_parameterDriverPassagePast measurable_const measurable_id.neg
  let s : ℝ × Path → ℝ≥0 := fun z ↦ (Q z).2.1
  let J : (ℝ × Path) × ℝ → ℝ≥0∞ := fun z ↦ K (Q z.1,z.2)
  have hs : Measurable s := hQ.snd.fst
  have hJ : Measurable J := hK.comp ((hQ.comp measurable_fst).prodMk measurable_snd)
  have hdiv : Measurable (fun z : (ℝ × (ℝ≥0 × Path)) × ℝ ↦
      K z/ENNReal.ofReal z.2) := hK.div measurable_snd.ennreal_ofReal
  have hbase := measurable_joint_anchorKernel
    (fun z : ℝ × (ℝ≥0 × Path) ↦ z.2.1) _ measurable_snd.fst hdiv
  have hbase_t (t : ℝ) : Measurable (fun z : ℝ × (ℝ≥0 × Path) ↦
      if (z.2.1 : ℝ) < t then
        ∫⁻ l in Ioi (t-(z.2.1 : ℝ)), K (z,l)/ENNReal.ofReal l else 0) :=
    hbase.comp (measurable_const.prodMk measurable_id)
  have hraw_t (t : ℝ) : Measurable (fun z : ℝ × Path ↦
      if (s z : ℝ) < t then
        ∫⁻ l in Ioi (t-(s z : ℝ)), J (z,l)/ENNReal.ofReal l else 0) :=
    (hbase_t t).comp hQ
  have hleft (t : ℝ) (ht : 0 < t) :
      (∫⁻ a : ℝ in Ioi 0, ∫⁻ p : ℝ≥0 × Path in {p | p.1 < Real.toNNReal t},
        (∫⁻ l : ℝ in Ioi ((Real.toNNReal t-p.1 : ℝ≥0) : ℝ),
          K ((a,p),l)/ENNReal.ofReal l)
        ∂pathLaw.map (actualDriverPassagePast lambda (-a))) =
      ∫⁻ z, if (s z : ℝ) < t then
        ∫⁻ l in Ioi (t-(s z : ℝ)), J (z,l)/ENNReal.ofReal l else 0 ∂μ := by
    rw [lintegral_prod _ (hraw_t t).aemeasurable]
    apply lintegral_congr
    intro a
    rw [← lintegral_indicator (measurableSet_lt measurable_fst measurable_const)]
    have he : (fun p : ℝ≥0 × Path ↦
        {p | p.1 < Real.toNNReal t}.indicator
          (fun p ↦ ∫⁻ l : ℝ in Ioi ((Real.toNNReal t-p.1 : ℝ≥0) : ℝ),
            K ((a,p),l)/ENNReal.ofReal l) p) =
        fun p ↦ if (p.1 : ℝ) < t then
          ∫⁻ l in Ioi (t-(p.1 : ℝ)), K ((a,p),l)/ENNReal.ofReal l else 0 := by
      funext p
      exact (real_anchor_eq_nn_anchor p.1
        (fun l ↦ K ((a,p),l)/ENNReal.ofReal l) t ht.le).symm
    rw [he]
    have hm : Measurable (fun p : ℝ≥0 × Path ↦
        if (p.1 : ℝ) < t then
          ∫⁻ l in Ioi (t-(p.1 : ℝ)), K ((a,p),l)/ENNReal.ofReal l else 0) :=
      (hbase_t t).comp (measurable_const.prodMk measurable_id)
    exact lintegral_map hm (measurable_actualDriverPassagePast lambda (-a))
  have hfull : Measurable (fun z : ℝ × (ℝ≥0 × Path) ↦
      ∫⁻ l : ℝ in Ioi 0, K (z,l)) := hK.lintegral_prod_right'
  have hright :
      (∫⁻ z, (∫⁻ l : ℝ in Ioi 0, J (z,l)) ∂μ) =
        ∫⁻ a : ℝ in Ioi 0, ∫⁻ p : ℝ≥0 × Path,
          (∫⁻ l : ℝ in Ioi 0, K ((a,p),l))
          ∂pathLaw.map (actualDriverPassagePast lambda (-a)) := by
    exact (actual_depth_source_lintegral lambda _ hfull).symm
  calc
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ z,
        if (s z : ℝ) < t then
          ∫⁻ l in Ioi (t-(s z : ℝ)), J (z,l)/ENNReal.ofReal l else 0 ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hleft t ht
    _ = ∫⁻ z, (∫⁻ l : ℝ in Ioi 0, J (z,l)) ∂μ :=
      anchor_time_inverse_length_lintegral μ s J hs hJ
    _ = _ := hright

theorem actual_passage_anchor_inverse_length_swapped_lintegral (lambda : ℝ)
    (K : (ℝ × (ℝ≥0 × Path)) × ℝ → ℝ≥0∞) (hK : Measurable K) :
    (∫⁻ t : ℝ in Ioi 0, ∫⁻ a : ℝ in Ioi 0,
      ∫⁻ p : ℝ≥0 × Path in {p | p.1 < Real.toNNReal t},
        (∫⁻ l : ℝ in Ioi ((Real.toNNReal t-p.1 : ℝ≥0) : ℝ),
          K ((a,p),l)/ENNReal.ofReal l)
        ∂pathLaw.map (actualDriverPassagePast lambda (-a))) =
      ∫⁻ l : ℝ in Ioi 0, ∫⁻ a : ℝ in Ioi 0, ∫⁻ p : ℝ≥0 × Path,
        K ((a,p),l) ∂pathLaw.map (actualDriverPassagePast lambda (-a)) := by
  let μ : Measure (ℝ × Path) := (volume.restrict (Ioi (0 : ℝ))).prod pathLaw
  let Q : ℝ × Path → ℝ × (ℝ≥0 × Path) :=
    parameterDriverPassagePast (fun _ : ℝ ↦ lambda) (fun a : ℝ ↦ -a)
  have hQ : Measurable Q :=
    measurable_parameterDriverPassagePast measurable_const measurable_id.neg
  have hJ : Measurable (fun z : (ℝ × Path) × ℝ ↦ K (Q z.1,z.2)) :=
    hK.comp ((hQ.comp measurable_fst).prodMk measurable_snd)
  have hfull : Measurable (fun z : ℝ × (ℝ≥0 × Path) ↦
      ∫⁻ l : ℝ in Ioi 0, K (z,l)) := hK.lintegral_prod_right'
  calc
    _ = ∫⁻ a : ℝ in Ioi 0, ∫⁻ p : ℝ≥0 × Path,
        (∫⁻ l : ℝ in Ioi 0, K ((a,p),l))
        ∂pathLaw.map (actualDriverPassagePast lambda (-a)) :=
      actual_passage_anchor_inverse_length_lintegral lambda K hK
    _ = ∫⁻ z : ℝ × Path, (∫⁻ l : ℝ in Ioi 0, K (Q z,l)) ∂μ :=
      actual_depth_source_lintegral lambda _ hfull
    _ = ∫⁻ l : ℝ in Ioi 0, ∫⁻ z : ℝ × Path, K (Q z,l) ∂μ :=
      lintegral_lintegral_swap hJ.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro l
      have hm : Measurable (fun z : ℝ × (ℝ≥0 × Path) ↦ K (z,l)) :=
        hK.comp (measurable_id.prodMk measurable_const)
      exact (actual_depth_source_lintegral lambda _ hm).symm

end PerronWright.BrownianActualPassageAnchorExchange
