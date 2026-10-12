import PerronWright.Probability.BrownianMinimumSplitCandidate

/-! # Explicit depth and time marginals of the genuine split candidate

These computations use the actual negative-level first-passage density
and the probability law of the minimum-future source. They do not presume
that the full candidate has been identified with the actual minimum split.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumSplitCandidateMarginals

open BrownianPathLaw BrownianMinimumSplitCandidate BrownianMinimumFutureEntranceSource
open BrownianFirstPassagePastTimeMarginal BrownianFirstPassageDensityGeometry
open BrownianMinimumWindowSurvivalBounds
open BrownianFirstPassageMinimumWindowPastFutureLaw

private def timeWeight (T : ℝ≥0) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-s))

private theorem measurable_timeWeight (T : ℝ≥0) : Measurable (timeWeight T) := by
  unfold timeWeight
  fun_prop

def depthTimeDensity (T : ℝ≥0) (q : ℝ × ℝ) : ℝ≥0∞ :=
  (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) (T : ℝ)).indicator
    (fun q ↦ density q.1 q.2*(ENNReal.ofReal entranceCoefficient*
      ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-q.2)))) q

def arcsineDensity (T : ℝ≥0) (s : ℝ) : ℝ≥0∞ :=
  (Ioo (0 : ℝ) (T : ℝ)).indicator
    (fun s ↦ ENNReal.ofReal (1/(Real.pi*Real.sqrt (s*((T : ℝ)-s))))) s

private theorem measurable_depthTimeDensity (T : ℝ≥0) : Measurable (depthTimeDensity T) :=
  (BrownianHeatResolvent.measurable_joint_passageDensity.mul
    ((measurable_timeWeight T).comp measurable_snd)).indicator
      (measurableSet_Ioi.prod measurableSet_Ioo)

private theorem measurable_arcsineDensity (T : ℝ≥0) : Measurable (arcsineDensity T) :=
  (by fun_prop : Measurable (fun s : ℝ ↦
    ENNReal.ofReal (1/(Real.pi*Real.sqrt (s*((T : ℝ)-s)))))).indicator measurableSet_Ioo

theorem candidate_depth_time_lintegral (T : ℝ≥0) (H : ℝ × ℝ → ℝ≥0∞)
    (hH : Measurable H) :
    (∫⁻ q, H (-q.2.1,(q.1.1 : ℝ)) ∂candidateLaw T) =
      ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        density a s*(ENNReal.ofReal entranceCoefficient*
          ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-s)))*H (a,s) := by
  have hm : Measurable (fun q : (ℝ≥0 × Path) × (ℝ × Path) ↦
      H (-q.2.1,(q.1.1 : ℝ))) :=
    hH.comp (measurable_snd.fst.neg.prodMk
      (NNReal.continuous_coe.measurable.comp measurable_fst.fst))
  rw [lintegral_candidateLaw T _ hm]
  simp only [neg_neg,lintegral_const,measure_univ,mul_one]
  change (∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
    timeWeight T (p.1 : ℝ)*H (a,(p.1 : ℝ)) ∂passagePastLaw (-a)) = _
  rw [lintegral_level_past_time_density T
    (fun q : ℝ × ℝ ↦ timeWeight T q.2*H q)
    (((measurable_timeWeight T).comp measurable_snd).mul hH)]
  apply lintegral_congr
  intro s
  exact lintegral_congr (fun a ↦ (mul_assoc _ _ _).symm)

private theorem lintegral_depthTimeDensity (T : ℝ≥0) (H : ℝ × ℝ → ℝ≥0∞)
    (hH : Measurable H) :
    (∫⁻ q : ℝ × ℝ, depthTimeDensity T q*H q) =
      ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        density a s*timeWeight T s*H (a,s) := by
  have he : (fun q : ℝ × ℝ ↦ depthTimeDensity T q*H q) =
      (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) (T : ℝ)).indicator
        (fun q ↦ density q.1 q.2*timeWeight T q.2*H q) := by
    funext q
    unfold depthTimeDensity
    by_cases hq : q ∈ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) (T : ℝ) <;> simp [hq,timeWeight]
  rw [he,lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  have hm : Measurable (fun q : ℝ × ℝ ↦ density q.1 q.2*timeWeight T q.2*H q) :=
    (BrownianHeatResolvent.measurable_joint_passageDensity.mul
      ((measurable_timeWeight T).comp measurable_snd)).mul hH
  exact setLIntegral_prod_symm _ hm.aemeasurable

theorem candidate_depth_time_map_eq_withDensity (T : ℝ≥0) :
    (candidateLaw T).map
      (fun q : (ℝ≥0 × Path) × (ℝ × Path) ↦ (-q.2.1,(q.1.1 : ℝ))) =
        volume.withDensity (depthTimeDensity T) := by
  have hm : Measurable (fun q : (ℝ≥0 × Path) × (ℝ × Path) ↦
      (-q.2.1,(q.1.1 : ℝ))) :=
    measurable_snd.fst.neg.prodMk
      (NNReal.continuous_coe.measurable.comp measurable_fst.fst)
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH hm,candidate_depth_time_lintegral T H hH,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_depthTimeDensity T) hH]
  exact (lintegral_depthTimeDensity T H hH).symm

private theorem coefficient_ratio : entranceCoefficient/Real.sqrt (2*Real.pi) =
    1/Real.pi := by
  rw [entranceCoefficient,Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  calc
    (Real.sqrt 2/Real.sqrt Real.pi)/(Real.sqrt 2*Real.sqrt Real.pi) =
        1/(Real.sqrt Real.pi*Real.sqrt Real.pi) := by field_simp
    _ = 1/Real.pi := by rw [Real.mul_self_sqrt Real.pi_pos.le]

private theorem passage_weight_eq_arcsine (T : ℝ≥0) (s : ℝ)
    (hs : s ∈ Ioo (0 : ℝ) (T : ℝ)) :
    ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*timeWeight T s =
      ENNReal.ofReal (1/(Real.pi*Real.sqrt (s*((T : ℝ)-s)))) := by
  have hcoeff : 0 ≤ entranceCoefficient := by unfold entranceCoefficient; positivity
  rw [timeWeight,← ENNReal.ofReal_mul hcoeff,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.sqrt_mul hs.1.le]
  calc
    (1/(Real.sqrt (2*Real.pi)*Real.sqrt s))*
        (entranceCoefficient*(1/Real.sqrt ((T : ℝ)-s))) =
      (entranceCoefficient/Real.sqrt (2*Real.pi))*
        (1/(Real.sqrt s*Real.sqrt ((T : ℝ)-s))) := by ring
    _ = _ := by rw [coefficient_ratio]; ring

theorem candidate_time_lintegral (T : ℝ≥0) (H : ℝ → ℝ≥0∞)
    (hH : Measurable H) :
    (∫⁻ q, H (q.1.1 : ℝ) ∂candidateLaw T) =
      ∫⁻ s : ℝ, arcsineDensity T s*H s := by
  have hc := candidate_depth_time_lintegral T (fun q : ℝ × ℝ ↦ H q.2)
    (hH.comp measurable_snd)
  change (∫⁻ q, H (q.1.1 : ℝ) ∂candidateLaw T) = _ at hc
  rw [hc]
  change (∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
    density a s*timeWeight T s*H s) = _
  have he : (fun s : ℝ ↦ ∫⁻ a in Ioi (0 : ℝ), density a s*timeWeight T s*H s) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) (T : ℝ))]
      fun s ↦ ENNReal.ofReal (1/(Real.pi*Real.sqrt (s*((T : ℝ)-s))))*H s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hd : Measurable (fun a : ℝ ↦ density a s) :=
      BrownianHeatResolvent.measurable_joint_passageDensity.comp
        (measurable_id.prodMk measurable_const)
    simp_rw [mul_assoc]
    rw [lintegral_mul_const'' _ hd.aemeasurable,passage_level_mass s hs.1,
      ← mul_assoc,passage_weight_eq_arcsine T s hs]
  rw [lintegral_congr_ae he]
  have hf : (fun s : ℝ ↦ arcsineDensity T s*H s) =
      (Ioo (0 : ℝ) (T : ℝ)).indicator
        (fun s ↦ ENNReal.ofReal (1/(Real.pi*Real.sqrt (s*((T : ℝ)-s))))*H s) := by
    funext s
    unfold arcsineDensity
    by_cases hs : s ∈ Ioo (0 : ℝ) (T : ℝ) <;> simp [hs]
  rw [hf,lintegral_indicator measurableSet_Ioo]

theorem candidate_time_map_eq_withDensity (T : ℝ≥0) :
    (candidateLaw T).map (fun q : (ℝ≥0 × Path) × (ℝ × Path) ↦ (q.1.1 : ℝ)) =
      volume.withDensity (arcsineDensity T) := by
  have hm : Measurable (fun q : (ℝ≥0 × Path) × (ℝ × Path) ↦ (q.1.1 : ℝ)) :=
    NNReal.continuous_coe.measurable.comp measurable_fst.fst
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH hm,candidate_time_lintegral T H hH,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_arcsineDensity T) hH]
  rfl

end PerronWright.BrownianMinimumSplitCandidateMarginals
