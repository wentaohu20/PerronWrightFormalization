import PerronWright.Probability.BrownianParabolicFirstPassageStrongMarkovFull
import PerronWright.Probability.BrownianFirstPassageMinimumWindowGeometry

/-! # Actual parabolic minimum windows retain the raw Brownian pieces

The true uncapped parabolic hitting product law is restricted to a
finite horizon and to the literal lower-minimum window. The survival
condition uses the shifted parabolic parameter, while the entire raw
Brownian past and future remain in arbitrary nonnegative Borel tests.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianParabolicMinimumWindowPastFutureLaw

open BrownianPathLaw ContinuousPathFirstPassage BrownianPathReflectionLaw
open BrownianParabolicFirstPassageStrongMarkovFull BrownianParabolicFirstPassageFinite
open BrownianParabolicFirstPassageStrongMarkov
open BrownianFirstPassageMinimumWindowGeometry BrownianFirstPassageEndpointGeometry

def passagePastLaw (lambda level : ℝ) : Measure (ℝ≥0 × Path) :=
  pathLaw.map (parabolicPassagePast lambda level)

def futureSurvival (lambda δ : ℝ) (T : ℝ≥0) : Set ((ℝ≥0 × Path) × Path) :=
  {p | driftPath (lambda-(p.1.1 : ℝ)) p.2 ∈ survival (-δ) (remainingTime T (p.1.1 : ℝ))}

theorem measurableSet_futureSurvival (lambda δ : ℝ) (T : ℝ≥0) :
    MeasurableSet (futureSurvival lambda δ T) := by
  have ht : Measurable (fun p : (ℝ≥0 × Path) × Path ↦ (p.1.1 : ℝ)) :=
    NNReal.continuous_coe.measurable.comp measurable_fst.fst
  have hd : Measurable (fun p : (ℝ≥0 × Path) × Path ↦ driftPath (lambda-(p.1.1 : ℝ)) p.2) :=
    continuous_driftPath.measurable.comp ((measurable_const.sub ht).prodMk measurable_snd)
  have h := (BrownianFirstPassageMinimumWindowGeometry.measurableSet_futureSurvival δ T).preimage
    (ht.prodMk hd)
  simpa only [futureSurvival,BrownianFirstPassageMinimumWindowGeometry.futureSurvival,
    Set.preimage_ofPred_eq] using h

theorem restricted_past_future_jointLaw (lambda level : ℝ) (T : ℝ≥0) :
    (pathLaw.restrict {f : Path | parabolicPassageTime lambda level f < T}).map
      (fun f ↦ (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f)) =
      ((passagePastLaw lambda level).restrict {p : ℝ≥0 × Path | p.1 < T}).prod pathLaw := by
  have hm := (measurable_parabolicPassagePast lambda level).prodMk
    (measurable_parabolicPassageFuture lambda level)
  have hset : MeasurableSet ({p : ℝ≥0 × Path | p.1 < T} ×ˢ (univ : Set Path)) :=
    ((measurable_fst : Measurable (Prod.fst : ℝ≥0 × Path → ℝ≥0)) measurableSet_Iio).prod
      MeasurableSet.univ
  have hr := Measure.restrict_map (μ := pathLaw) hm hset
  rw [parabolic_passage_jointLaw lambda level,← Measure.restrict_prod_eq_prod_univ] at hr
  have hp : (fun f : Path ↦
      (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f)) ⁻¹'
      ({p : ℝ≥0 × Path | p.1 < T} ×ˢ (univ : Set Path)) =
      {f : Path | parabolicPassageTime lambda level f < T} := by
    ext f
    simp only [mem_preimage,mem_prod,mem_univ,and_true,mem_ofPred_eq,parabolicPassagePast]
  rw [hp] at hr
  exact hr.symm

theorem ae_survival_after_parabolicPassage_iff (lambda level : ℝ) (hlevel : level < 0)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0) :
    ∀ᵐ f ∂pathLaw, parabolicPassageTime lambda level f < T →
      (driftPath lambda f ∈ survival (level-δ) T ↔
        (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f) ∈
          futureSurvival lambda δ T) := by
  filter_upwards [ae_parabolicFirstPassage_ne_top lambda level,
    isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hfin h0
  intro ht
  have hstart : level < driftPath lambda f 0 := by
    simpa only [driftPath_apply,NNReal.coe_zero,mul_zero,zero_pow (by norm_num : 2 ≠ 0),
      zero_div,add_zero,sub_zero,h0] using hlevel
  have hs := survival_after_firstPassage_iff level δ hδ T (driftPath lambda f) hstart hfin ht.le
  change _ ↔ BrownianPathIndependentIncrements.futurePath
    (parabolicPassageTime lambda level f) (driftPath lambda f) ∈
      survival (-δ) (remainingTime T (parabolicPassageTime lambda level f : ℝ)) at hs
  rw [actual_drift_futurePath_eq_shift] at hs
  exact hs

theorem actual_minimum_window_past_future_lintegral (lambda level : ℝ) (hlevel : level < 0)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Ψ : ((ℝ≥0 × Path) × Path) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f in {f : Path | parabolicPassageTime lambda level f < T},
      ((driftPath lambda) ⁻¹' survival (level-δ) T).indicator
        (fun f ↦ Ψ (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f)) f
          ∂pathLaw) =
      ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        ∫⁻ g in (driftPath (lambda-(p.1 : ℝ))) ⁻¹' survival (-δ) (remainingTime T (p.1 : ℝ)),
          Ψ (p,g) ∂pathLaw ∂passagePastLaw lambda level := by
  let F : ((ℝ≥0 × Path) × Path) → ℝ≥0∞ := (futureSurvival lambda δ T).indicator Ψ
  have hF : Measurable F := hΨ.indicator (measurableSet_futureSurvival lambda δ T)
  have hH : MeasurableSet {f : Path | parabolicPassageTime lambda level f < T} :=
    (measurable_parabolicPassageTime lambda level) measurableSet_Iio
  have he : (fun f : Path ↦ ((driftPath lambda) ⁻¹' survival (level-δ) T).indicator
      (fun f ↦ Ψ (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f)) f) =ᵐ[
        pathLaw.restrict {f : Path | parabolicPassageTime lambda level f < T}]
      F ∘ (fun f ↦ (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f)) := by
    filter_upwards [ae_restrict_of_ae
      (ae_survival_after_parabolicPassage_iff lambda level hlevel δ hδ T),
      ae_restrict_mem hH] with f hs ht
    have hse := hs ht
    change ((driftPath lambda) ⁻¹' survival (level-δ) T).indicator
      (fun f ↦ Ψ (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f)) f =
      (futureSurvival lambda δ T).indicator Ψ
        (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f)
    by_cases hsurv : driftPath lambda f ∈ survival (level-δ) T
    · simp only [Set.indicator,mem_preimage,if_pos hsurv,if_pos (hse.mp hsurv)]
    · have hfuture : (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f) ∉
          futureSurvival lambda δ T := fun h ↦ hsurv (hse.mpr h)
      simp only [Set.indicator,mem_preimage,if_neg hsurv,if_neg hfuture]
  rw [lintegral_congr_ae he]
  change (∫⁻ f in {f : Path | parabolicPassageTime lambda level f < T},
    F (parabolicPassagePast lambda level f,parabolicPassageFuture lambda level f) ∂pathLaw) = _
  rw [← lintegral_map hF ((measurable_parabolicPassagePast lambda level).prodMk
    (measurable_parabolicPassageFuture lambda level)),
    restricted_past_future_jointLaw lambda level T,lintegral_prod _ hF.aemeasurable]
  apply lintegral_congr
  intro p
  have hd : Measurable (driftPath (lambda-(p.1 : ℝ))) :=
    (continuous_driftPath.comp (continuous_const.prodMk continuous_id)).measurable
  rw [← lintegral_indicator
    ((measurableSet_survival (-δ) (remainingTime T (p.1 : ℝ))).preimage hd)]
  apply lintegral_congr
  intro g
  rfl

end PerronWright.BrownianParabolicMinimumWindowPastFutureLaw
