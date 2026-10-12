import PerronWright.Probability.BrownianFirstPassageMinimumWindowFutureLaw
import PerronWright.Probability.BrownianFirstPassageStrongMarkovFull

/-! # Actual minimum-depth windows retaining the whole stopped past

The literal negative-level first hit separates the entire stopped past
from the entire future Brownian path. Restriction to a finite horizon
and the actual lower-minimum-window event are carried through this
product law for arbitrary nonnegative Borel tests. No random-excursion
Palm law or conditional-distribution interface is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFirstPassageMinimumWindowPastFutureLaw

open BrownianPathLaw ContinuousPathFirstPassage BrownianFirstPassageUncappedLaw
open BrownianFirstPassageStrongMarkovFull BrownianFirstPassageEndpointGeometry

def passagePastLaw (level : ℝ) : Measure (ℝ≥0 × Path) := pathLaw.map (passagePast level)

def futureSurvival (δ : ℝ) (T : ℝ≥0) : Set ((ℝ≥0 × Path) × Path) :=
  {p | p.2 ∈ survival (-δ) (remainingTime T (p.1.1 : ℝ))}

theorem measurableSet_futureSurvival (δ : ℝ) (T : ℝ≥0) :
    MeasurableSet (futureSurvival δ T) := by
  have hm : Measurable (fun p : (ℝ≥0 × Path) × Path ↦ ((p.1.1 : ℝ),p.2)) :=
    (NNReal.continuous_coe.measurable.comp measurable_fst.fst).prodMk measurable_snd
  have h := (BrownianFirstPassageMinimumWindowGeometry.measurableSet_futureSurvival δ T).preimage hm
  simpa only [futureSurvival,BrownianFirstPassageMinimumWindowGeometry.futureSurvival,
    Set.preimage_ofPred_eq] using h

theorem restricted_past_future_jointLaw (level : ℝ) (hlevel : level < 0) (T : ℝ≥0) :
    (pathLaw.restrict {f : Path | passageTime level f < T}).map
      (fun f ↦ (passagePast level f,passageFuture level f)) =
      ((passagePastLaw level).restrict {p : ℝ≥0 × Path | p.1 < T}).prod pathLaw := by
  have hm := (measurable_passagePast level).prodMk (measurable_passageFuture level)
  have hset : MeasurableSet ({p : ℝ≥0 × Path | p.1 < T} ×ˢ (univ : Set Path)) :=
    ((measurable_fst : Measurable (Prod.fst : ℝ≥0 × Path → ℝ≥0)) measurableSet_Iio).prod
      MeasurableSet.univ
  have hr := Measure.restrict_map (μ := pathLaw) hm hset
  rw [passage_jointLaw level hlevel,← Measure.restrict_prod_eq_prod_univ] at hr
  have hp : (fun f : Path ↦ (passagePast level f,passageFuture level f)) ⁻¹'
      ({p : ℝ≥0 × Path | p.1 < T} ×ˢ (univ : Set Path)) =
      {f : Path | passageTime level f < T} := by
    ext f
    simp only [mem_preimage,mem_prod,mem_univ,and_true,mem_ofPred_eq,passagePast]
  rw [hp] at hr
  exact hr.symm

theorem actual_minimum_window_past_future_lintegral (level : ℝ) (hlevel : level < 0)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Ψ : ((ℝ≥0 × Path) × Path) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f in {f : Path | passageTime level f < T},
      (survival (level-δ) T).indicator
        (fun f ↦ Ψ (passagePast level f,passageFuture level f)) f ∂pathLaw) =
      ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        ∫⁻ g in survival (-δ) (remainingTime T (p.1 : ℝ)), Ψ (p,g) ∂pathLaw
          ∂passagePastLaw level := by
  let F : ((ℝ≥0 × Path) × Path) → ℝ≥0∞ := (futureSurvival δ T).indicator Ψ
  have hF : Measurable F := hΨ.indicator (measurableSet_futureSurvival δ T)
  have hH : MeasurableSet {f : Path | passageTime level f < T} :=
    (measurable_passageTime level) measurableSet_Iio
  have he : (fun f : Path ↦ (survival (level-δ) T).indicator
      (fun f ↦ Ψ (passagePast level f,passageFuture level f)) f) =ᵐ[
        pathLaw.restrict {f : Path | passageTime level f < T}]
      F ∘ (fun f ↦ (passagePast level f,passageFuture level f)) := by
    filter_upwards [ae_restrict_of_ae
      (BrownianFirstPassageMinimumWindowGeometry.ae_survival_after_firstPassage_iff
        level hlevel δ hδ T),ae_restrict_mem hH] with f hs hmem
    have ht : realTime level f < (T : ℝ) := by exact_mod_cast hmem
    have hse : f ∈ survival (level-δ) T ↔
        (passagePast level f,passageFuture level f) ∈ futureSurvival δ T := hs ht
    change (survival (level-δ) T).indicator
      (fun f ↦ Ψ (passagePast level f,passageFuture level f)) f =
      (futureSurvival δ T).indicator Ψ (passagePast level f,passageFuture level f)
    by_cases hsurv : f ∈ survival (level-δ) T
    · simp only [Set.indicator,if_pos hsurv,if_pos (hse.mp hsurv)]
    · have hfuture : (passagePast level f,passageFuture level f) ∉ futureSurvival δ T :=
        fun h ↦ hsurv (hse.mpr h)
      simp only [Set.indicator,if_neg hsurv,if_neg hfuture]
  rw [lintegral_congr_ae he]
  change (∫⁻ f in {f : Path | passageTime level f < T},
    F (passagePast level f,passageFuture level f) ∂pathLaw) = _
  rw [← lintegral_map hF ((measurable_passagePast level).prodMk (measurable_passageFuture level)),
    restricted_past_future_jointLaw level hlevel T,lintegral_prod _ hF.aemeasurable]
  apply lintegral_congr
  intro p
  rw [← lintegral_indicator (measurableSet_survival (-δ) (remainingTime T (p.1 : ℝ)))]
  apply lintegral_congr
  intro g
  rfl

end PerronWright.BrownianFirstPassageMinimumWindowPastFutureLaw
