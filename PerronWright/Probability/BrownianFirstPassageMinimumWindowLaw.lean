import PerronWright.Probability.BrownianFirstPassageEndpointJointLaw
import PerronWright.Probability.BrownianFirstPassageMinimumWindowGeometry
import PerronWright.Probability.BrownianPositiveKilledEndpoint

/-! # Actual endpoint disintegration in a minimum-depth window

The Brownian path first hits a negative level before the endpoint horizon
and then stays strictly above a lower level. The whole-future product law
and exact first-hit geometry identify the resulting endpoint measure with
the genuine killed Brownian endpoint law, integrated against the genuine
first-passage time law. No bridge minimum-time or excursion decomposition
is an input to this identity.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageMinimumWindowLaw

open BrownianPathLaw ContinuousPathFirstPassage BrownianFirstPassageUncappedLaw
open BrownianFirstPassageEndpointGeometry BrownianFirstPassageEndpointJointLaw
open BrownianFirstPassageMinimumWindowGeometry

theorem futureSurvival_lintegral (level δ : ℝ) (T : ℝ≥0) (s : ℝ)
    (Φ : ℝ × ℝ → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ g, (futureSurvival δ T).indicator
      (fun p ↦ Φ (endpointMap level T p)) (s,g) ∂pathLaw) =
      ∫⁻ y, Φ (s,level-δ+y) ∂BrownianPositiveKilledEndpoint.law δ (remainingTime T s) := by
  have hΦs : Measurable (fun y : ℝ ↦ Φ (s,level-δ+y)) :=
    hΦ.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  have hm : Measurable (fun g : Path ↦ g (remainingTime T s)+δ) :=
    (continuous_eval (remainingTime T s)).measurable.add measurable_const
  rw [BrownianPositiveKilledEndpoint.law,lintegral_map hΦs hm,
    ← lintegral_indicator (measurableSet_survival (-δ) (remainingTime T s))]
  apply lintegral_congr
  intro g
  by_cases hg : g ∈ survival (-δ) (remainingTime T s)
  · simp only [Set.indicator,mem_ofPred_eq,futureSurvival,hg,if_pos,
      endpointMap,futureEndpoint]
    congr 2
    ring
  · simp [futureSurvival,hg]

theorem actual_minimum_window_lintegral (level : ℝ) (hlevel : level < 0)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Φ : ℝ × ℝ → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ f in {f : Path | realTime level f < (T : ℝ)},
      (survival (level-δ) T).indicator (fun f ↦ Φ (realTime level f,f T)) f ∂pathLaw) =
      ∫⁻ s in Iio (T : ℝ), ∫⁻ y, Φ (s,level-δ+y)
        ∂BrownianPositiveKilledEndpoint.law δ (remainingTime T s) ∂timeLaw level := by
  let Ψ : ℝ × Path → ℝ≥0∞ := (futureSurvival δ T).indicator
    (fun p ↦ Φ (endpointMap level T p))
  have hΨ : Measurable Ψ :=
    (hΦ.comp (continuous_endpointMap level T).measurable).indicator
      (measurableSet_futureSurvival δ T)
  have hH : MeasurableSet {f : Path | realTime level f < (T : ℝ)} :=
    (measurable_realTime level) measurableSet_Iio
  have he : (fun f : Path ↦ (survival (level-δ) T).indicator
      (fun f ↦ Φ (realTime level f,f T)) f) =ᵐ[
      pathLaw.restrict {f : Path | realTime level f < (T : ℝ)}]
      Ψ ∘ (fun f ↦ (realTime level f,passageFuture level f)) := by
    filter_upwards [ae_restrict_of_ae (ae_endpoint_reconstruction level hlevel T),
      ae_restrict_of_ae (ae_survival_after_firstPassage_iff level hlevel δ hδ T),
      ae_restrict_mem hH] with f hf hs hmem
    have hse := hs hmem
    have hfe := hf hmem
    change (survival (level-δ) T).indicator (fun f ↦ Φ (realTime level f,f T)) f =
      (futureSurvival δ T).indicator (fun p ↦ Φ (endpointMap level T p))
        (realTime level f,passageFuture level f)
    by_cases hsurv : f ∈ survival (level-δ) T
    · have hfuture := hse.mp hsurv
      simp only [Set.indicator,if_pos hsurv,if_pos hfuture,endpointMap,hfe]
    · have hfuture : (realTime level f,passageFuture level f) ∉ futureSurvival δ T :=
        fun h ↦ hsurv (hse.mpr h)
      simp only [Set.indicator,if_neg hsurv,if_neg hfuture]
  rw [lintegral_congr_ae he]
  change (∫⁻ f in {f : Path | realTime level f < (T : ℝ)},
    Ψ (realTime level f,passageFuture level f) ∂pathLaw) = _
  rw [← lintegral_map hΨ
    ((measurable_realTime level).prodMk (measurable_passageFuture level)),
    restricted_time_future_jointLaw level hlevel T,
    lintegral_prod _ hΨ.aemeasurable]
  apply lintegral_congr
  intro s
  exact futureSurvival_lintegral level δ T s Φ hΦ

end PerronWright.BrownianFirstPassageMinimumWindowLaw
