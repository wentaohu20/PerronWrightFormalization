import PerronWright.Probability.BrownianFirstPassageEndpointJointLaw
import PerronWright.Probability.BrownianFirstPassageMinimumWindowGeometry

/-! # Genuine whole-future disintegration in a minimum-depth window

The entire future path, not just its terminal point, is retained in this
identity. Thus later finite-dimensional tests can be reconstructed after
the actual first hit without inserting a conditional Markov interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageMinimumWindowFutureLaw

open BrownianPathLaw ContinuousPathFirstPassage BrownianFirstPassageUncappedLaw
open BrownianFirstPassageEndpointGeometry BrownianFirstPassageEndpointJointLaw
open BrownianFirstPassageMinimumWindowGeometry

theorem actual_minimum_window_future_lintegral (level : ℝ) (hlevel : level < 0)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0)
    (Ψ : ℝ × Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f in {f : Path | realTime level f < (T : ℝ)},
      (survival (level-δ) T).indicator
        (fun f ↦ Ψ (realTime level f,passageFuture level f)) f ∂pathLaw) =
      ∫⁻ s in Iio (T : ℝ), ∫⁻ g in survival (-δ) (remainingTime T s),
        Ψ (s,g) ∂pathLaw ∂timeLaw level := by
  let F : ℝ × Path → ℝ≥0∞ := (futureSurvival δ T).indicator Ψ
  have hF : Measurable F := hΨ.indicator (measurableSet_futureSurvival δ T)
  have hH : MeasurableSet {f : Path | realTime level f < (T : ℝ)} :=
    (measurable_realTime level) measurableSet_Iio
  have he : (fun f : Path ↦ (survival (level-δ) T).indicator
      (fun f ↦ Ψ (realTime level f,passageFuture level f)) f) =ᵐ[
      pathLaw.restrict {f : Path | realTime level f < (T : ℝ)}]
      F ∘ (fun f ↦ (realTime level f,passageFuture level f)) := by
    filter_upwards [ae_restrict_of_ae (ae_survival_after_firstPassage_iff level hlevel δ hδ T),
      ae_restrict_mem hH] with f hs hmem
    have hse := hs hmem
    change (survival (level-δ) T).indicator
      (fun f ↦ Ψ (realTime level f,passageFuture level f)) f =
      (futureSurvival δ T).indicator Ψ (realTime level f,passageFuture level f)
    by_cases hsurv : f ∈ survival (level-δ) T
    · simp only [Set.indicator,if_pos hsurv,if_pos (hse.mp hsurv)]
    · have hfuture : (realTime level f,passageFuture level f) ∉ futureSurvival δ T :=
        fun h ↦ hsurv (hse.mpr h)
      simp only [Set.indicator,if_neg hsurv,if_neg hfuture]
  rw [lintegral_congr_ae he]
  change (∫⁻ f in {f : Path | realTime level f < (T : ℝ)},
    F (realTime level f,passageFuture level f) ∂pathLaw) = _
  rw [← lintegral_map hF
    ((measurable_realTime level).prodMk (measurable_passageFuture level)),
    restricted_time_future_jointLaw level hlevel T,lintegral_prod _ hF.aemeasurable]
  apply lintegral_congr
  intro s
  rw [← lintegral_indicator (measurableSet_survival (-δ) (remainingTime T s))]
  apply lintegral_congr
  intro g
  rfl

end PerronWright.BrownianFirstPassageMinimumWindowFutureLaw
