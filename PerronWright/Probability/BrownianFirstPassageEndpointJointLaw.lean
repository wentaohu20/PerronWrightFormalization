import PerronWright.Probability.BrownianFirstPassageEndpointGeometry
import PerronWright.Probability.BrownianFirstPassageStrongMarkovFull

/-! # Actual first-passage time and later Brownian endpoint

The actual negative-level first-passage time and whole future have a
proved product law. Restricting the actual passage before a fixed
horizon and reconstructing that endpoint yields an exact Gaussian
endpoint disintegration against the genuine passage-time law. No pinned
bridge minimum-time decomposition or excursion identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageEndpointJointLaw

open BrownianPathLaw BrownianFirstPassageUncappedLaw BrownianFirstPassageStrongMarkovFull
open BrownianFirstPassageEndpointGeometry

theorem time_future_jointLaw (level : ℝ) (hlevel : level < 0) :
    pathLaw.map (fun f ↦ (realTime level f,passageFuture level f)) =
      (timeLaw level).prod pathLaw := by
  let π : ℝ≥0 × Path → ℝ := fun p ↦ (p.1 : ℝ)
  have hπ : Measurable π := NNReal.continuous_coe.measurable.comp measurable_fst
  have he := congrArg (Measure.map (Prod.map π (id : Path → Path)))
    (passage_jointLaw level hlevel)
  rw [Measure.map_map (hπ.prodMap measurable_id)
    ((measurable_passagePast level).prodMk (measurable_passageFuture level)),
    ← Measure.map_prod_map _ _ hπ measurable_id,Measure.map_id,
    Measure.map_map hπ (measurable_passagePast level)] at he
  exact he

theorem restricted_time_future_jointLaw (level : ℝ) (hlevel : level < 0) (T : ℝ≥0) :
    (pathLaw.restrict {f : Path | realTime level f < (T : ℝ)}).map
      (fun f ↦ (realTime level f,passageFuture level f)) =
      ((timeLaw level).restrict (Iio (T : ℝ))).prod pathLaw := by
  have hm := (measurable_realTime level).prodMk (measurable_passageFuture level)
  have hset : MeasurableSet ((Iio (T : ℝ)) ×ˢ (univ : Set Path)) :=
    measurableSet_Iio.prod MeasurableSet.univ
  have hr := Measure.restrict_map (μ := pathLaw) hm hset
  rw [time_future_jointLaw level hlevel,← Measure.restrict_prod_eq_prod_univ] at hr
  have hp : (fun f : Path ↦ (realTime level f,passageFuture level f)) ⁻¹'
      ((Iio (T : ℝ)) ×ˢ (univ : Set Path)) = {f : Path | realTime level f < (T : ℝ)} := by
    ext f
    simp only [mem_preimage,mem_prod,mem_Iio,mem_univ,and_true,mem_ofPred_eq]
  rw [hp] at hr
  exact hr.symm

theorem actual_endpoint_jointLaw (level : ℝ) (hlevel : level < 0) (T : ℝ≥0) :
    (pathLaw.restrict {f : Path | realTime level f < (T : ℝ)}).map
      (fun f ↦ (realTime level f,f T)) =
      (((timeLaw level).restrict (Iio (T : ℝ))).prod pathLaw).map (endpointMap level T) := by
  have hH : MeasurableSet {f : Path | realTime level f < (T : ℝ)} :=
    (measurable_realTime level) measurableSet_Iio
  have he : (fun f : Path ↦ (realTime level f,f T)) =ᵐ[
      pathLaw.restrict {f : Path | realTime level f < (T : ℝ)}]
      (endpointMap level T) ∘ (fun f ↦ (realTime level f,passageFuture level f)) := by
    filter_upwards [ae_restrict_of_ae (ae_endpoint_reconstruction level hlevel T),
      ae_restrict_mem hH] with f hf hmem
    exact Prod.ext rfl (hf hmem).symm
  rw [Measure.map_congr he,← Measure.map_map (continuous_endpointMap level T).measurable
    ((measurable_realTime level).prodMk (measurable_passageFuture level)),
    restricted_time_future_jointLaw level hlevel T]

theorem actual_endpoint_lintegral (level : ℝ) (hlevel : level < 0) (T : ℝ≥0)
    (Φ : ℝ × ℝ → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ f in {f : Path | realTime level f < (T : ℝ)}, Φ (realTime level f,f T) ∂pathLaw) =
      ∫⁻ s in Iio (T : ℝ), ∫⁻ z, Φ (s,z) ∂gaussianReal level (remainingTime T s)
        ∂timeLaw level := by
  have hm := (measurable_realTime level).prodMk (continuous_eval T).measurable
  rw [← lintegral_map hΦ hm,actual_endpoint_jointLaw level hlevel T,
    lintegral_map hΦ (continuous_endpointMap level T).measurable,
    lintegral_prod (fun p ↦ Φ (endpointMap level T p))
      (hΦ.comp (continuous_endpointMap level T).measurable).aemeasurable]
  apply lintegral_congr
  intro s
  have hΦs : Measurable (fun z : ℝ ↦ Φ (s,z)) := hΦ.comp (measurable_const.prodMk measurable_id)
  have hms : Measurable (fun g : Path ↦ futureEndpoint level T (s,g)) :=
    (continuous_futureEndpoint level T).measurable.comp (measurable_const.prodMk measurable_id)
  change (∫⁻ g, Φ (s,futureEndpoint level T (s,g)) ∂pathLaw) = _
  rw [← lintegral_map hΦs hms,futureEndpoint_gaussianLaw]

end PerronWright.BrownianFirstPassageEndpointJointLaw
