import PerronWright.Probability.BrownianParabolicFirstPassagePastFibers
import PerronWright.Probability.BrownianFirstPassageGridStrongMarkov

/-! # Genuine Brownian whole-future product law at parabolic grid hitting

The parabolic grid fibers are actual stopped-past events. Restriction
of the proved deterministic Brownian past/future law and summation over
the finite partition prove the literal selected-time product law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicFirstPassageGridStrongMarkov

open BrownianPathLaw BrownianPathIndependentIncrements BrownianFiniteReflectionLaw
open BrownianParabolicFirstPassagePastFibers

theorem parabolic_selected_restrict_jointLaw (lambda level : ℝ) (t : ℕ → ℝ≥0)
    (ht : Monotone t) (m : ℕ) (i : Fin (m+1)) :
    (pathLaw.restrict {f | parabolicGridIndex lambda level t m f = i}).map
      (fun f ↦ (parabolicSelectedPast lambda level t m f,parabolicSelectedFuture lambda level t m f)) =
      ((pathLaw.restrict {f | parabolicGridIndex lambda level t m f = i}).map
        (parabolicSelectedPast lambda level t m)).prod pathLaw := by
  let A : Set Path := {f | parabolicGridIndex lambda level t m f = i}
  have hA : MeasurableSet A := (measurable_parabolicGridIndex lambda level t m)
    (measurableSet_singleton i)
  have hp : (pastPath (t i)) ⁻¹' A = A := by
    ext f
    exact parabolicGridIndex_pastPath_stable lambda level t ht m i f
  have hj := BrownianFirstPassageGridStrongMarkov.fixed_past_future_restrict_jointLaw (t i) A hA
  rw [hp] at hj
  let tag : Path → ℝ≥0 × Path := fun g ↦ (t i,g)
  have htag : Measurable tag := measurable_const.prodMk measurable_id
  have hsp : parabolicSelectedPast lambda level t m =ᵐ[pathLaw.restrict A] tag ∘ pastPath (t i) := by
    filter_upwards [ae_restrict_mem hA] with f hf
    change (t (parabolicGridIndex lambda level t m f),
      pastPath (t (parabolicGridIndex lambda level t m f)) f) = _
    rw [show parabolicGridIndex lambda level t m f = i from hf]
    rfl
  have hsf : parabolicSelectedFuture lambda level t m =ᵐ[pathLaw.restrict A] futurePath (t i) := by
    filter_upwards [ae_restrict_mem hA] with f hf
    change futurePath (t (parabolicGridIndex lambda level t m f)) f = _
    rw [show parabolicGridIndex lambda level t m f = i from hf]
  have hpast := Measure.restrict_map (μ := pathLaw) (measurable_pastPath (t i)) hA
  change (pastLaw (t i)).restrict A = _ at hpast
  rw [hp] at hpast
  change (pathLaw.restrict A).map _ = ((pathLaw.restrict A).map _).prod pathLaw
  rw [Measure.map_congr (hsp.prodMk hsf),Measure.map_congr hsp]
  rw [← Measure.map_map htag (measurable_pastPath (t i)),← hpast]
  have he := congrArg (Measure.map (Prod.map tag (id : Path → Path))) hj
  rw [Measure.map_map (htag.prodMap measurable_id)
    ((measurable_pastPath (t i)).prodMk (measurable_futurePath (t i))),
    ← Measure.map_prod_map _ _ htag measurable_id,Measure.map_id] at he
  exact he

theorem parabolic_selected_jointLaw (lambda level : ℝ) (t : ℕ → ℝ≥0)
    (ht : Monotone t) (m : ℕ) :
    pathLaw.map (fun f ↦ (parabolicSelectedPast lambda level t m f,
      parabolicSelectedFuture lambda level t m f)) =
      (pathLaw.map (parabolicSelectedPast lambda level t m)).prod pathLaw := by
  have hκ := measurable_parabolicGridIndex lambda level t m
  have hj := (measurable_parabolicSelectedPast lambda level t m).prodMk
    (measurable_parabolicSelectedFuture lambda level t m)
  have hμ := law_eq_sum_fibers hκ
  calc
    _ = (Measure.sum (fun i : Fin (m+1) ↦
        pathLaw.restrict {f | parabolicGridIndex lambda level t m f = i})).map
        (fun f ↦ (parabolicSelectedPast lambda level t m f,
          parabolicSelectedFuture lambda level t m f)) := by rw [← hμ]
    _ = Measure.sum (fun i : Fin (m+1) ↦
        ((pathLaw.restrict {f | parabolicGridIndex lambda level t m f = i}).map
          (parabolicSelectedPast lambda level t m)).prod pathLaw) := by
      rw [Measure.map_sum hj.aemeasurable]
      congr 1
      funext i
      exact parabolic_selected_restrict_jointLaw lambda level t ht m i
    _ = (pathLaw.map (parabolicSelectedPast lambda level t m)).prod pathLaw := by
      rw [← Measure.prod_sum_left,
        ← Measure.map_sum (measurable_parabolicSelectedPast lambda level t m).aemeasurable,← hμ]

end PerronWright.BrownianParabolicFirstPassageGridStrongMarkov
