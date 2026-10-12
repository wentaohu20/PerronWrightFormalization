import PerronWright.Probability.BrownianMinimumFuturePostUnit

/-! # Exact whole-path reconstruction of the true minimum-future source

The actual source consists of its actual unit prefix and an independent
whole Brownian future. This is a whole compact-open Borel law identity,
derived from the proved product law and literal path splicing.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianMinimumFutureWholeLaw

open BrownianPathLaw BrownianPathIndependentIncrements
open BrownianMinimumFutureEntranceSource BrownianMinimumFuturePostUnit

theorem actual_source_future_law : unitSourceLaw.map (futurePath 1) = pathLaw := by
  let : IsProbabilityMeasure (unitSourceLaw.map (pastPath 1)) :=
    Measure.isProbabilityMeasure_map (measurable_pastPath 1).aemeasurable
  have he := congrArg (Measure.map (Prod.snd : Path × Path → Path))
    actual_source_past_future_jointLaw
  rw [Measure.map_map measurable_snd
    ((measurable_pastPath 1).prodMk (measurable_futurePath 1)),
    Measure.map_snd_prod,measure_univ,one_smul] at he
  exact he

theorem actual_source_whole_splice_law :
    ((unitSourceLaw.map (pastPath 1)).prod pathLaw).map (splicePath 1) = unitSourceLaw := by
  rw [← actual_source_past_future_jointLaw,
    Measure.map_map (measurable_splicePath 1)
      ((measurable_pastPath 1).prodMk (measurable_futurePath 1))]
  have he : splicePath 1 ∘ (fun g : Path ↦ (pastPath 1 g,futurePath 1 g)) = id :=
    funext (fun g ↦ splice_past_future 1 g)
  rw [he,Measure.map_id]

theorem actual_source_whole_lintegral {F : Path → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ g : Path, F g ∂unitSourceLaw) =
      ∫⁻ p : Path, ∫⁻ h : Path, F (splicePath 1 (p,h)) ∂pathLaw
        ∂unitSourceLaw.map (pastPath 1) := by
  let : IsProbabilityMeasure (unitSourceLaw.map (pastPath 1)) :=
    Measure.isProbabilityMeasure_map (measurable_pastPath 1).aemeasurable
  calc
    _ = ∫⁻ g : Path, F g ∂((unitSourceLaw.map (pastPath 1)).prod pathLaw).map
        (splicePath 1) := by rw [actual_source_whole_splice_law]
    _ = ∫⁻ p : Path × Path, F (splicePath 1 p)
        ∂(unitSourceLaw.map (pastPath 1)).prod pathLaw :=
      lintegral_map hF (measurable_splicePath 1)
    _ = _ := lintegral_prod _ (hF.comp (measurable_splicePath 1)).aemeasurable

end PerronWright.BrownianMinimumFutureWholeLaw
