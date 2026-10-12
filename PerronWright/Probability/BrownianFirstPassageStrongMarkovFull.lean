import PerronWright.Probability.BrownianFirstPassageUncappedLaw
import PerronWright.Probability.BrownianFirstPassageZeroDrift

/-! # Actual whole-future Brownian law at a negative first-passage level

The true first passage is almost surely finite by the proved survival
tail estimate. Thus the uncapped product-law argument has no additional
finiteness or strong-Markov hypothesis in any terminal theorem below.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFirstPassageStrongMarkovFull

open BrownianPathLaw ContinuousPathFirstPassage
open BrownianFirstPassageUncappedLaw BrownianFirstPassageZeroDrift

theorem passage_jointLaw (level : ℝ) (hlevel : level < 0) :
    pathLaw.map (fun f ↦ (passagePast level f,passageFuture level f)) =
      (pathLaw.map (passagePast level)).prod pathLaw :=
  passage_jointLaw_of_ae_finite level (ae_firstPassage_ne_top level hlevel)

theorem passageFuture_law (level : ℝ) (hlevel : level < 0) :
    pathLaw.map (passageFuture level) = pathLaw := by
  have hp := measurable_passagePast level
  have hf := measurable_passageFuture level
  let : IsProbabilityMeasure (pathLaw.map (passagePast level)) :=
    Measure.isProbabilityMeasure_map hp.aemeasurable
  have he := congrArg (Measure.map Prod.snd) (passage_jointLaw level hlevel)
  rw [Measure.map_map measurable_snd (hp.prodMk hf),Measure.map_snd_prod,
    measure_univ,one_smul] at he
  exact he

theorem passagePast_future_independent (level : ℝ) (hlevel : level < 0) :
    IndepFun (passagePast level) (passageFuture level) pathLaw := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_passagePast level).aemeasurable
    (measurable_passageFuture level).aemeasurable).mpr
  rw [passageFuture_law level hlevel]
  exact passage_jointLaw level hlevel

theorem ae_passageTime_coe_eq (level : ℝ) (hlevel : level < 0) :
    ∀ᵐ f ∂pathLaw, (passageTime level f : ℝ≥0∞) = firstPassage level f := by
  filter_upwards [ae_firstPassage_ne_top level hlevel] with f hf
  exact ENNReal.coe_toNNReal hf

theorem passageFuture_lintegral (level : ℝ) (hlevel : level < 0)
    (Ψ : Path → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (passageFuture level f) ∂pathLaw) = ∫⁻ f, Ψ f ∂pathLaw := by
  rw [← lintegral_map hΨ (measurable_passageFuture level),passageFuture_law level hlevel]

theorem passageFuture_integrable_iff (level : ℝ) (hlevel : level < 0)
    (Ψ : Path → ℝ) (hΨ : Measurable Ψ) :
    Integrable (fun f ↦ Ψ (passageFuture level f)) pathLaw ↔ Integrable Ψ pathLaw := by
  have he := integrable_map_measure (μ := pathLaw) hΨ.aestronglyMeasurable
    (measurable_passageFuture level).aemeasurable
  rw [passageFuture_law level hlevel] at he
  exact he.symm

theorem passageFuture_integral (level : ℝ) (hlevel : level < 0)
    (Ψ : Path → ℝ) (hΨ : Measurable Ψ) :
    (∫ f, Ψ (passageFuture level f) ∂pathLaw) = ∫ f, Ψ f ∂pathLaw := by
  rw [← integral_map_of_stronglyMeasurable (measurable_passageFuture level)
    hΨ.stronglyMeasurable,passageFuture_law level hlevel]

end PerronWright.BrownianFirstPassageStrongMarkovFull
