import PerronWright.Probability.BrownianMinimumFutureCompleteReturnTilt
import PerronWright.Probability.BrownianParabolicMinimumSplitPassageLaw
import PerronWright.Probability.BrownianParabolicCompletedMinimumSource

/-! # Actual completed excursion and fresh residual future in the minimum source

The genuine minimum-passage source is disintegrated at the physical complete
return using the proved return density. The minimum stopped driver, depth,
complete stopped excursion, and entire residual future remain in arbitrary
Borel tests. Neither a lifetime-conditioned shape nor a Palm deletion law
is a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianParabolicMinimumCompletedPassageLaw

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open ContinuousPathMinimumSplitBandAverage BrownianPathDilationLaw
open BrownianMinimumFutureEntranceSource BrownianFirstPassageEndpointGeometry
open BrownianMinimumFutureReturnPathGeometry ContinuousPathPositiveReturnMeasurable
open BrownianParabolicWholePathTilt BrownianParabolicDriftTiltGeometry BrownianParabolicStoppedTiltGeometry
open BrownianParabolicMinimumSplitPassageLaw BrownianParabolicFirstPassageStoppedTiltFull
open BrownianMinimumFutureCompleteReturnTilt BrownianMinimumFutureScaledStrongMarkov
open BrownianParabolicCompletedMinimumSource

theorem actual_parabolic_completed_passage_source_lintegral (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (Ψ : CompletedState → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (completion (minimumPoint T (driftPath lambda f))) ∂pathLaw) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        (ENNReal.ofReal BrownianMinimumSplitCandidate.entranceCoefficient*
          ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
          (∫⁻ q : ℝ≥0 × Path, density (lambda-(p.1 : ℝ)) q.1 q.2*
            (∫⁻ h : Path, Ψ (p,-a,q,driftPath (lambda-(p.1 : ℝ)-(q.1 : ℝ)) h) ∂pathLaw)
              ∂(sourceLaw (T-p.1)).map returnTaggedPast)
            ∂pathLaw.map (actualDriverPassagePast lambda (-a)) := by
  have hΦ : Measurable (Ψ ∘ completion) := hΨ.comp measurable_completion
  change (∫⁻ f, (Ψ ∘ completion) (minimumPoint T (driftPath lambda f)) ∂pathLaw) = _
  rw [actual_parabolic_passage_source_lintegral lambda T hT (Ψ ∘ completion) hΦ]
  apply lintegral_congr
  intro a
  have hS : MeasurableSet {p : ℝ≥0 × Path | p.1 < T} := measurable_fst measurableSet_Iio
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hS] with p hp
  have hr : 0 < T-p.1 := tsub_pos_of_lt hp
  have hrem : remainingTime T (p.1 : ℝ) = T-p.1 := by
    rw [remainingTime,← NNReal.coe_sub hp.le,Real.toNNReal_coe]
  let Φ : (ℝ≥0 × Path) × Path → ℝ≥0∞ := fun z ↦ Ψ (p,-a,z.1,z.2)
  have hΦ' : Measurable Φ := hΨ.comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  let L : Path → ℝ≥0∞ := fun g ↦ density (lambda-(p.1 : ℝ)) (T-p.1) g*
    Φ (returnTaggedPast (wholeLift (lambda-(p.1 : ℝ)) (T-p.1) g),
      returnFuturePath (wholeLift (lambda-(p.1 : ℝ)) (T-p.1) g))
  have hL : Measurable L := (measurable_density (lambda-(p.1 : ℝ)) (T-p.1)).mul
    (hΦ'.comp ((measurable_returnTaggedPast.comp (measurable_wholeLift _ _)).prodMk
      (measurable_returnFuturePath.comp (measurable_wholeLift _ _))))
  congr 1
  rw [hrem]
  change (∫⁻ g, L (brownianDilation (T-p.1) g) ∂unitSourceLaw) = _
  rw [← lintegral_map hL (measurable_brownianDilation (T-p.1))]
  change (∫⁻ g, L g ∂sourceLaw (T-p.1)) = _
  exact actual_scaled_source_complete_return_lintegral (lambda-(p.1 : ℝ)) (T-p.1) hr hΦ'

end PerronWright.BrownianParabolicMinimumCompletedPassageLaw
