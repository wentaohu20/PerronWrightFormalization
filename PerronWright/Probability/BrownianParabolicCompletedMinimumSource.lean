import PerronWright.Probability.BrownianParabolicMinimumSplitLaw
import PerronWright.Probability.BrownianMinimumPointReturnAnchor
import PerronWright.Probability.ContinuousPathPositiveReturnMeasurable
import PerronWright.Probability.BrownianKilledAreaDuhamelGeometry

/-! # The actual completed excursion in the parabolic minimum source

The positive-time return stops the entire physical future, not merely the
future prefix up to the original horizon. The whole remaining tail is
retained. Its tagged duration and area are proved to be the literal
complete component duration and area under the actual Brownian law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicCompletedMinimumSource

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open ContinuousPathMinimumSplitBandAverage BrownianParabolicMinimumSplitLaw
open BrownianMinimumFutureFirstReturn BrownianMinimumFutureReturnPathGeometry
open ContinuousPathPositiveReturnMeasurable BrownianMinimumPointReturnAnchor
open BrownianBridgeCyclicArea BrownianKilledAreaGeometry BrownianKilledAreaDuhamelGeometry
open BrownianFullHorizonExcursionAreas BrownianExcursionDeletionGeometry

abbrev CompletedState := (ℝ≥0 × Path) × (ℝ × ((ℝ≥0 × Path) × Path))

def completion (z : (ℝ≥0 × Path) × (ℝ × Path)) : CompletedState :=
  (z.1,z.2.1,returnTaggedPast z.2.2,returnFuturePath z.2.2)

theorem measurable_completion : Measurable completion :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk
    (((measurable_returnTaggedPast).comp measurable_snd.snd).prodMk
      ((measurable_returnFuturePath).comp measurable_snd.snd)))

def completeArea (q : CompletedState) : ℝ := pathArea q.2.2.1.1 q.2.2.1.2

theorem measurable_completeArea : Measurable completeArea :=
  measurable_joint_pathArea.comp measurable_snd.snd.fst

theorem completeArea_completion (z : (ℝ≥0 × Path) × (ℝ × Path)) :
    completeArea (completion z) = pathArea (firstReturnZero z.2.2).toNNReal z.2.2 :=
  pathArea_past _ _

theorem ae_actual_parabolic_completion (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f : Path ∂pathLaw,
      let q := completion (minimumPoint T (driftPath lambda f))
      q.2.2.1.1 = cutLength (T : ℝ) lambda f ∧
      q.1.1+q.2.2.1.1 = rightTime (T : ℝ) lambda f ∧
      completeArea q = (excursionArea (T : ℝ) lambda f : ℝ) := by
  filter_upwards [ae_actual_parabolic_minimumFuture_return lambda T hT,
    ae_actual_parabolic_completed_minimumFuture_area lambda T hT,
    BrownianParabolicExcursionAnchor.ae_actual_parabolic_anchor_endpoints lambda T hT,
    ae_actual_parabolic_component_bddAbove lambda (T : ℝ)] with f hr ha hq hb
  dsimp only
  have hlen := cutLength_eq_length (T : ℝ) lambda f hq.1 hb
  have hret : (firstReturnZero (futurePath (ContinuousPathLeastMinimum.leastMinimizer T
      (driftPath lambda f)) (driftPath lambda f))).toNNReal =
        cutLength (T : ℝ) lambda f := by
    rw [hr.1,← hlen,ENNReal.ofReal_coe_nnreal,ENNReal.toNNReal_coe]
  refine ⟨hret,hr.2,?_⟩
  rw [completeArea_completion]
  exact ha

theorem actual_parabolic_completed_law (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (fun f ↦ completion (minimumPoint T (driftPath lambda f))) =
      ((BrownianMinimumSplitCandidate.candidateLaw T).withDensity (splitDensity lambda T)).map
        (completion ∘ liftSplit lambda T) := by
  have hd := BrownianParabolicFirstPassagePastFibers.measurable_actual_driftPath lambda
  have hm := (measurable_minimumPoint T).comp hd
  calc
    _ = (pathLaw.map (fun f ↦ minimumPoint T (driftPath lambda f))).map completion :=
      (Measure.map_map measurable_completion hm).symm
    _ = _ := by
      rw [actual_parabolic_minimum_split_law lambda T hT,
        Measure.map_map measurable_completion (measurable_liftSplit lambda T)]

/-- Arbitrary Borel tests retain the completed physical future and its full
area. This is a proved source formula, not a conditional excursion law. -/
theorem actual_parabolic_complete_area_lintegral (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (Ψ : CompletedState × ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (completion (minimumPoint T (driftPath lambda f)),
      (excursionArea (T : ℝ) lambda f : ℝ)) ∂pathLaw) =
      ∫⁻ z, splitDensity lambda T z*
        Ψ (completion (liftSplit lambda T z),completeArea (completion (liftSplit lambda T z)))
          ∂BrownianMinimumSplitCandidate.candidateLaw T := by
  let F : CompletedState → ℝ≥0∞ := fun q ↦ Ψ (q,completeArea q)
  have hF : Measurable F := hΨ.comp (measurable_id.prodMk measurable_completeArea)
  have hd := BrownianParabolicFirstPassagePastFibers.measurable_actual_driftPath lambda
  have hm := measurable_completion.comp ((measurable_minimumPoint T).comp hd)
  calc
    _ = ∫⁻ f, F (completion (minimumPoint T (driftPath lambda f))) ∂pathLaw := by
      apply lintegral_congr_ae
      filter_upwards [ae_actual_parabolic_completion lambda T hT] with f hf
      exact congrArg (fun a ↦ Ψ (completion (minimumPoint T (driftPath lambda f)),a)) hf.2.2.symm
    _ = ∫⁻ q, F q ∂pathLaw.map (fun f ↦ completion (minimumPoint T (driftPath lambda f))) :=
      (lintegral_map hF hm).symm
    _ = _ := by
      rw [actual_parabolic_completed_law lambda T hT,
        lintegral_map hF (measurable_completion.comp (measurable_liftSplit lambda T))]
      change (∫⁻ z, (F ∘ (completion ∘ liftSplit lambda T)) z
        ∂(BrownianMinimumSplitCandidate.candidateLaw T).withDensity (splitDensity lambda T)) = _
      rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_splitDensity lambda T)
        (hF.comp (measurable_completion.comp (measurable_liftSplit lambda T)))]
      rfl

end PerronWright.BrownianParabolicCompletedMinimumSource
