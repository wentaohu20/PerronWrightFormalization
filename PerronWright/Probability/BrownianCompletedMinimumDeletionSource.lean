import PerronWright.Probability.BrownianParabolicCompletedMinimumSource

/-! # Literal deletion in the actual completed minimum source

The retained minimum past and the future after the physical return
reconstruct the actual compensated deleted driver. The remaining
parabolic parameter is exactly lambda minus the full cut length.
No stochastic deletion or Palm identity is an assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianCompletedMinimumDeletionSource

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open ContinuousPathMinimumSplitBandAverage BrownianParabolicMinimumSplitLaw
open BrownianMinimumFutureFirstReturn BrownianMinimumFutureReturnPathGeometry
open BrownianParabolicCompletedMinimumSource ContinuousPathIntervalDeletion
open BrownianExcursionDeletionGeometry BrownianFullHorizonExcursionAreas

theorem splice_past_future_after_cut (a l : ℝ≥0) (f : Path) :
    deletionPath a l f = splicePath a (pastPath a f,futurePath (a+l) f) := by
  apply ContinuousMap.ext
  intro t
  rw [deletionPath_apply]
  change (if t ≤ a then f t else f (t+l)-f (a+l)+f a) =
    f (min (min t a) a)+(f ((a+l)+(t-a))-f (a+l))
  rw [min_assoc,min_self]
  by_cases ht : t ≤ a
  · simp only [if_pos ht,min_eq_left ht,tsub_eq_zero_of_le ht,add_zero,sub_self,add_zero]
  · have hta : a ≤ t := (le_of_not_ge ht)
    have he : (a+l)+(t-a) = t+l := by
      calc
        _ = (a+(t-a))+l := by ac_rfl
        _ = t+l := by rw [add_tsub_cancel_of_le hta]
    rw [if_neg ht,min_eq_right hta,he]
    ring

def remainingDriver (q : CompletedState) : Path := splicePath q.1.1 (q.1.2,q.2.2.2)

theorem continuous_remainingDriver : Continuous remainingDriver := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_fst.fst.snd.eval (continuous_snd.min continuous_fst.fst.fst)).add
    (continuous_fst.snd.snd.snd.eval (continuous_snd.sub continuous_fst.fst.fst))

theorem measurable_remainingDriver : Measurable remainingDriver := continuous_remainingDriver.measurable

theorem remainingDriver_completion_minimumPoint (T : ℝ≥0) (f : Path) :
    remainingDriver (completion (minimumPoint T f)) =
      deletionPath (ContinuousPathLeastMinimum.leastMinimizer T f)
        (firstReturnZero (futurePath (ContinuousPathLeastMinimum.leastMinimizer T f) f)).toNNReal f := by
  change splicePath (ContinuousPathLeastMinimum.leastMinimizer T f)
    (pastPath (ContinuousPathLeastMinimum.leastMinimizer T f) f,
      futurePath (firstReturnZero (futurePath (ContinuousPathLeastMinimum.leastMinimizer T f) f)).toNNReal
        (futurePath (ContinuousPathLeastMinimum.leastMinimizer T f) f)) = _
  rw [← futurePath_add,← splice_past_future_after_cut]

theorem ae_actual_deleted_driver (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f : Path ∂pathLaw, remainingDriver (completion (minimumPoint T (driftPath lambda f))) =
      driftPath (deletedParameter (T : ℝ) lambda f) (deletedPath (T : ℝ) lambda f) := by
  filter_upwards [ae_actual_parabolic_completion lambda T hT,
    BrownianParabolicExcursionAnchor.ae_actual_parabolic_anchor_endpoints lambda T hT] with f hr ha
  have hs : ContinuousPathLeastMinimum.leastMinimizer T (driftPath lambda f) =
      leftTime (T : ℝ) lambda f := by
    rw [leftTime,ha.2.1,Real.toNNReal_coe]
  have hl : (firstReturnZero (futurePath (ContinuousPathLeastMinimum.leastMinimizer T
      (driftPath lambda f)) (driftPath lambda f))).toNNReal = cutLength (T : ℝ) lambda f := hr.1
  rw [remainingDriver_completion_minimumPoint,hl,hs,parabolic_deletion_eq]
  rfl

theorem actual_complete_area_deleted_driver_lintegral (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (H : CompletedState × (ℝ × Path) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ f, H (completion (minimumPoint T (driftPath lambda f)),
      ((excursionArea (T : ℝ) lambda f : ℝ),
        driftPath (deletedParameter (T : ℝ) lambda f) (deletedPath (T : ℝ) lambda f))) ∂pathLaw) =
      ∫⁻ z, splitDensity lambda T z*H (completion (liftSplit lambda T z),
        (completeArea (completion (liftSplit lambda T z)),
          remainingDriver (completion (liftSplit lambda T z))))
            ∂BrownianMinimumSplitCandidate.candidateLaw T := by
  let Ψ : CompletedState × ℝ → ℝ≥0∞ := fun q ↦ H (q.1,(q.2,remainingDriver q.1))
  have hΨ : Measurable Ψ := hH.comp (measurable_fst.prodMk
    (measurable_snd.prodMk (measurable_remainingDriver.comp measurable_fst)))
  calc
    _ = ∫⁻ f, Ψ (completion (minimumPoint T (driftPath lambda f)),
        (excursionArea (T : ℝ) lambda f : ℝ)) ∂pathLaw := by
      apply lintegral_congr_ae
      filter_upwards [ae_actual_deleted_driver lambda T hT] with f hf
      exact congrArg (fun p ↦ H (completion (minimumPoint T (driftPath lambda f)),
        ((excursionArea (T : ℝ) lambda f : ℝ),p))) hf.symm
    _ = _ := actual_parabolic_complete_area_lintegral lambda T hT Ψ hΨ

end PerronWright.BrownianCompletedMinimumDeletionSource
