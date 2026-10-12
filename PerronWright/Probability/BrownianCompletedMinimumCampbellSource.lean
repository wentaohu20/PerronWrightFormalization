import PerronWright.Probability.BrownianParabolicMinimumCompletedPassageLaw
import PerronWright.Probability.BrownianCompletedMinimumDeletionSource
import PerronWright.Probability.BrownianExcursionOccupationCampbell

/-! # Actual complete-state Campbell source at the minimum anchor

The nonrepeating genuine excursion section is exchanged with inverse-
length time occupation. At each positive deterministic anchor the literal
component endpoint state equals the proved completed minimum state. Thus
the complete excursion and the entire deleted driver can remain in Borel
tests, without assuming a Palm or conditional shape identity.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedMinimumCampbellSource

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open BrownianFirstPassagePastFibers ContinuousPathLeastMinimum
open FullHorizonExcursionComponents FullHorizonExcursionEndpoints FullHorizonExcursionSection
open BrownianExcursionOccupationCampbell BrownianParabolicExcursionAnchor
open BrownianParabolicCompletedMinimumSource ContinuousPathMinimumSplitBandAverage
open BrownianMinimumFutureReturnPathGeometry BrownianMinimumFutureFirstReturn
open BrownianExcursionDeletionGeometry BrownianMinimumPointReturnAnchor
open BrownianParabolicMinimumCompletedPassageLaw BrownianParabolicDriftTiltGeometry
open BrownianParabolicFirstPassageStoppedTiltFull BrownianMinimumFutureScaledStrongMarkov
open BrownianFullHorizonExcursionAreas BrownianBridgeCyclicArea BrownianKilledAreaGeometry
open BrownianExcursionDeletionDensity BrownianCompletedMinimumDeletionSource
open ContinuousPathIntervalDeletion

def endpointState (lambda : ℝ) (z : Path × ℝ × ℝ) : CompletedState :=
  let s := Real.toNNReal z.2.1
  let l := Real.toNNReal z.2.2
  let g := driftPath lambda z.1
  ((s,pastPath s g),g s,(l,pastPath l (futurePath s g)),futurePath (s+l) g)

theorem measurable_endpointState (lambda : ℝ) : Measurable (endpointState lambda) := by
  have hs : Measurable (fun z : Path × ℝ × ℝ ↦ Real.toNNReal z.2.1) := measurable_snd.fst.real_toNNReal
  have hl : Measurable (fun z : Path × ℝ × ℝ ↦ Real.toNNReal z.2.2) := measurable_snd.snd.real_toNNReal
  have hg : Measurable (fun z : Path × ℝ × ℝ ↦ driftPath lambda z.1) :=
    (BrownianParabolicFirstPassagePastFibers.measurable_actual_driftPath lambda).comp measurable_fst
  have hfuture := continuous_joint_futurePath.measurable.comp (hs.prodMk hg)
  exact (hs.prodMk (continuous_joint_pastPath.measurable.comp (hs.prodMk hg))).prodMk
    ((continuous_joint_eval.measurable.comp (hg.prodMk hs)).prodMk
      ((hl.prodMk (continuous_joint_pastPath.measurable.comp (hl.prodMk hfuture))).prodMk
        (continuous_joint_futurePath.measurable.comp ((hs.add hl).prodMk hg))))

def componentState (lambda : ℝ) (q : ℝ) (f : Path) : CompletedState :=
  endpointState lambda (f,leftEndpoint q (driftedReflectionPath lambda f),
    length q (driftedReflectionPath lambda f))

theorem measurable_componentState (lambda q : ℝ) : Measurable (componentState lambda q) :=
  (measurable_endpointState lambda).comp (measurable_id.prodMk
    (((measurable_leftEndpoint q).comp (measurable_driftedReflectionPath lambda)).prodMk
      ((measurable_length q).comp (measurable_driftedReflectionPath lambda))))

theorem completeArea_componentState (lambda q : ℝ) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hb : BddAbove (component (driftedReflectionPath lambda f) q)) :
    completeArea (componentState lambda q f) = (excursionArea q lambda f : ℝ) := by
  have hl : Real.toNNReal (length q (driftedReflectionPath lambda f)) = cutLength q lambda f := by
    rw [← cutLength_eq_length q lambda f hq hb,Real.toNNReal_coe]
  have hab : leftTime q lambda f ≤ rightTime q lambda f := by
    apply NNReal.coe_le_coe.mp
    rw [coe_leftTime,coe_rightTime]
    exact ((endpoint_bounds hq hb).2.1.trans (endpoint_bounds hq hb).2.2).le
  have he : leftTime q lambda f+cutLength q lambda f = rightTime q lambda f :=
    add_tsub_cancel_of_le hab
  have hc : (cutLength q lambda f : ℝ) =
      (rightTime q lambda f : ℝ)-(leftTime q lambda f : ℝ) := NNReal.coe_sub hab
  change pathArea (Real.toNNReal (length q (driftedReflectionPath lambda f)))
    (pastPath (Real.toNNReal (length q (driftedReflectionPath lambda f)))
      (futurePath (leftTime q lambda f) (driftPath lambda f))) = _
  rw [pathArea_past,hl]
  have hsegment := pathArea_future_segment (leftTime q lambda f) (cutLength q lambda f)
    (driftPath lambda f)
  rw [he,hc] at hsegment
  have hremoved := actual_removed_driver_integral q lambda f hq hb
  linarith

theorem remainingDriver_componentState (lambda q : ℝ) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hb : BddAbove (component (driftedReflectionPath lambda f) q)) :
    remainingDriver (componentState lambda q f) =
      driftPath (deletedParameter q lambda f) (deletedPath q lambda f) := by
  have hl : Real.toNNReal (length q (driftedReflectionPath lambda f)) = cutLength q lambda f := by
    rw [← cutLength_eq_length q lambda f hq hb,Real.toNNReal_coe]
  change splicePath (leftTime q lambda f)
    (pastPath (leftTime q lambda f) (driftPath lambda f),
      futurePath (leftTime q lambda f+Real.toNNReal (length q (driftedReflectionPath lambda f)))
        (driftPath lambda f)) = _
  rw [hl,← splice_past_future_after_cut,parabolic_deletion_eq]
  rfl

theorem ae_componentState_eq_completion (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f : Path ∂pathLaw, componentState lambda (T : ℝ) f =
      completion (minimumPoint T (driftPath lambda f)) := by
  filter_upwards [ae_actual_parabolic_anchor_endpoints lambda T hT,
    ae_actual_parabolic_component_bddAbove lambda (T : ℝ),
    ae_actual_parabolic_completion lambda T hT] with f ha hb hr
  have hs : Real.toNNReal (leftEndpoint (T : ℝ) (driftedReflectionPath lambda f)) =
      leastMinimizer T (driftPath lambda f) := by
    rw [ha.2.1,Real.toNNReal_coe]
  have hl : Real.toNNReal (length (T : ℝ) (driftedReflectionPath lambda f)) =
      cutLength (T : ℝ) lambda f := by
    rw [← cutLength_eq_length (T : ℝ) lambda f ha.1 hb,Real.toNNReal_coe]
  have he : driftPath lambda f (leastMinimizer T (driftPath lambda f)) =
      minimumValue T (driftPath lambda f) := leastMinimizer_value _ _
  unfold componentState endpointState completion minimumPoint returnTaggedPast returnFuturePath
  dsimp only
  rw [hs,hl,← hr.1,he,futurePath_add]
  rfl

theorem actual_completed_campbell_inverse_length (lambda : ℝ)
    (Ψ : CompletedState → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∑' q : ℚ, ∫⁻ f : Path,
      if Representative (driftedReflectionPath lambda f) q then
        Ψ (componentState lambda (q : ℝ) f) else 0 ∂pathLaw) =
      ∫⁻ t : ℝ in Ioi 0, ∫⁻ f : Path,
        Ψ (completion (minimumPoint (Real.toNNReal t) (driftPath lambda f))) /
          ((completion (minimumPoint (Real.toNNReal t) (driftPath lambda f))).2.2.1.1 : ℝ≥0∞)
            ∂pathLaw := by
  let H : Path × ℝ × ℝ → ℝ≥0∞ := fun z ↦ Ψ (endpointState lambda z)
  have hH : Measurable H := hΨ.comp (measurable_endpointState lambda)
  change (∑' q : ℚ, ∫⁻ f : Path,
    if Representative (driftedReflectionPath lambda f) q then
      H (f,leftEndpoint (q : ℝ) (driftedReflectionPath lambda f),
        length (q : ℝ) (driftedReflectionPath lambda f)) else 0 ∂pathLaw) = _
  rw [← actual_campbell_inverse_length lambda H hH]
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro t
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    let T := Real.toNNReal t
    have hT : 0 < T := Real.toNNReal_pos.mpr ht
    have htT : (T : ℝ) = t := Real.coe_toNNReal t ht.le
    apply lintegral_congr_ae
    filter_upwards [ae_actual_parabolic_anchor_endpoints lambda T hT,
      ae_actual_parabolic_component_bddAbove lambda t,
      ae_componentState_eq_completion lambda T hT,
      ae_actual_parabolic_completion lambda T hT] with f ha hb hs hr
    have hq : t ∈ positiveSet (driftedReflectionPath lambda f) := htT ▸ ha.1
    have hl : ENNReal.ofReal (length t (driftedReflectionPath lambda f)) =
        ((completion (minimumPoint T (driftPath lambda f))).2.2.1.1 : ℝ≥0∞) := by
      rw [hr.1,htT]
      have hlen := cutLength_eq_length (T : ℝ) lambda f ha.1 (by rwa [htT] :
        BddAbove (component (driftedReflectionPath lambda f) (T : ℝ)))
      rw [htT] at hlen
      rw [← hlen,ENNReal.ofReal_coe_nnreal]
    change FullHorizonExcursionOccupation.occupation
      (fun p ↦ H p / ENNReal.ofReal p.2.2) f (driftedReflectionPath lambda f) t = _
    rw [FullHorizonExcursionOccupation.occupation,if_pos hq,hl]
    change Ψ (componentState lambda t f) / _ = _
    rw [← htT,hs,Real.toNNReal_coe]
  · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
    have he (f : Path) : occupation lambda (fun p ↦ H p / ENNReal.ofReal p.2.2) (f,t) = 0 := by
      have hq : t ∉ positiveSet (driftedReflectionPath lambda f) := fun h ↦ ht h.1
      simp only [occupation,FullHorizonExcursionOccupation.occupation,if_neg hq]
    simp only [he,lintegral_zero]

theorem actual_completed_campbell_passage_source_lintegral (lambda : ℝ)
    (Ψ : CompletedState → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∑' q : ℚ, ∫⁻ f : Path,
      if Representative (driftedReflectionPath lambda f) q then
        Ψ (componentState lambda (q : ℝ) f) else 0 ∂pathLaw) =
      ∫⁻ t : ℝ in Ioi 0, ∫⁻ a : ℝ in Ioi 0,
        ∫⁻ p in {p : ℝ≥0 × Path | p.1 < Real.toNNReal t},
          (ENNReal.ofReal BrownianMinimumSplitCandidate.entranceCoefficient*
            ENNReal.ofReal (1/Real.sqrt (t-(p.1 : ℝ))))*
            (∫⁻ q : ℝ≥0 × Path, density (lambda-(p.1 : ℝ)) q.1 q.2*
              (∫⁻ h : Path,
                Ψ (p,-a,q,driftPath (lambda-(p.1 : ℝ)-(q.1 : ℝ)) h)/(q.1 : ℝ≥0∞) ∂pathLaw)
                ∂(sourceLaw (Real.toNNReal t-p.1)).map returnTaggedPast)
              ∂pathLaw.map (actualDriverPassagePast lambda (-a)) := by
  rw [actual_completed_campbell_inverse_length lambda Ψ hΨ]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  let Φ : CompletedState → ℝ≥0∞ := fun q ↦ Ψ q/(q.2.2.1.1 : ℝ≥0∞)
  have hΦ : Measurable Φ := hΨ.div measurable_snd.snd.fst.fst.coe_nnreal_ennreal
  have he := actual_parabolic_completed_passage_source_lintegral lambda (Real.toNNReal t)
    (Real.toNNReal_pos.mpr ht) Φ hΦ
  simpa only [Φ,Real.coe_toNNReal t ht.le] using he

end PerronWright.BrownianCompletedMinimumCampbellSource
