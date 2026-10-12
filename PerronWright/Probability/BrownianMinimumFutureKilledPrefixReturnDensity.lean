import PerronWright.Probability.BrownianKilledPrefixFirstPassageJointDensity
import PerronWright.Probability.BrownianMinimumFutureReturnPathGeometry
import PerronWright.Probability.BrownianMinimumFuturePrefixTests

/-! # Actual entrance-source observations before the completed return

The actual unit prefix is retained together with ordered post-unit samples
and the literal positive-time return. The fresh Brownian future supplies
the killed transition chain and the final true first-hit density. Applying
the proved prefix law also gives the full entrance/killed/first-hit chain.
No conditional excursion law or return-density interface is a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumFutureKilledPrefixReturnDensity

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassageEndpointGeometry BrownianMinimumFutureEntranceSource
open BrownianMinimumFuturePostUnit BrownianMinimumFutureFirstReturn
open BrownianMinimumFutureReturnPathGeometry BrownianMinimumFuturePrefixTests
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledPrefixFirstPassageJointDensity BrownianKilledFreeEntranceTests
open BrownianKilledFreeEntranceGeometry

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

private def postCoordinates (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (q : Path × Path) : FreeVector (n+1) := fun i ↦ q.1 1+q.2 (times i.succ)

private theorem measurable_postCoordinates (n : ℕ) (times : Fin (n+2) → ℝ≥0) :
    Measurable (postCoordinates n times) :=
  measurable_pi_lambda _ (fun _ ↦
    ((continuous_eval 1).measurable.comp measurable_fst).add
      ((continuous_eval _).measurable.comp measurable_snd))

private theorem measurable_joint_realTime : Measurable (fun q : ℝ × Path ↦ realTime q.1 q.2) :=
  NNReal.continuous_coe.measurable.comp measurable_joint_firstPassage.ennreal_toNNReal

private def postSurvival (T : ℝ≥0) : Set (Path × Path) :=
  {q | q.2 ∈ survival (-q.1 1) T}

private theorem measurableSet_postSurvival (T : ℝ≥0) : MeasurableSet (postSurvival T) := by
  have hm : Measurable (fun q : Path × Path ↦ firstPassage (-q.1 1) q.2) :=
    measurable_joint_firstPassage.comp
      (((continuous_eval 1).measurable.comp measurable_fst).neg.prodMk measurable_snd)
  have hs : MeasurableSet {q : Path × Path | (T : ℝ≥0∞) < firstPassage (-q.1 1) q.2} :=
    measurableSet_lt measurable_const hm
  convert hs using 1
  exact Set.ext (fun q ↦ mem_survival_iff_firstPassage (-q.1 1) T q.2)

private def sourceSurvival (T : ℝ≥0) : Set Path :=
  {g | futurePath 1 g ∈ survival (-g 1) T}

private theorem measurableSet_sourceSurvival (T : ℝ≥0) : MeasurableSet (sourceSurvival T) := by
  have hm := (measurable_pastPath 1).prodMk (measurable_futurePath 1)
  have h := hm (measurableSet_postSurvival T)
  simpa only [postSurvival,sourceSurvival,Set.preimage_ofPred_eq,pastPath_eval,min_self] using h

private theorem return_event_eq (T : ℝ≥0) :
    {g : Path | ((1+T : ℝ≥0) : ℝ≥0∞) < firstReturnZero g} =ᵐ[unitSourceLaw]
      sourceSurvival T := by
  filter_upwards [ae_unitSourceLaw_firstReturn_eq] with g hg
  change (((1+T : ℝ≥0) : ℝ≥0∞) < firstReturnZero g) =
    (futurePath 1 g ∈ survival (-g 1) T)
  rw [hg,ENNReal.coe_add,ENNReal.coe_one,
    ENNReal.add_lt_add_iff_left (by norm_num),mem_survival_iff_firstPassage]

private theorem return_real_eq :
    ∀ᵐ g : Path ∂unitSourceLaw,
      (firstReturnZero g).toReal = 1+realTime (-g 1) (futurePath 1 g) := by
  filter_upwards [ae_returnTime_eq_post_unit_passage] with g hg
  change ((firstReturnZero g).toNNReal : ℝ) =
    1+(BrownianFirstPassageUncappedLaw.passageTime (-g 1) (futurePath 1 g) : ℝ)
  exact_mod_cast hg

theorem actual_prefix_postUnit_return_lintegral (n : ℕ)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (H : Path × (FreeVector (n+1) × ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ g in {g : Path | ((1+times (Fin.last (n+1)) : ℝ≥0) : ℝ≥0∞) < firstReturnZero g},
      H (pastPath 1 g,((fun i : Fin (n+1) ↦ g (1+times i.succ)),
        (firstReturnZero g).toReal)) ∂unitSourceLaw) =
      ∫⁻ p : Path, (∫⁻ v : FreeVector (n+1),
        jointDensity (n+1) (p 1) (orderedGaps (n+1) times) v*
          (∫⁻ s in Ioi (times (Fin.last (n+1)) : ℝ),
            BrownianFirstPassageDensityGeometry.density (v (Fin.last n))
              (s-(times (Fin.last (n+1)) : ℝ))*H (p,(v,1+s))))
                ∂unitSourceLaw.map (pastPath 1) := by
  let T := times (Fin.last (n+1))
  let μ := unitSourceLaw.map (pastPath 1)
  let : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (measurable_pastPath 1).aemeasurable
  let J : Path × Path → ℝ≥0∞ := fun q ↦ H (q.1,
    (postCoordinates n times q,1+realTime (-q.1 1) q.2))
  have hJ : Measurable J := hH.comp (measurable_fst.prodMk
    ((measurable_postCoordinates n times).prodMk (measurable_const.add
      (measurable_joint_realTime.comp
        (((continuous_eval 1).measurable.comp measurable_fst).neg.prodMk measurable_snd)))))
  let F := (postSurvival T).indicator J
  have hF : Measurable F := hJ.indicator (measurableSet_postSurvival T)
  have hj := (measurable_pastPath 1).prodMk (measurable_futurePath 1)
  have hp : ∀ᵐ p : Path ∂μ, 0 < p 1 := by
    apply (ae_map_iff (measurable_pastPath 1).aemeasurable
      (measurableSet_lt measurable_const (continuous_eval 1).measurable)).mpr
    simpa only [pastPath_eval,min_self] using ae_unitSourceLaw_endpoint_pos
  calc
    _ = ∫⁻ g in sourceSurvival T,
        H (pastPath 1 g,((fun i : Fin (n+1) ↦ g (1+times i.succ)),
          1+realTime (-g 1) (futurePath 1 g))) ∂unitSourceLaw := by
      rw [Measure.restrict_congr_set (return_event_eq T)]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae return_real_eq] with g hg
      rw [hg]
    _ = ∫⁻ g : Path, F (pastPath 1 g,futurePath 1 g) ∂unitSourceLaw := by
      rw [← lintegral_indicator (measurableSet_sourceSurvival T)]
      apply lintegral_congr
      intro g
      have he : postCoordinates n times (pastPath 1 g,futurePath 1 g) =
          fun i : Fin (n+1) ↦ g (1+times i.succ) := by
        funext i
        simp only [postCoordinates,pastPath_eval,min_self,futurePath_eval,add_sub_cancel]
      by_cases hs : g ∈ sourceSurvival T
      · have ht : (pastPath 1 g,futurePath 1 g) ∈ postSurvival T := by
          simpa only [postSurvival,sourceSurvival,Set.mem_ofPred_eq,pastPath_eval,min_self] using hs
        rw [indicator_of_mem hs,show F (pastPath 1 g,futurePath 1 g) =
          J (pastPath 1 g,futurePath 1 g) from indicator_of_mem ht J]
        simp only [J,he,pastPath_eval,min_self]
      · have ht : (pastPath 1 g,futurePath 1 g) ∉ postSurvival T := by
          simpa only [postSurvival,sourceSurvival,Set.mem_ofPred_eq,pastPath_eval,min_self] using hs
        rw [indicator_of_notMem hs,show F (pastPath 1 g,futurePath 1 g) = 0 from
          indicator_of_notMem ht J]
    _ = ∫⁻ p : Path, ∫⁻ g : Path, F (p,g) ∂pathLaw ∂μ := by
      rw [← lintegral_map hF hj,actual_source_past_future_jointLaw,
        lintegral_prod _ hF.aemeasurable]
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hp] with p hpos
      have ht := actual_ordered_prefix_firstPassage_lintegral n (p 1) hpos times hstrict hzero
        (fun q ↦ H (p,(q.1,1+q.2)))
        (hH.comp (measurable_const.prodMk (measurable_fst.prodMk
          (measurable_const.add measurable_snd))))
      rw [← lintegral_indicator (measurableSet_survival (-p 1) T)] at ht
      exact ht

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem measurable_joint_initial_density (n : ℕ) (gaps : ℕ → ℝ≥0) :
    Measurable (fun q : ℝ × FreeVector n ↦ jointDensity n q.1 gaps q.2) := by
  have hprep : Measurable (fun q : ℝ × FreeVector n ↦ prependInitial n q.1 q.2) := by
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa only [prependInitial,Fin.cons_zero] using measurable_fst
    · simpa only [prependInitial,Fin.cons_succ,Function.comp_def] using
        (measurable_pi_apply j).comp measurable_snd
  unfold jointDensity
  have hp (i : Fin n) : Measurable (fun q : ℝ × FreeVector n ↦
      prependInitial n q.1 q.2 i.castSucc) :=
    (measurable_pi_apply i.castSucc).comp hprep
  have hv (i : Fin n) : Measurable (fun q : ℝ × FreeVector n ↦ q.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hi (i : Fin n) : Measurable (fun q : ℝ × FreeVector n ↦
      BrownianPositiveKilledEndpoint.density (prependInitial n q.1 q.2 i.castSucc)
        (gaps i.val) (q.2 i)) := by
    have hpair : Measurable (fun q : ℝ × FreeVector n ↦
        (prependInitial n q.1 q.2 i.castSucc,q.2 i)) := (hp i).prodMk (hv i)
    simpa only [Function.comp_def] using
      (BrownianPositiveKilledKernel.measurable_joint_density (gaps i.val)).comp hpair
  exact Finset.measurable_prod (f := fun (i : Fin n) (q : ℝ × FreeVector n) ↦
    BrownianPositiveKilledEndpoint.density (prependInitial n q.1 q.2 i.castSucc)
      (gaps i.val) (q.2 i)) Finset.univ (fun i _ ↦ hi i)

private def mixedKernel (k n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (G : FreeVector (k+1) × (FreeVector (n+1) × ℝ) → ℝ≥0∞)
    (u : FreeVector (k+1)) : ℝ≥0∞ :=
  ∫⁻ v : FreeVector (n+1), jointDensity (n+1) (u (Fin.last k)) (orderedGaps (n+1) times) v*
    (∫⁻ s in Ioi (times (Fin.last (n+1)) : ℝ),
      BrownianFirstPassageDensityGeometry.density (v (Fin.last n))
        (s-(times (Fin.last (n+1)) : ℝ))*G (u,(v,1+s)))

private theorem measurable_mixedKernel (k n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (G : FreeVector (k+1) × (FreeVector (n+1) × ℝ) → ℝ≥0∞) (hG : Measurable G) :
    Measurable (mixedKernel k n times G) := by
  have hv : Measurable (fun v : FreeVector (n+1) ↦ v (Fin.last n)) := measurable_pi_apply _
  have hp : Measurable (fun q : (FreeVector (k+1) × FreeVector (n+1)) × ℝ ↦
      (q.1.2 (Fin.last n),q.2-(times (Fin.last (n+1)) : ℝ))) :=
    (hv.comp (measurable_snd.comp measurable_fst)).prodMk (measurable_snd.sub_const _)
  have hj : Measurable (fun q : (FreeVector (k+1) × FreeVector (n+1)) × ℝ ↦
      (q.1.1,(q.1.2,1+q.2))) :=
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_const.add measurable_snd)))
  have htest : Measurable (fun q : (FreeVector (k+1) × FreeVector (n+1)) × ℝ ↦
      G (q.1.1,(q.1.2,1+q.2))) := by
    simpa only [Function.comp_def] using hG.comp hj
  have hdp : Measurable (fun q : (FreeVector (k+1) × FreeVector (n+1)) × ℝ ↦
      BrownianFirstPassageDensityGeometry.density (q.1.2 (Fin.last n))
        (q.2-(times (Fin.last (n+1)) : ℝ))) := by
    simpa only [Function.comp_def] using BrownianHeatResolvent.measurable_joint_passageDensity.comp hp
  have hm : Measurable (fun q : (FreeVector (k+1) × FreeVector (n+1)) × ℝ ↦
      BrownianFirstPassageDensityGeometry.density (q.1.2 (Fin.last n))
        (q.2-(times (Fin.last (n+1)) : ℝ))*G (q.1.1,(q.1.2,1+q.2))) := by
    simpa only [Function.comp_def] using measurable_mul.comp (hdp.prodMk htest)
  have hi := hm.lintegral_prod_right' (ν := volume.restrict (Ioi (times (Fin.last (n+1)) : ℝ)))
  have hu : Measurable (fun u : FreeVector (k+1) ↦ u (Fin.last k)) := measurable_pi_apply _
  have hd : Measurable (fun q : FreeVector (k+1) × FreeVector (n+1) ↦
      jointDensity (n+1) (q.1 (Fin.last k)) (orderedGaps (n+1) times) q.2) := by
    simpa only [Function.comp_def] using
      (measurable_joint_initial_density (n+1) (orderedGaps (n+1) times)).comp
        ((hu.comp measurable_fst).prodMk measurable_snd)
  have hprod : Measurable (fun q : FreeVector (k+1) × FreeVector (n+1) ↦
      jointDensity (n+1) (q.1 (Fin.last k)) (orderedGaps (n+1) times) q.2*
        (∫⁻ s in Ioi (times (Fin.last (n+1)) : ℝ),
          BrownianFirstPassageDensityGeometry.density (q.2 (Fin.last n))
            (s-(times (Fin.last (n+1)) : ℝ))*G (q.1,(q.2,1+s)))) := by
    simpa only [Function.comp_def] using measurable_mul.comp (hd.prodMk hi)
  unfold mixedKernel
  exact hprod.lintegral_prod_right' (ν := volume)

theorem actual_mixed_ordered_return_lintegral (k n : ℕ)
    (prefixTimes : Fin (k+2) → ℝ≥0) (hprefix : StrictMono prefixTimes)
    (hprefixzero : prefixTimes 0 = 0) (hprefixlast : prefixTimes (Fin.last (k+1)) = 1)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (G : FreeVector (k+1) × (FreeVector (n+1) × ℝ) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ g in {g : Path | ((1+times (Fin.last (n+1)) : ℝ≥0) : ℝ≥0∞) < firstReturnZero g},
      G ((fun i : Fin (k+1) ↦ g (prefixTimes i.succ)),
        ((fun i : Fin (n+1) ↦ g (1+times i.succ)),(firstReturnZero g).toReal)) ∂unitSourceLaw) =
      (∫⁻ u : FreeVector (k+1), entranceJoint k (orderedGaps (k+1) prefixTimes) u*
        (∫⁻ v : FreeVector (n+1), jointDensity (n+1) (u (Fin.last k)) (orderedGaps (n+1) times) v*
          (∫⁻ s in Ioi (times (Fin.last (n+1)) : ℝ),
            BrownianFirstPassageDensityGeometry.density (v (Fin.last n))
              (s-(times (Fin.last (n+1)) : ℝ))*G (u,(v,1+s)))))/
                ENNReal.ofReal (Real.sqrt (2/Real.pi)) := by
  let coords : Path → FreeVector (k+1) := fun p ↦ fun i ↦ p (prefixTimes i.succ)
  have hm : Measurable coords := measurable_pi_lambda _ (fun _ ↦ (continuous_eval _).measurable)
  have he (g : Path) : coords (pastPath 1 g) = coords g := by
    funext i
    have hi : prefixTimes i.succ ≤ 1 := hprefixlast ▸ hprefix.monotone (Fin.le_last i.succ)
    simp only [coords,pastPath_eval,min_eq_left hi]
  let H : Path × (FreeVector (n+1) × ℝ) → ℝ≥0∞ := fun q ↦ G (coords q.1,q.2)
  have hH : Measurable H := hG.comp ((hm.comp measurable_fst).prodMk measurable_snd)
  have h := actual_prefix_postUnit_return_lintegral n times hstrict hzero H hH
  simp only [H,he] at h
  have hc (p : Path) : coords p (Fin.last k) = p 1 := by
    simp only [coords,Fin.succ_last,hprefixlast]
  simp_rw [← hc] at h
  change (∫⁻ g in {g : Path | ((1+times (Fin.last (n+1)) : ℝ≥0) : ℝ≥0∞) < firstReturnZero g},
      G (coords g,((fun i : Fin (n+1) ↦ g (1+times i.succ)),(firstReturnZero g).toReal)) ∂unitSourceLaw) = _
  rw [h]
  have hK := measurable_mixedKernel k n times G hG
  change (∫⁻ p : Path, mixedKernel k n times G (coords p) ∂unitSourceLaw.map (pastPath 1)) = _
  have hKm : Measurable (fun p : Path ↦ mixedKernel k n times G (coords p)) := hK.comp hm
  rw [lintegral_map hKm (measurable_pastPath 1)]
  simp only [he]
  rw [unitSource_prefix_borel_test k prefixTimes hprefix hprefixzero hprefixlast _ hK,
    freeEntranceLaw,lintegral_withDensity_eq_lintegral_mul volume (measurable_entranceJoint k _) hK]
  rfl

end PerronWright.BrownianMinimumFutureKilledPrefixReturnDensity
