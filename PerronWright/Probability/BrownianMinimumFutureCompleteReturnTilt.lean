import PerronWright.Probability.BrownianParabolicPositivePrefixReturnLaw
import PerronWright.Probability.BrownianMinimumFutureScaledStrongMarkov
import PerronWright.Probability.BrownianParabolicWholePathTilt

/-! # Genuine density at the physical complete entrance return

The physical post-prefix parabolic return is handled by actual negative-
level first passage and its proved stopped-driver density. Only after that
measure change does the density cocycle combine the prefix and the complete
returned path. Thus the density at a prefix is never directly replaced by
the density at a later zero-drift return. Entire fresh residual futures and
arbitrary nonnegative Borel tests are retained throughout.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumFutureCompleteReturnTilt

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open BrownianPathDilationLaw BrownianMinimumFutureEntranceSource BrownianMinimumFuturePostUnit
open BrownianMinimumFutureFirstReturn BrownianMinimumFutureReturnPathGeometry
open ContinuousPathPositiveReturnMeasurable BrownianMinimumFutureScaledStrongMarkov
open BrownianParabolicPositivePrefixReturnLaw BrownianParabolicWholePathTilt
open BrownianParabolicDriftTiltGeometry BrownianParabolicStoppedTiltGeometry
open BrownianParabolicFirstPassageStoppedTilt BrownianParabolicFirstPassageStoppedTiltFull
open BrownianFirstPassageUncappedLaw

private def completeDensity (lambda : ℝ) (p : ℝ≥0 × Path) : ℝ≥0∞ := density lambda p.1 p.2

private theorem measurable_completeDensity (lambda : ℝ) : Measurable (completeDensity lambda) :=
  measurable_joint_density.comp (measurable_const.prodMk measurable_id)

private def residualLift (lambda : ℝ) (z : (ℝ≥0 × Path) × Path) : (ℝ≥0 × Path) × Path :=
  (z.1,driftPath (lambda-(z.1.1 : ℝ)) z.2)

private theorem measurable_residualLift (lambda : ℝ) : Measurable (residualLift lambda) :=
  measurable_fst.prodMk (continuous_driftPath.measurable.comp
    ((measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk measurable_snd))

private theorem past_splice (r : ℝ≥0) (p h : Path) (hzero : h 0 = 0) :
    pastPath r (splicePath r (p,h)) = pastPath r p := by
  apply ContinuousMap.ext
  intro t
  change p (min (min t r) r)+h (min t r-r) = p (min t r)
  rw [min_assoc,min_self,tsub_eq_zero_of_le (min_le_right t r),hzero,add_zero]

private theorem future_splice (r : ℝ≥0) (p h : Path) (hzero : h 0 = 0) :
    futurePath r (splicePath r (p,h)) = h := by
  apply ContinuousMap.ext
  intro t
  change (p (min (r+t) r)+h (r+t-r))-(p (min r r)+h (r-r)) = h t
  rw [min_eq_right (le_add_of_nonneg_right bot_le),add_tsub_cancel_left,min_self,
    tsub_self,hzero,add_zero]
  ring

private theorem density_splice_prefix (lambda : ℝ) (r : ℝ≥0) (p h : Path) (hzero : h 0 = 0) :
    density lambda r (splicePath r (p,h)) = density lambda r p := by
  rw [← density_past lambda r (splicePath r (p,h)),past_splice r p h hzero,density_past]

private theorem density_splice_complete (lambda : ℝ) (r : ℝ≥0) (p : Path)
    (q : ℝ≥0 × Path) (hzero : q.2 0 = 0) :
    density lambda (r+q.1) (splicePath r (pastPath r p,q.2)) =
      density lambda r p*stoppedDensity (lambda-(r : ℝ)) q := by
  rw [density_add,density_splice_prefix lambda r (pastPath r p) q.2 hzero,
    density_past,future_splice r (pastPath r p) q.2 hzero]
  rfl

private theorem ae_passage_past_initial_zero (level : ℝ) :
    ∀ᵐ q : ℝ≥0 × Path ∂pathLaw.map (passagePast level), q.2 0 = 0 := by
  apply (ae_map_iff (measurable_passagePast level).aemeasurable
    (measurableSet_eq_fun ((continuous_eval 0).measurable.comp measurable_snd) measurable_const)).mpr
  filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with h hh
  change h (min 0 (passageTime level h)) = 0
  rwa [min_eq_left (show (0 : ℝ≥0) ≤ passageTime level h by positivity)]

private def inserted (r : ℝ≥0) (p : Path) (q : ℝ≥0 × Path) : ℝ≥0 × Path :=
  (r+q.1,splicePath r (pastPath r p,q.2))

private theorem measurable_inserted (r : ℝ≥0) (p : Path) : Measurable (inserted r p) :=
  (measurable_const.add measurable_fst).prodMk
    ((measurable_splicePath r).comp (measurable_const.prodMk measurable_snd))

private theorem residual_inserted (lambda : ℝ) (r : ℝ≥0) (q : ℝ≥0 × Path) :
    lambda-((r+q.1 : ℝ≥0) : ℝ) = lambda-(r : ℝ)-(q.1 : ℝ) := by
  rw [NNReal.coe_add]
  ring

theorem actual_positive_prefix_complete_return_tilt (lambda : ℝ) (r : ℝ≥0) (hr : 0 < r)
    (p : Path) (hp : ∀ t : ℝ≥0, 0 < t → t ≤ r → 0 < p t)
    {Ψ : (ℝ≥0 × Path) × Path → ℝ≥0∞} (hΨ : Measurable Ψ) :
    density lambda r p*(∫⁻ h : Path,
      Ψ (returnTaggedPast (splicePath r (p,driftPath (lambda-(r : ℝ)) h)),
        returnFuturePath (splicePath r (p,driftPath (lambda-(r : ℝ)) h))) ∂pathLaw) =
      ∫⁻ h : Path, density lambda (returnTaggedPast (splicePath r (p,h))).1
          (returnTaggedPast (splicePath r (p,h))).2*
        Ψ (returnTaggedPast (splicePath r (p,h)),
          driftPath (lambda-((returnTaggedPast (splicePath r (p,h))).1 : ℝ))
            (returnFuturePath (splicePath r (p,h)))) ∂pathLaw := by
  let K : (ℝ≥0 × Path) × Path → ℝ≥0∞ := fun z ↦
    completeDensity lambda z.1*Ψ (residualLift lambda z)
  have hK : Measurable K := ((measurable_completeDensity lambda).comp measurable_fst).mul
    (hΨ.comp (measurable_residualLift lambda))
  let J : ℝ≥0 × Path → ℝ≥0∞ := fun q ↦
    ∫⁻ h : Path, Ψ (inserted r p q,driftPath (lambda-(r : ℝ)-(q.1 : ℝ)) h) ∂pathLaw
  have hpoint : Measurable (fun z : (ℝ≥0 × Path) × Path ↦
      (inserted r p z.1,driftPath (lambda-(r : ℝ)-(z.1.1 : ℝ)) z.2)) :=
    ((measurable_inserted r p).comp measurable_fst).prodMk
      (continuous_driftPath.measurable.comp
        ((measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk measurable_snd))
  have hJ : Measurable J := (hΨ.comp hpoint).lintegral_prod_right'
  have hnegative : -p r < 0 := neg_neg_of_pos (hp r hr le_rfl)
  calc
    _ = density lambda r p*(∫⁻ q : ℝ≥0 × Path, J q
        ∂pathLaw.map (actualDriverPassagePast (lambda-(r : ℝ)) (-p r))) := by
      rw [actual_positive_prefix_parabolic_return_lintegral r hr p hp (lambda-(r : ℝ)) hΨ]
      rfl
    _ = ∫⁻ q : ℝ≥0 × Path, density lambda r p*
        (stoppedDensity (lambda-(r : ℝ)) q*J q) ∂pathLaw.map (passagePast (-p r)) := by
      rw [actual_parabolic_passage_law _ _ hnegative]
      rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_stoppedDensity _) hJ]
      simp only [Pi.mul_apply]
      have hmul : Measurable (fun q : ℝ≥0 × Path ↦ stoppedDensity (lambda-(r : ℝ)) q*J q) :=
        (measurable_stoppedDensity _).mul hJ
      rw [lintegral_const_mul _ hmul]
    _ = ∫⁻ q : ℝ≥0 × Path, completeDensity lambda (inserted r p q)*J q
        ∂pathLaw.map (passagePast (-p r)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_passage_past_initial_zero (-p r)] with q hq
      change density lambda r p*(stoppedDensity (lambda-(r : ℝ)) q*J q) =
        density lambda (r+q.1) (splicePath r (pastPath r p,q.2))*J q
      rw [density_splice_complete lambda r p q hq,mul_assoc]
    _ = ∫⁻ q : ℝ≥0 × Path, ∫⁻ h : Path, K (inserted r p q,h) ∂pathLaw
        ∂pathLaw.map (passagePast (-p r)) := by
      apply lintegral_congr
      intro q
      have htest : Measurable (fun h : Path ↦
          Ψ (inserted r p q,driftPath (lambda-(r : ℝ)-(q.1 : ℝ)) h)) :=
        hΨ.comp (measurable_const.prodMk
          (BrownianParabolicFirstPassagePastFibers.measurable_actual_driftPath _))
      rw [← lintegral_const_mul _ htest]
      apply lintegral_congr
      intro h
      change _ = completeDensity lambda (inserted r p q)*
        Ψ (inserted r p q,driftPath (lambda-((r+q.1 : ℝ≥0) : ℝ)) h)
      rw [residual_inserted]
    _ = _ := (actual_positive_prefix_brownian_return_lintegral r hr p hp hK).symm

private theorem scaled_source_prefix_lintegral (r : ℝ≥0) (hr : 0 < r)
    {H : Path → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ g, H g ∂sourceLaw r) =
      ∫⁻ g, ∫⁻ h : Path, H (splicePath r (brownianDilation r (pastPath 1 g),h))
        ∂pathLaw ∂unitSourceLaw := by
  have hp : (sourceLaw r).map (pastPath r) =
      (unitSourceLaw.map (pastPath 1)).map (brownianDilation r) := by
    rw [sourceLaw,Measure.map_map (measurable_pastPath r) (measurable_brownianDilation r),
      Measure.map_map (measurable_brownianDilation r) (measurable_pastPath 1)]
    congr 1
    funext g
    change pastPath r (brownianDilation r g) = brownianDilation r (pastPath 1 g)
    simpa only [mul_one] using pastPath_brownianDilation r 1 hr g
  have hO : Measurable (fun p : Path ↦ ∫⁻ h : Path, H (splicePath r (p,h)) ∂pathLaw) :=
    (hH.comp (measurable_splicePath r)).lintegral_prod_right'
  rw [actual_scaled_source_whole_lintegral r hr hH,hp,lintegral_map hO (measurable_brownianDilation r)]
  change (∫⁻ a : Path, ((fun p : Path ↦ ∫⁻ h : Path, H (splicePath r (p,h)) ∂pathLaw) ∘
    brownianDilation r) a ∂unitSourceLaw.map (pastPath 1)) = _
  rw [lintegral_map (hO.comp (measurable_brownianDilation r)) (measurable_pastPath 1)]
  rfl

private theorem wholeLift_splice (lambda : ℝ) (r : ℝ≥0) (p h : Path) (hzero : h 0 = 0) :
    wholeLift lambda r (splicePath r (p,h)) = splicePath r (pastPath r p,driftPath (lambda-(r : ℝ)) h) := by
  unfold wholeLift shiftedSplice
  rw [past_splice r p h hzero,future_splice r p h hzero]

private theorem stopped_scaled_prefix (r : ℝ≥0) (hr : 0 < r) (g : Path) :
    pastPath r (brownianDilation r (pastPath 1 g)) = brownianDilation r (pastPath 1 g) := by
  have hi : pastPath 1 (pastPath 1 g) = pastPath 1 g := by
    apply ContinuousMap.ext
    intro t
    change g (min (min t 1) 1) = g (min t 1)
    rw [min_assoc,min_self]
  simpa only [mul_one,hi] using pastPath_brownianDilation r 1 hr (pastPath 1 g)

theorem actual_scaled_source_complete_return_lintegral (lambda : ℝ) (r : ℝ≥0) (hr : 0 < r)
    {Ψ : (ℝ≥0 × Path) × Path → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ g, density lambda r g*
      Ψ (returnTaggedPast (wholeLift lambda r g),returnFuturePath (wholeLift lambda r g)) ∂sourceLaw r) =
      ∫⁻ p : ℝ≥0 × Path, density lambda p.1 p.2*
        (∫⁻ h : Path, Ψ (p,driftPath (lambda-(p.1 : ℝ)) h) ∂pathLaw)
          ∂(sourceLaw r).map returnTaggedPast := by
  let H : Path → ℝ≥0∞ := fun g ↦ density lambda r g*
    Ψ (returnTaggedPast (wholeLift lambda r g),returnFuturePath (wholeLift lambda r g))
  have hH : Measurable H := (measurable_density lambda r).mul
    (hΨ.comp ((measurable_returnTaggedPast.comp (measurable_wholeLift lambda r)).prodMk
      (measurable_returnFuturePath.comp (measurable_wholeLift lambda r))))
  let K : (ℝ≥0 × Path) × Path → ℝ≥0∞ := fun z ↦
    completeDensity lambda z.1*Ψ (residualLift lambda z)
  have hK : Measurable K := ((measurable_completeDensity lambda).comp measurable_fst).mul
    (hΨ.comp (measurable_residualLift lambda))
  have hG : Measurable (fun g : Path ↦ K (returnTaggedPast g,returnFuturePath g)) :=
    hK.comp (measurable_returnTaggedPast.prodMk measurable_returnFuturePath)
  calc
    _ = ∫⁻ g, K (returnTaggedPast g,returnFuturePath g) ∂sourceLaw r := by
      change (∫⁻ g, H g ∂sourceLaw r) = _
      rw [scaled_source_prefix_lintegral r hr hH,scaled_source_prefix_lintegral r hr hG]
      apply lintegral_congr_ae
      filter_upwards [ae_unitSourceLaw_strict_positive_prefix] with g hg
      let p := brownianDilation r (pastPath 1 g)
      have hp : ∀ t : ℝ≥0, 0 < t → t ≤ r → 0 < p t := by
        intro t ht htr
        change 0 < Real.sqrt (r : ℝ)*pastPath 1 g (t/r)
        apply mul_pos (Real.sqrt_pos.mpr hr)
        have hdiv : t/r ≤ 1 := (div_le_one hr).mpr htr
        rw [pastPath_eval,min_eq_left hdiv]
        exact hg (t/r) (div_pos ht hr) hdiv
      have hpast : pastPath r p = p := stopped_scaled_prefix r hr g
      calc
        _ = density lambda r p*(∫⁻ h : Path,
            Ψ (returnTaggedPast (splicePath r (p,driftPath (lambda-(r : ℝ)) h)),
              returnFuturePath (splicePath r (p,driftPath (lambda-(r : ℝ)) h))) ∂pathLaw) := by
          have hm : Measurable (fun h : Path ↦
              Ψ (returnTaggedPast (splicePath r (p,driftPath (lambda-(r : ℝ)) h)),
                returnFuturePath (splicePath r (p,driftPath (lambda-(r : ℝ)) h)))) :=
            hΨ.comp ((measurable_returnTaggedPast.prodMk measurable_returnFuturePath).comp
              ((measurable_splicePath r).comp (measurable_const.prodMk
                (BrownianParabolicFirstPassagePastFibers.measurable_actual_driftPath _))))
          rw [← lintegral_const_mul _ hm]
          apply lintegral_congr_ae
          filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with h hh
          change H (splicePath r (p,h)) = _
          simp only [H,density_splice_prefix lambda r p h hh,wholeLift_splice lambda r p h hh,hpast]
        _ = _ := actual_positive_prefix_complete_return_tilt lambda r hr p hp hΨ
    _ = _ := by
      rw [← lintegral_map hK (measurable_returnTaggedPast.prodMk measurable_returnFuturePath),
        actual_scaled_return_past_future_jointLaw r hr]
      let : IsProbabilityMeasure ((sourceLaw r).map returnTaggedPast) :=
        Measure.isProbabilityMeasure_map measurable_returnTaggedPast.aemeasurable
      rw [lintegral_prod _ hK.aemeasurable]
      apply lintegral_congr
      intro p
      change (∫⁻ h : Path, completeDensity lambda p*Ψ (p,driftPath (lambda-(p.1 : ℝ)) h) ∂pathLaw) = _
      have htest : Measurable (fun h : Path ↦ Ψ (p,driftPath (lambda-(p.1 : ℝ)) h)) :=
        hΨ.comp (measurable_const.prodMk
          (BrownianParabolicFirstPassagePastFibers.measurable_actual_driftPath _))
      rw [lintegral_const_mul _ htest]
      rfl

end PerronWright.BrownianMinimumFutureCompleteReturnTilt
