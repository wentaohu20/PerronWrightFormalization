import PerronWright.Probability.ContinuousExcursionDeletionComponents

/-! # Measurable deletion at true reflected excursion endpoints

The interval is the actual full positivity component at the chosen anchor.
The parameter and remaining continuous driver are Borel functions of the
original parameter and path. Remaining lengths and literal full areas
are preserved, without assuming any stochastic deletion or Palm law.
-/

open MeasureTheory Topology Set
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionDeletionGeometry

open BrownianPathLaw BrownianPathReflectionLaw BrownianFullHorizonExcursionAreas
open FullHorizonExcursionComponents ContinuousPathIntervalDeletion
open ContinuousExcursionDeletionReflection ContinuousExcursionDeletionComponents

def cutLength (q lambda : ℝ) (f : Path) : ℝ≥0 :=
  rightTime q lambda f-leftTime q lambda f

def deletedPath (q lambda : ℝ) (f : Path) : Path :=
  correctedDeletionPath (leftTime q lambda f) (cutLength q lambda f) f

def deletedParameter (q lambda : ℝ) (f : Path) : ℝ :=
  lambda-(cutLength q lambda f : ℝ)

theorem measurable_cutLength_all_parameters (q : ℝ) :
    Measurable (fun p : ℝ × Path ↦ cutLength q p.1 p.2) :=
  (measurable_rightTime_all_parameters q).sub (measurable_leftTime_all_parameters q)

theorem measurable_deletedPath_all_parameters (q : ℝ) :
    Measurable (fun p : ℝ × Path ↦ deletedPath q p.1 p.2) := by
  have hm : Measurable (fun p : ℝ × Path ↦
      (p.2,leftTime q p.1 p.2,cutLength q p.1 p.2)) :=
    measurable_snd.prodMk ((measurable_leftTime_all_parameters q).prodMk
      (measurable_cutLength_all_parameters q))
  simpa only [deletedPath,Function.comp_def] using
    continuous_joint_correctedDeletionPath.measurable.comp hm

theorem measurable_deletedParameter_all_parameters (q : ℝ) :
    Measurable (fun p : ℝ × Path ↦ deletedParameter q p.1 p.2) :=
  measurable_fst.sub (NNReal.continuous_coe.measurable.comp (measurable_cutLength_all_parameters q))

private theorem leftTime_le_rightTime (q lambda : ℝ) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hb : BddAbove (component (driftedReflectionPath lambda f) q)) :
    leftTime q lambda f ≤ rightTime q lambda f := by
  apply NNReal.coe_le_coe.mp
  rw [coe_leftTime,coe_rightTime]
  exact ((endpoint_bounds hq hb).2.1.trans (endpoint_bounds hq hb).2.2).le

theorem cutLength_eq_length (q lambda : ℝ) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hb : BddAbove (component (driftedReflectionPath lambda f) q)) :
    (cutLength q lambda f : ℝ) = FullHorizonExcursionComponents.length q
      (driftedReflectionPath lambda f) := by
  unfold cutLength
  rw [NNReal.coe_sub (leftTime_le_rightTime q lambda f hq hb),coe_rightTime,coe_leftTime]
  rfl

theorem deleted_reflection_eq (q lambda : ℝ) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hb : BddAbove (component (driftedReflectionPath lambda f) q)) :
    driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f) =
      deletionPath (leftTime q lambda f) (cutLength q lambda f)
        (driftedReflectionPath lambda f) :=
  parabolic_excursion_deletion_eq lambda f q hq hb

private theorem zeros_at_cut (q lambda : ℝ) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hb : BddAbove (component (driftedReflectionPath lambda f) q)) :
    driftedReflectionPath lambda f (leftTime q lambda f) = 0 ∧
      driftedReflectionPath lambda f (leftTime q lambda f+cutLength q lambda f) = 0 := by
  have ha := leftEndpoint_zero hq hb (show driftedReflectionPath lambda f 0 = 0 from
    ContinuousPathReflection.reflected_zero _)
  have he : leftTime q lambda f+cutLength q lambda f = rightTime q lambda f :=
    add_tsub_cancel_of_le (leftTime_le_rightTime q lambda f hq hb)
  constructor
  · exact ha
  · rw [he]
    exact rightEndpoint_zero hq hb

theorem remaining_before_length_area (q lambda r : ℝ) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hbq : BddAbove (component (driftedReflectionPath lambda f) q))
    (hr : r ∈ positiveSet (driftedReflectionPath lambda f))
    (hbr : BddAbove (component (driftedReflectionPath lambda f) r))
    (hra : r < leftTime q lambda f) :
    FullHorizonExcursionComponents.length r
        (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f)) =
      FullHorizonExcursionComponents.length r (driftedReflectionPath lambda f) ∧
    excursionArea r (deletedParameter q lambda f) (deletedPath q lambda f) = excursionArea r lambda f := by
  have hz := zeros_at_cut q lambda f hq hbq
  have hc := component_before_deletion (driftedReflectionPath lambda f)
    (leftTime q lambda f) (cutLength q lambda f) r hr hra hz.1
  have hd := deleted_reflection_eq q lambda f hq hbq
  have hbD : BddAbove (component
      (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f)) r) := by
    rw [hd,hc]
    exact hbr
  constructor
  · rw [hd]
    exact length_before_deletion _ _ _ r hr hra hz.1
  · apply NNReal.eq
    rw [excursionArea_eq_component_integral hbD,excursionArea_eq_component_integral hbr,hd]
    exact component_integral_before_deletion _ _ _ r hr hra hz.1

theorem remaining_after_length_area (q lambda r : ℝ) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hbq : BddAbove (component (driftedReflectionPath lambda f) q))
    (hr : r ∈ positiveSet (driftedReflectionPath lambda f))
    (hbr : BddAbove (component (driftedReflectionPath lambda f) r))
    (hbrt : (rightTime q lambda f : ℝ) < r) :
    FullHorizonExcursionComponents.length (r-cutLength q lambda f)
        (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f)) =
      FullHorizonExcursionComponents.length r (driftedReflectionPath lambda f) ∧
    excursionArea (r-cutLength q lambda f) (deletedParameter q lambda f) (deletedPath q lambda f) =
      excursionArea r lambda f := by
  have hz := zeros_at_cut q lambda f hq hbq
  have he : leftTime q lambda f+cutLength q lambda f = rightTime q lambda f :=
    add_tsub_cancel_of_le (leftTime_le_rightTime q lambda f hq hbq)
  have hra : ((leftTime q lambda f+cutLength q lambda f : ℝ≥0) : ℝ) < r := by
    rwa [he]
  have hc := component_after_deletion (driftedReflectionPath lambda f)
    (leftTime q lambda f) (cutLength q lambda f) r hr hra hz.1 hz.2
  have hd := deleted_reflection_eq q lambda f hq hbq
  have hbD : BddAbove (component
      (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f))
        (r-cutLength q lambda f)) := by
    rw [hd,hc]
    obtain ⟨z,hz⟩ := hbr
    refine ⟨z-cutLength q lambda f,?_⟩
    rintro t ⟨u,hu,rfl⟩
    exact sub_le_sub_right (hz hu) _
  constructor
  · rw [hd]
    exact length_after_deletion _ _ _ r hr hra hz.1 hz.2 hbr
  · apply NNReal.eq
    rw [excursionArea_eq_component_integral hbD,excursionArea_eq_component_integral hbr,hd]
    exact component_integral_after_deletion _ _ _ r hr hra hz.1 hz.2

end PerronWright.BrownianExcursionDeletionGeometry
