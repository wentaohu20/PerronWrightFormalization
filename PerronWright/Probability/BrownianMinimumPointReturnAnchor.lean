import PerronWright.Probability.BrownianParabolicExcursionAnchor
import PerronWright.Probability.BrownianMinimumFutureFirstReturn
import PerronWright.Probability.BrownianExcursionDeletionDensity

/-! # The literal complete excursion at a true minimum-split anchor

The positive-time return of the whole minimum future is proved to be the
length of the actual reflected component containing the anchor. Its
stopped future area is the full component area, not a truncated area.
The parabolic terminals discharge positivity, uniqueness and finiteness
from the actual Brownian path law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianMinimumPointReturnAnchor

open BrownianPathLaw BrownianPathReflectionLaw ContinuousPathReflection
open BrownianPathIndependentIncrements ContinuousPathLeastMinimum
open FullHorizonExcursionComponents FullHorizonExcursionEndpoints
open BrownianParabolicExcursionAnchor ContinuousExcursionDeletionReflection
open BrownianMinimumFutureFirstReturn BrownianBridgeCyclicArea BrownianKilledAreaGeometry
open BrownianFullHorizonExcursionAreas BrownianExcursionDeletionGeometry

theorem firstReturnZero_eq_of_positive_interval (g : Path) (r : ℝ≥0) (hr : 0 < r)
    (hpos : ∀ t : ℝ≥0, 0 < t → t < r → 0 < g t) (hzero : g r = 0) :
    firstReturnZero g = (r : ℝ≥0∞) := by
  apply le_antisymm
  · exact sInf_le ⟨r,⟨hr,hzero.le⟩,rfl⟩
  · apply le_sInf
    rintro x ⟨t,⟨ht,hgt⟩,rfl⟩
    exact ENNReal.coe_le_coe.mpr (le_of_not_gt (fun h ↦ (not_le_of_gt (hpos t ht h)) hgt))

/-- No excursion law is assumed in this deterministic identification. -/
theorem minimumFuture_firstReturn_eq_length (f : Path) (t : ℝ≥0)
    (hq : (t : ℝ) ∈ positiveSet (reflectionPath f))
    (hb : BddAbove (component (reflectionPath f) (t : ℝ)))
    (hu : ∀ u : ℝ≥0, u ≤ t → f u = minimumValue t f → u = leastMinimizer t f) :
    firstReturnZero (futurePath (leastMinimizer t f) f) =
      ENNReal.ofReal (length (t : ℝ) (reflectionPath f)) := by
  let a := leastMinimizer t f
  let b := Real.toNNReal (rightEndpoint (t : ℝ) (reflectionPath f))
  have hleft : leftEndpoint (t : ℝ) (reflectionPath f) = (a : ℝ) :=
    leftEndpoint_eq_leastMinimizer f t hq hb hu
  have hbound := endpoint_bounds hq hb
  have hb0 : 0 ≤ rightEndpoint (t : ℝ) (reflectionPath f) := rightEndpoint_nonneg _ _
  have hbr : (b : ℝ) = rightEndpoint (t : ℝ) (reflectionPath f) := Real.coe_toNNReal _ hb0
  have hab : a < b := NNReal.coe_lt_coe.mp (by
    rw [hbr,← hleft]
    exact hbound.2.1.trans hbound.2.2)
  have hpos : ∀ u ∈ Ioo a b, 0 < reflectionPath f u := by
    intro u hu'
    have hc : (u : ℝ) ∈ component (reflectionPath f) (t : ℝ) := by
      rw [component_eq_Ioo hq hb,hleft,← hbr]
      exact hu'
    have hp := (component_subset _ _ hc).2
    change 0 < reflectionPath f (Real.toNNReal (u : ℝ)) at hp
    simpa only [Real.toNNReal_coe] using hp
  have hm := runningMinimum_constant_on_positive_interval f a b hab hpos
  have hstart : f a = runningMinimum f a := by
    have hz := leftEndpoint_zero hq hb (show reflectionPath f 0 = 0 from reflected_zero f)
    rw [hleft] at hz
    change f (Real.toNNReal (a : ℝ))-runningMinimum f (Real.toNNReal (a : ℝ)) = 0 at hz
    rw [Real.toNNReal_coe] at hz
    linarith
  have hgpos : ∀ u : ℝ≥0, 0 < u → u < b-a → 0 < futurePath a f u := by
    intro u hu0 hu
    have hau : a+u ∈ Ioo a b :=
      ⟨lt_add_of_pos_right a hu0,(lt_tsub_iff_left).mp hu⟩
    have hp := hpos (a+u) hau
    change 0 < f (a+u)-runningMinimum f (a+u) at hp
    rw [hm _ ⟨hau.1.le,hau.2.le⟩,← hstart] at hp
    exact hp
  have hgend : futurePath a f (b-a) = 0 := by
    rw [futurePath_eval,add_tsub_cancel_of_le hab.le]
    have he := (component_driver_endpoints_eq_prefix_minimum f t hq hb)
    have haeq : Real.toNNReal (leftEndpoint (t : ℝ) (reflectionPath f)) = a := by
      rw [hleft,Real.toNNReal_coe]
    have heb : f b = minimumValue t f := he.2
    have hea : f a = minimumValue t f := by simpa only [haeq] using he.1
    rw [heb,hea,sub_self]
  have hr := firstReturnZero_eq_of_positive_interval (futurePath a f) (b-a)
    (tsub_pos_iff_lt.mpr hab) hgpos hgend
  have hlen : length (t : ℝ) (reflectionPath f) = ((b-a : ℝ≥0) : ℝ) := by
    rw [length,hleft,← hbr,NNReal.coe_sub hab.le]
  rw [hlen,ENNReal.ofReal_coe_nnreal]
  exact hr

theorem minimumFuture_return_endpoint (f : Path) (t : ℝ≥0)
    (hq : (t : ℝ) ∈ positiveSet (reflectionPath f))
    (hb : BddAbove (component (reflectionPath f) (t : ℝ)))
    (hu : ∀ u : ℝ≥0, u ≤ t → f u = minimumValue t f → u = leastMinimizer t f) :
    leastMinimizer t f+
        (firstReturnZero (futurePath (leastMinimizer t f) f)).toNNReal =
      Real.toNNReal (rightEndpoint (t : ℝ) (reflectionPath f)) := by
  rw [minimumFuture_firstReturn_eq_length f t hq hb hu]
  change leastMinimizer t f+Real.toNNReal (length (t : ℝ) (reflectionPath f)) = _
  apply NNReal.coe_injective
  rw [NNReal.coe_add,Real.coe_toNNReal _ (length_pos hq hb).le,
    Real.coe_toNNReal _ (rightEndpoint_nonneg _ _),length,
    leftEndpoint_eq_leastMinimizer f t hq hb hu]
  ring

theorem ae_actual_parabolic_component_bddAbove (lambda q : ℝ) :
    ∀ᵐ f : Path ∂pathLaw, BddAbove (component (driftedReflectionPath lambda f) q) := by
  rw [pathLaw]
  apply (ae_map_iff measurable_measurablePath.aemeasurable
    ((measurableSet_component_bddAbove q).preimage (measurable_driftedReflectionPath lambda))).mpr
  exact BrownianFullHorizonExcursions.ae_all_actual_components_bddAbove.mono
    (fun x hx ↦ hx lambda q)

theorem ae_actual_parabolic_minimumFuture_return (lambda : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ f : Path ∂pathLaw,
      firstReturnZero (futurePath (leastMinimizer t (driftPath lambda f)) (driftPath lambda f)) =
        ENNReal.ofReal (length (t : ℝ) (driftedReflectionPath lambda f)) ∧
      leastMinimizer t (driftPath lambda f)+
          (firstReturnZero (futurePath (leastMinimizer t (driftPath lambda f))
            (driftPath lambda f))).toNNReal = rightTime (t : ℝ) lambda f := by
  filter_upwards [ae_actual_parabolic_anchor_endpoints lambda t ht,
    ae_actual_parabolic_component_bddAbove lambda (t : ℝ),
    BrownianPathMinimumUnique.ae_actual_parabolic_unique_minimum lambda t ht] with f hq hb hu
  exact ⟨minimumFuture_firstReturn_eq_length _ t hq.1 hb hu,
    minimumFuture_return_endpoint _ t hq.1 hb hu⟩

/-- The source's return-stopped area is exactly the literal full reflected
component area. This identity is not an area-law or Palm-law premise. -/
theorem ae_actual_parabolic_completed_minimumFuture_area (lambda : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ f : Path ∂pathLaw,
      pathArea (firstReturnZero (futurePath (leastMinimizer t (driftPath lambda f))
        (driftPath lambda f))).toNNReal
          (futurePath (leastMinimizer t (driftPath lambda f)) (driftPath lambda f)) =
        (excursionArea (t : ℝ) lambda f : ℝ) := by
  filter_upwards [ae_actual_parabolic_anchor_endpoints lambda t ht,
    ae_actual_parabolic_component_bddAbove lambda (t : ℝ),
    ae_actual_parabolic_minimumFuture_return lambda t ht] with f hq hb hr
  have ha : leftTime (t : ℝ) lambda f = leastMinimizer t (driftPath lambda f) := by
    rw [leftTime,hq.2.1,Real.toNNReal_coe]
  let s := leastMinimizer t (driftPath lambda f)
  let r := (firstReturnZero (futurePath s (driftPath lambda f))).toNNReal
  have he : s+r = rightTime (t : ℝ) lambda f := hr.2
  have harea := BrownianExcursionDeletionDensity.actual_removed_driver_integral
    (t : ℝ) lambda f hq.1 hb
  rw [ha,← he,pathArea_future_segment,NNReal.coe_add] at harea
  change pathArea r (futurePath s (driftPath lambda f)) = _
  linarith

end PerronWright.BrownianMinimumPointReturnAnchor
