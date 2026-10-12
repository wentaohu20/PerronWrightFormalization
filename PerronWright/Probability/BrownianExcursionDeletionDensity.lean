import PerronWright.Probability.BrownianExcursionDeletionGeometry
import PerronWright.Probability.BrownianParabolicStoppedTiltGeometry
import PerronWright.Probability.BrownianMinimumShiftWrightLaw

/-! # The actual parabolic path density after removing a complete excursion

The density is evaluated in driver coordinates, as in the proved Brownian
change of measure. A closed interval is removed from that driver. Its literal
area and the actual parabolic energy give the density ratio. For a genuine
reflected excursion the removed area is its full reflected area plus its
length times the driver value at the left endpoint.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionDeletionDensity

open BrownianPathLaw BrownianPathIndependentIncrements BrownianBridgeCyclicArea
open BrownianPathReflectionLaw ContinuousPathReflection ContinuousPathIntervalDeletion
open BrownianKilledAreaGeometry BrownianParabolicDriftTiltGeometry
open BrownianParabolicStoppedTiltGeometry ContinuousExcursionDeletionReflection
open BrownianFullHorizonExcursionAreas BrownianExcursionDeletionGeometry
open FullHorizonExcursionComponents FullHorizonExcursionEndpoints
open BrownianExcursionTuplePoissonWeights

private theorem deletion_prefix_area (a l : ℝ≥0) (f : Path) :
    pathArea a (deletionPath a l f) = pathArea a f := by
  unfold pathArea
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc 0 (a : ℝ) := by
    simpa only [uIcc_of_le a.coe_nonneg] using hr
  dsimp only
  rw [deletionPath_apply,if_pos (Real.toNNReal_le_iff_le_coe.mpr hr'.2)]

private theorem deletion_future (a l : ℝ≥0) (f : Path)
    (hclosed : f (a+l) = f a) :
    futurePath a (deletionPath a l f) = futurePath (a+l) f := by
  apply ContinuousMap.ext
  intro t
  rw [futurePath_eval,futurePath_eval,deletionPath_closed_apply a l f hclosed (a+t),
    deletionPath_closed_apply a l f hclosed a,if_pos le_rfl,hclosed]
  by_cases ht : t = 0
  · subst t
    simp only [add_zero,le_refl,if_true,hclosed]
  · have hta : ¬ a+t ≤ a := not_le.mpr (lt_add_of_pos_right a (pos_iff_ne_zero.mpr ht))
    rw [if_neg hta]
    congr 1
    congr 1
    ac_rfl

private theorem deletion_endpoint (a l t : ℝ≥0) (f : Path)
    (hat : a ≤ t) (hclosed : f (a+l) = f a) :
    deletionPath a l f t = f (t+l) := by
  rw [deletionPath_closed_apply a l f hclosed t]
  by_cases hta : t ≤ a
  · have he : t = a := le_antisymm hta hat
    subst t
    rw [if_pos le_rfl,hclosed]
  · exact if_neg hta

/-- The area of the original driver is the area of the actual remaining
driver plus the literal removed interval integral. Zero cut length is allowed. -/
theorem pathArea_closed_deletion (a l t : ℝ≥0) (f : Path)
    (hat : a ≤ t) (hclosed : f (a+l) = f a) :
    pathArea (t+l) f = pathArea t (deletionPath a l f)+
      ∫ r in (a : ℝ)..((a+l : ℝ≥0) : ℝ), f (Real.toNNReal r) := by
  have he : a+(t-a) = t := add_tsub_cancel_of_le hat
  have ht : (a+l)+(t-a) = t+l := by
    calc
      (a+l)+(t-a) = (a+(t-a))+l := by ac_rfl
      _ = t+l := by rw [he]
  have ho := pathArea_add (a+l) (t-a) f
  rw [ht,pathArea_add a l f,hclosed] at ho
  have hd := pathArea_add a (t-a) (deletionPath a l f)
  rw [he,deletion_prefix_area,deletion_future a l f hclosed,
    deletionPath_apply,if_pos le_rfl] at hd
  rw [pathArea_future_segment]
  linarith

theorem score_closed_deletion (lambda : ℝ) (a l t : ℝ≥0) (f : Path)
    (hat : a ≤ t) (hclosed : f (a+l) = f a) :
    score lambda (t+l) f = score (lambda-(l : ℝ)) t (deletionPath a l f)+
      ∫ r in (a : ℝ)..((a+l : ℝ≥0) : ℝ), f (Real.toNNReal r) := by
  unfold score
  rw [pathArea_closed_deletion a l t f hat hclosed,
    deletion_endpoint a l t f hat hclosed,NNReal.coe_add]
  ring

/-- The actual density cocycle is on driver paths, not on their raw Brownian
preimages. The parameter of the remaining driver is lambda minus cut length. -/
theorem density_closed_deletion (lambda : ℝ) (a l t : ℝ≥0) (f : Path)
    (hat : a ≤ t) (hclosed : f (a+l) = f a) :
    density lambda (t+l) f = density (lambda-(l : ℝ)) t (deletionPath a l f)*
      ENNReal.ofReal (Real.exp ((∫ r in (a : ℝ)..((a+l : ℝ≥0) : ℝ),
        f (Real.toNNReal r))-energy lambda l/2)) := by
  have he : energy lambda (t+l) = energy lambda l+energy (lambda-(l : ℝ)) t := by
    rw [add_comm t l,energy_add]
  unfold density
  rw [score_closed_deletion lambda a l t f hat hclosed,he,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

/-- On a genuine full excursion, the removed driver integral is its actual
reflected area plus the constant running-minimum level times its length. -/
theorem actual_removed_driver_integral (q lambda : ℝ) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hb : BddAbove (component (driftedReflectionPath lambda f) q)) :
    (∫ r in (leftTime q lambda f : ℝ)..(rightTime q lambda f : ℝ),
      driftPath lambda f (Real.toNNReal r)) =
      (excursionArea q lambda f : ℝ)+
        ((rightTime q lambda f : ℝ)-(leftTime q lambda f : ℝ))*
          driftPath lambda f (leftTime q lambda f) := by
  let g := driftPath lambda f
  let a := leftTime q lambda f
  let b := rightTime q lambda f
  have hqg : q ∈ positiveSet (reflectionPath g) := hq
  have hbg : BddAbove (component (reflectionPath g) q) := hb
  have ha : (a : ℝ) = leftEndpoint q (reflectionPath g) := coe_leftTime q lambda f
  have he : (b : ℝ) = rightEndpoint q (reflectionPath g) := coe_rightTime q lambda f
  have hbound := endpoint_bounds hq hb
  have hab : a < b := NNReal.coe_lt_coe.mp (by
    rw [ha,he]
    exact hbound.2.1.trans hbound.2.2)
  have hpos : ∀ t ∈ Ioo a b, 0 < reflectionPath g t := by
    intro t ht
    have htr : (t : ℝ) ∈ component (reflectionPath g) q := by
      rw [component_eq_Ioo hqg hbg]
      exact ⟨by rw [← ha]; exact ht.1,by rw [← he]; exact ht.2⟩
    have hp := (component_subset (reflectionPath g) q htr).2
    change 0 < reflectionPath g (Real.toNNReal (t : ℝ)) at hp
    simpa only [Real.toNNReal_coe] using hp
  have hzero := leftEndpoint_zero hq hb (show reflectionPath g 0 = 0 from reflected_zero g)
  change g a-runningMinimum g a = 0 at hzero
  have hmin : ∀ u ∈ Icc a b, runningMinimum g u = g a := by
    intro u hu
    have hm := runningMinimum_constant_on_positive_interval g a b hab hpos u hu
    linarith
  have hi : (∫ r in (a : ℝ)..(b : ℝ), g (Real.toNNReal r)) =
      ∫ r in (a : ℝ)..(b : ℝ), BrownianReflectedAreaCounts.surface lambda f r+g a := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (a : ℝ) (b : ℝ) := by
      simpa only [uIcc_of_le (show (a : ℝ) ≤ (b : ℝ) from hab.le)] using hr
    have hr0 : 0 ≤ r := a.coe_nonneg.trans hr'.1
    have hn : Real.toNNReal r ∈ Icc a b := by
      constructor
      · apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal _ hr0]
        exact hr'.1
      · exact Real.toNNReal_le_iff_le_coe.mpr hr'.2
    dsimp only
    change g (Real.toNNReal r) =
      (g (Real.toNNReal r)-runningMinimum g (Real.toNNReal r))+g a
    rw [hmin _ hn]
    ring
  have hsurface : IntervalIntegrable (BrownianReflectedAreaCounts.surface lambda f)
      volume (a : ℝ) (b : ℝ) :=
    (BrownianReflectedAreaCounts.continuous_surface lambda f).intervalIntegrable _ _
  have harea : (∫ r in (a : ℝ)..(b : ℝ), BrownianReflectedAreaCounts.surface lambda f r) =
      (excursionArea q lambda f : ℝ) := by
    change _ = ∫ r in Icc (a : ℝ) (b : ℝ), BrownianReflectedAreaCounts.surface lambda f r
    rw [integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (show (a : ℝ) ≤ (b : ℝ) from hab.le)]
  change (∫ r in (a : ℝ)..(b : ℝ), g (Real.toNNReal r)) =
    (excursionArea q lambda f : ℝ)+((b : ℝ)-(a : ℝ))*g a
  rw [hi,intervalIntegral.integral_add hsurface intervalIntegrable_const,
    harea,intervalIntegral.integral_const,smul_eq_mul]

/-- Literal density factorization at one actual complete excursion. The
residual path is the proved compensated Brownian splice with its exact
remaining parabolic parameter. No stochastic deletion law is presumed. -/
theorem actual_excursion_deletion_density (q lambda : ℝ) (T : ℝ≥0) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hb : BddAbove (component (driftedReflectionPath lambda f) q))
    (hT : rightTime q lambda f ≤ T) :
    density lambda T (driftPath lambda f) =
      density (deletedParameter q lambda f) (T-cutLength q lambda f)
        (driftPath (deletedParameter q lambda f) (deletedPath q lambda f))*
      ENNReal.ofReal (Real.exp ((excursionArea q lambda f : ℝ)+
        (cutLength q lambda f : ℝ)*driftPath lambda f (leftTime q lambda f)-
          energy lambda (cutLength q lambda f)/2)) := by
  let a := leftTime q lambda f
  let b := rightTime q lambda f
  let l := cutLength q lambda f
  have hab : a ≤ b := NNReal.coe_le_coe.mp (by
    rw [coe_leftTime,coe_rightTime]
    exact ((endpoint_bounds hq hb).2.1.trans (endpoint_bounds hq hb).2.2).le)
  have he : a+l = b := add_tsub_cancel_of_le hab
  have hlT : l ≤ T := (tsub_le_self : b-a ≤ b).trans hT
  have hat : a ≤ T-l := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_sub hlT]
    have hs : (a : ℝ)+(l : ℝ) = (b : ℝ) := by
      rw [← NNReal.coe_add,he]
    have ht : (b : ℝ) ≤ (T : ℝ) := hT
    linarith
  have hclosed : driftPath lambda f (a+l) = driftPath lambda f a := by
    rw [he]
    exact excursion_endpoints_closed (driftPath lambda f) q hq hb
  have hd := density_closed_deletion lambda a l (T-l) (driftPath lambda f) hat hclosed
  rw [tsub_add_cancel_of_le hlT,he,actual_removed_driver_integral q lambda f hq hb,
    parabolic_deletion_eq] at hd
  have hc : (l : ℝ) = (b : ℝ)-(a : ℝ) := NNReal.coe_sub hab
  rw [← hc] at hd
  exact hd

/-- The actual removed-area Poisson probability cancels the area exponential
in the driver density. Only the full area moment and the level/energy factor
remain for the genuine marked Palm calculation. -/
theorem actual_excursion_deletion_poisson_density (q lambda : ℝ) (T : ℝ≥0)
    (f : Path) (r : ℕ)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hb : BddAbove (component (driftedReflectionPath lambda f) q))
    (hT : rightTime q lambda f ≤ T) :
    density lambda T (driftPath lambda f)*poissonWeight (excursionArea q lambda f) r =
      (density (deletedParameter q lambda f) (T-cutLength q lambda f)
        (driftPath (deletedParameter q lambda f) (deletedPath q lambda f))*
        ENNReal.ofReal (Real.exp ((cutLength q lambda f : ℝ)*
          driftPath lambda f (leftTime q lambda f)-energy lambda (cutLength q lambda f)/2)))*
      ENNReal.ofReal ((excursionArea q lambda f : ℝ)^r/(r.factorial : ℝ)) := by
  rw [actual_excursion_deletion_density q lambda T f hq hb hT]
  have he : ENNReal.ofReal (Real.exp ((excursionArea q lambda f : ℝ)+
        (cutLength q lambda f : ℝ)*driftPath lambda f (leftTime q lambda f)-
          energy lambda (cutLength q lambda f)/2)) =
      ENNReal.ofReal (Real.exp ((cutLength q lambda f : ℝ)*
        driftPath lambda f (leftTime q lambda f)-energy lambda (cutLength q lambda f)/2))*
      ENNReal.ofReal (Real.exp (excursionArea q lambda f : ℝ)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
    congr 2
    ring
  have hc : ENNReal.ofReal (Real.exp (excursionArea q lambda f : ℝ))*
      poissonWeight (excursionArea q lambda f) r =
      ENNReal.ofReal ((excursionArea q lambda f : ℝ)^r/(r.factorial : ℝ)) := by
    simpa only [Real.toNNReal_coe] using
      BrownianMinimumShiftWrightLaw.poissonWeight_exp_cancel
        (excursionArea q lambda f : ℝ) (excursionArea q lambda f).coe_nonneg r
  rw [he]
  calc
    _ = (density (deletedParameter q lambda f) (T-cutLength q lambda f)
        (driftPath (deletedParameter q lambda f) (deletedPath q lambda f))*
        ENNReal.ofReal (Real.exp ((cutLength q lambda f : ℝ)*
          driftPath lambda f (leftTime q lambda f)-energy lambda (cutLength q lambda f)/2)))*
      (ENNReal.ofReal (Real.exp (excursionArea q lambda f : ℝ))*
        poissonWeight (excursionArea q lambda f) r) := by ac_rfl
    _ = _ := by rw [hc]

end PerronWright.BrownianExcursionDeletionDensity
