import PerronWright.Probability.BrownianPathMinimumUnique
import PerronWright.Probability.BrownianParabolicMinimumSplitWindow
import PerronWright.Probability.ContinuousExcursionDeletionReflection
import PerronWright.Probability.BrownianParabolicFirstPassageStrongMarkovFull

/-! # Actual excursion endpoints from a deterministic interior anchor

The driver values at the genuine component endpoints are the actual
prefix minimum. Proved minimum uniqueness identifies the left endpoint;
literal positivity and endpoint closure identify the right endpoint as
the future's first passage. The Brownian terminal discharges uniqueness,
positivity and finite-component requirements rather than assuming them.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianParabolicExcursionAnchor

open BrownianPathLaw BrownianPathReflectionLaw ContinuousPathReflection
open FullHorizonExcursionComponents FullHorizonExcursionEndpoints
open ContinuousExcursionDeletionReflection ContinuousPathLeastMinimum
open ContinuousPathFirstPassage
open BrownianPathIndependentIncrements (futurePath futurePath_eval)

private theorem component_times (f : Path) (t : ℝ≥0)
    (hq : (t : ℝ) ∈ positiveSet (reflectionPath f))
    (hb : BddAbove (component (reflectionPath f) (t : ℝ))) :
    let a := Real.toNNReal (leftEndpoint (t : ℝ) (reflectionPath f))
    let b := Real.toNNReal (rightEndpoint (t : ℝ) (reflectionPath f))
    a < t ∧ t < b ∧ ∀ u ∈ Ioo a b, 0 < reflectionPath f u := by
  dsimp only
  have hbound := endpoint_bounds hq hb
  have ha := Real.coe_toNNReal _ hbound.1
  have hb' := Real.coe_toNNReal _ (hbound.1.trans (hbound.2.1.trans hbound.2.2).le)
  refine ⟨?_,?_,?_⟩
  · exact NNReal.coe_lt_coe.mp (by rw [ha]; exact hbound.2.1)
  · exact NNReal.coe_lt_coe.mp (by rw [hb']; exact hbound.2.2)
  · intro u hu
    have hc : (u : ℝ) ∈ component (reflectionPath f) (t : ℝ) := by
      rw [component_eq_Ioo hq hb]
      exact ⟨by rw [← ha]; exact hu.1,by rw [← hb']; exact hu.2⟩
    have hp := (component_subset (reflectionPath f) (t : ℝ) hc).2
    change 0 < reflectionPath f (Real.toNNReal (u : ℝ)) at hp
    simpa only [BrownianWindowExcursions.realEval,Real.toNNReal_coe] using hp

theorem component_driver_endpoints_eq_prefix_minimum (f : Path) (t : ℝ≥0)
    (hq : (t : ℝ) ∈ positiveSet (reflectionPath f))
    (hb : BddAbove (component (reflectionPath f) (t : ℝ))) :
    f (Real.toNNReal (leftEndpoint (t : ℝ) (reflectionPath f))) = minimumValue t f ∧
      f (Real.toNNReal (rightEndpoint (t : ℝ) (reflectionPath f))) = minimumValue t f := by
  let a := Real.toNNReal (leftEndpoint (t : ℝ) (reflectionPath f))
  let b := Real.toNNReal (rightEndpoint (t : ℝ) (reflectionPath f))
  have htimes := component_times f t hq hb
  have hm := runningMinimum_constant_on_positive_interval f a b
    (htimes.1.trans htimes.2.1) htimes.2.2 t ⟨htimes.1.le,htimes.2.1.le⟩
  have hz := leftEndpoint_zero hq hb (show reflectionPath f 0 = 0 from reflected_zero f)
  change f a-runningMinimum f a = 0 at hz
  have he : f a = minimumValue t f := by
    change f a = runningMinimum f t
    rw [hm]
    linarith
  exact ⟨he,(excursion_endpoints_closed f (t : ℝ) hq hb).trans he⟩

theorem leftEndpoint_eq_leastMinimizer (f : Path) (t : ℝ≥0)
    (hq : (t : ℝ) ∈ positiveSet (reflectionPath f))
    (hb : BddAbove (component (reflectionPath f) (t : ℝ)))
    (hunique : ∀ u : ℝ≥0, u ≤ t → f u = minimumValue t f → u = leastMinimizer t f) :
    leftEndpoint (t : ℝ) (reflectionPath f) = (leastMinimizer t f : ℝ) := by
  have ht := (component_times f t hq hb).1.le
  have he := hunique _ ht (component_driver_endpoints_eq_prefix_minimum f t hq hb).1
  have hleft := (endpoint_bounds hq hb).1
  have h := congrArg (fun u : ℝ≥0 ↦ (u : ℝ)) he
  rwa [Real.coe_toNNReal _ hleft] at h

theorem rightEndpoint_eq_add_firstPassage (f : Path) (t : ℝ≥0)
    (hq : (t : ℝ) ∈ positiveSet (reflectionPath f))
    (hb : BddAbove (component (reflectionPath f) (t : ℝ))) :
    rightEndpoint (t : ℝ) (reflectionPath f) = (t : ℝ)+
      ((firstPassage (-reflectionPath f t) (futurePath t f)).toNNReal : ℝ) := by
  let b := Real.toNNReal (rightEndpoint (t : ℝ) (reflectionPath f))
  have htimes := component_times f t hq hb
  have ht : t < b := htimes.2.1
  have hend := (component_driver_endpoints_eq_prefix_minimum f t hq hb).2
  have hhit : futurePath t f (b-t) = -reflectionPath f t := by
    rw [futurePath_eval,add_tsub_cancel_of_le ht.le,hend]
    change runningMinimum f t-f t = -(f t-runningMinimum f t)
    ring
  have hle : firstPassage (-reflectionPath f t) (futurePath t f) ≤ (b-t : ℝ≥0) :=
    (firstPassage_le_iff _ _ _).mpr ⟨b-t,le_rfl,hhit.le⟩
  have hfin : firstPassage (-reflectionPath f t) (futurePath t f) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  let r := (firstPassage (-reflectionPath f t) (futurePath t f)).toNNReal
  have hrl : r ≤ b-t := by
    exact ENNReal.coe_le_coe.mp (by rwa [ENNReal.coe_toNNReal hfin])
  have hr : r = b-t := by
    apply le_antisymm hrl
    by_contra h
    have hlt : r < b-t := lt_of_not_ge h
    have hur : t+r < b := (lt_tsub_iff_left).mp hlt
    have hpos := htimes.2.2 (t+r) ⟨htimes.1.trans_le (le_add_of_nonneg_right zero_le),hur⟩
    have hm := runningMinimum_constant_on_positive_interval f
      (Real.toNNReal (leftEndpoint (t : ℝ) (reflectionPath f))) b
      (htimes.1.trans ht) htimes.2.2
    have hsame : runningMinimum f (t+r) = runningMinimum f t :=
      (hm _ ⟨htimes.1.le.trans (le_add_of_nonneg_right zero_le),hur.le⟩).trans
        (hm t ⟨htimes.1.le,ht.le⟩).symm
    have hsub := firstPassage_attained (-reflectionPath f t) (futurePath t f) hfin
    change f (t+r)-f t ≤ -(f t-runningMinimum f t) at hsub
    change 0 < f (t+r)-runningMinimum f (t+r) at hpos
    rw [hsame] at hpos
    linarith
  have hb0 := rightEndpoint_nonneg (t : ℝ) (reflectionPath f)
  have hbr : (b : ℝ) = rightEndpoint (t : ℝ) (reflectionPath f) := Real.coe_toNNReal _ hb0
  change _ = (t : ℝ)+(r : ℝ)
  rw [hr,← hbr,NNReal.coe_sub ht.le]
  ring

private theorem ae_component_bddAbove (lambda : ℝ) (q : ℝ) :
    ∀ᵐ f ∂pathLaw, BddAbove (component (driftedReflectionPath lambda f) q) := by
  have hfin : ∀ᵐ f ∂pathLaw, ∀ n : ℕ,
      firstPassage (-(n : ℝ)) (driftPath lambda f) ≠ ⊤ :=
    ae_all_iff.mpr (fun n ↦
      BrownianParabolicFirstPassageFinite.ae_parabolicFirstPassage_ne_top lambda (-(n : ℝ)))
  filter_upwards [hfin] with f hf
  let g := driftPath lambda f
  obtain ⟨n,hn⟩ := exists_nat_gt (-runningMinimum g (Real.toNNReal q))
  have hlt : g (firstPassage (-(n : ℝ)) g).toNNReal <
      runningMinimum g (Real.toNNReal q) := by
    have h := firstPassage_attained (-(n : ℝ)) g (hf n)
    linarith
  obtain ⟨u,hu,hz⟩ := ReflectionExcursionReturns.exists_zero_after_of_lt_minimum
    (continuous_path g) hlt
  have hqu : q < (u : ℝ) := (Real.le_coe_toNNReal q).trans_lt hu.1
  have hzero : BrownianWindowExcursions.realEval (reflectionPath g) (u : ℝ) = 0 := by
    change reflected g (Real.toNNReal (u : ℝ)) = 0
    rw [Real.toNNReal_coe]
    exact hz
  exact ⟨(u : ℝ),fun r hr ↦ (component_lt_zero hqu hzero r hr).le⟩

theorem ae_actual_parabolic_anchor_endpoints (lambda : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ f ∂pathLaw, (t : ℝ) ∈ positiveSet (driftedReflectionPath lambda f) ∧
      leftEndpoint (t : ℝ) (driftedReflectionPath lambda f) =
        (leastMinimizer t (driftPath lambda f) : ℝ) ∧
      rightEndpoint (t : ℝ) (driftedReflectionPath lambda f) = (t : ℝ)+
        ((firstPassage (-driftedReflectionPath lambda f t)
          (driftPath (lambda-(t : ℝ)) (futurePath t f))).toNNReal : ℝ) := by
  filter_upwards [BrownianPathMinimumUnique.ae_actual_parabolic_unique_minimum lambda t ht,
    BrownianParabolicMinimumSplitWindow.ae_actual_minimum_geometry lambda t ht,
    ae_component_bddAbove lambda (t : ℝ)] with f hu hm hb
  have hpos : 0 < driftedReflectionPath lambda f t := by
    have hle := minimumValue_le t (driftPath lambda f) t le_rfl
    have hne : driftPath lambda f t ≠ minimumValue t (driftPath lambda f) := by
      intro he
      have h := hu t le_rfl he
      exact (ne_of_lt hm.2.2) h.symm
    change 0 < driftPath lambda f t-runningMinimum (driftPath lambda f) t
    exact sub_pos.mpr (lt_of_le_of_ne hle hne.symm)
  have hq : (t : ℝ) ∈ positiveSet (driftedReflectionPath lambda f) := by
    refine ⟨ht,?_⟩
    change 0 < driftedReflectionPath lambda f (Real.toNNReal (t : ℝ))
    simpa only [Real.toNNReal_coe] using hpos
  refine ⟨hq,leftEndpoint_eq_leastMinimizer (driftPath lambda f) t hq hb hu,?_⟩
  rw [← BrownianParabolicFirstPassageStrongMarkov.actual_drift_futurePath_eq_shift]
  exact rightEndpoint_eq_add_firstPassage (driftPath lambda f) t hq hb

end PerronWright.BrownianParabolicExcursionAnchor
