import PerronWright.Probability.ContinuousPathIntervalDeletion
import PerronWright.Probability.FullHorizonExcursionEndpoints

/-! # Genuine excursion closure and reflection after deletion

Strict reflected positivity forces the actual running minimum to remain
constant on the full excursion interval. Hence the unreflected endpoints
agree. Removing this interval does not remove a smaller past minimum,
and therefore reflection commutes with the literal continuous splice.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ContinuousExcursionDeletionReflection

open BrownianPathLaw BrownianPathReflectionLaw ContinuousPathReflection
open ContinuousPathIntervalDeletion FullHorizonExcursionComponents FullHorizonExcursionEndpoints

theorem runningMinimum_constant_on_positive_interval (f : Path) (a b : ℝ≥0)
    (hab : a < b) (hpos : ∀ t ∈ Ioo a b, 0 < reflectionPath f t) :
    ∀ t ∈ Icc a b, runningMinimum f t = runningMinimum f a := by
  have hint : Ioo a b ⊆ {t | runningMinimum f t = runningMinimum f a} := by
    intro t ht
    apply le_antisymm ((runningMinimum_antitone (continuous_path f)) ht.1.le)
    obtain ⟨u,hu,he⟩ := runningMinimum_attained (continuous_path f) t
    by_cases hua : u ≤ a
    · rw [he]
      exact runningMinimum_le (continuous_path f) hua
    · have hpu := hpos u ⟨lt_of_not_ge hua,hu.2.trans_lt ht.2⟩
      have hm := (runningMinimum_antitone (continuous_path f)) hu.2
      change 0 < f u-runningMinimum f u at hpu
      linarith
  have hc : IsClosed {t | runningMinimum f t = runningMinimum f a} :=
    isClosed_eq (continuous_runningMinimum (continuous_path f)) continuous_const
  have hcl := hc.closure_subset_iff.mpr hint
  intro t ht
  exact hcl (by rw [closure_Ioo hab.ne]; exact ht)

theorem excursion_endpoints_closed (f : Path) (q : ℝ)
    (hq : q ∈ positiveSet (reflectionPath f))
    (hb : BddAbove (component (reflectionPath f) q)) :
    f (Real.toNNReal (rightEndpoint q (reflectionPath f))) =
      f (Real.toNNReal (leftEndpoint q (reflectionPath f))) := by
  let a := Real.toNNReal (leftEndpoint q (reflectionPath f))
  let b := Real.toNNReal (rightEndpoint q (reflectionPath f))
  have hbound := endpoint_bounds hq hb
  have ha : (a : ℝ) = leftEndpoint q (reflectionPath f) := Real.coe_toNNReal _ hbound.1
  have hb' : (b : ℝ) = rightEndpoint q (reflectionPath f) :=
    Real.coe_toNNReal _ (hbound.1.trans (hbound.2.1.trans hbound.2.2).le)
  have hab : a < b := NNReal.coe_lt_coe.mp (by rw [ha,hb']; exact hbound.2.1.trans hbound.2.2)
  have hpos : ∀ t ∈ Ioo a b, 0 < reflectionPath f t := by
    intro t ht
    have htr : (t : ℝ) ∈ component (reflectionPath f) q := by
      rw [component_eq_Ioo hq hb]
      exact ⟨by rw [← ha]; exact ht.1,by rw [← hb']; exact ht.2⟩
    have hp := (component_subset (reflectionPath f) q htr).2
    change 0 < reflectionPath f (Real.toNNReal (t : ℝ)) at hp
    simpa only [Real.toNNReal_coe] using hp
  have hm := runningMinimum_constant_on_positive_interval f a b hab hpos b ⟨hab.le,le_rfl⟩
  have hza := leftEndpoint_zero hq hb (show reflectionPath f 0 = 0 from reflected_zero f)
  have hzb := rightEndpoint_zero hq hb
  change f a-runningMinimum f a = 0 at hza
  change f b-runningMinimum f b = 0 at hzb
  change f b = f a
  linarith

theorem runningMinimum_deletion (f : Path) (a l : ℝ≥0)
    (hclosed : f (a+l) = f a) (hfloor : ∀ u ∈ Icc a (a+l), f a ≤ f u) (t : ℝ≥0) :
    runningMinimum (deletionPath a l f) t =
      if t ≤ a then runningMinimum f t else runningMinimum f (t+l) := by
  by_cases ht : t ≤ a
  · rw [if_pos ht]
    have h := runningMinimum_uniform_bound (continuous_path (deletionPath a l f))
      (continuous_path f) t (ε := 0) (by
        intro u hu
        rw [deletionPath_closed_apply a l f hclosed u,if_pos (hu.trans ht),sub_self,abs_zero])
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
  · rw [if_neg ht]
    have hat : a < t := lt_of_not_ge ht
    apply le_antisymm
    · obtain ⟨u,hu,he⟩ := runningMinimum_attained (continuous_path f) (t+l)
      rw [he]
      by_cases hua : u ≤ a
      · have hm := runningMinimum_le (continuous_path (deletionPath a l f)) (hua.trans hat.le)
        rwa [deletionPath_closed_apply a l f hclosed u,if_pos hua] at hm
      · by_cases huend : u ≤ a+l
        · have hm := runningMinimum_le (continuous_path (deletionPath a l f)) hat.le
          rw [deletionPath_closed_apply a l f hclosed a,if_pos le_rfl] at hm
          exact hm.trans (hfloor u ⟨(lt_of_not_ge hua).le,huend⟩)
        · have hlu : l ≤ u := (show l ≤ a+l from
            NNReal.coe_le_coe.mp (by simp only [NNReal.coe_add]; linarith [a.2])).trans
              (lt_of_not_ge huend).le
          have hv : a < u-l := by
            apply NNReal.coe_lt_coe.mp
            rw [NNReal.coe_sub hlu]
            have h := lt_of_not_ge huend
            exact (lt_sub_iff_add_lt).mpr h
          have hvt : u-l ≤ t := tsub_le_iff_right.mpr hu.2
          have hm := runningMinimum_le (continuous_path (deletionPath a l f)) hvt
          rwa [deletionPath_closed_apply a l f hclosed (u-l),if_neg (not_le.mpr hv),
            tsub_add_cancel_of_le hlu] at hm
    · obtain ⟨u,hu,he⟩ := runningMinimum_attained (continuous_path (deletionPath a l f)) t
      rw [he,deletionPath_closed_apply a l f hclosed u]
      split_ifs with hua
      · exact runningMinimum_le (continuous_path f) (hu.2.trans
          (NNReal.coe_le_coe.mp (by simp only [NNReal.coe_add]; linarith [l.2])))
      · apply runningMinimum_le (continuous_path f)
        gcongr
        exact hu.2

theorem reflection_deletion_eq_of_closed_floor (f : Path) (a l : ℝ≥0)
    (hclosed : f (a+l) = f a) (hfloor : ∀ u ∈ Icc a (a+l), f a ≤ f u) :
    reflectionPath (deletionPath a l f) = deletionPath a l (reflectionPath f) := by
  have hmin : runningMinimum f (a+l) = runningMinimum f a := by
    apply le_antisymm ((runningMinimum_antitone (continuous_path f))
      (NNReal.coe_le_coe.mp (by simp only [NNReal.coe_add]; linarith [l.2])))
    obtain ⟨u,hu,he⟩ := runningMinimum_attained (continuous_path f) (a+l)
    rw [he]
    by_cases hua : u ≤ a
    · exact runningMinimum_le (continuous_path f) hua
    · exact (runningMinimum_le (continuous_path f) le_rfl).trans
        (hfloor u ⟨(lt_of_not_ge hua).le,hu.2⟩)
  have hR : reflectionPath f (a+l) = reflectionPath f a := by
    change f (a+l)-runningMinimum f (a+l) = f a-runningMinimum f a
    rw [hclosed,hmin]
  apply ContinuousMap.ext
  intro t
  change deletionPath a l f t-runningMinimum (deletionPath a l f) t =
    deletionPath a l (reflectionPath f) t
  rw [deletionPath_closed_apply a l f hclosed t,runningMinimum_deletion f a l hclosed hfloor t,
    deletionPath_closed_apply a l (reflectionPath f) hR t]
  split_ifs <;> rfl

theorem parabolic_excursion_deletion_eq (lambda : ℝ) (f : Path) (q : ℝ)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hb : BddAbove (component (driftedReflectionPath lambda f) q)) :
    let a := Real.toNNReal (leftEndpoint q (driftedReflectionPath lambda f))
    let b := Real.toNNReal (rightEndpoint q (driftedReflectionPath lambda f))
    let l := b-a
    driftedReflectionPath (lambda-(l : ℝ)) (correctedDeletionPath a l f) =
      deletionPath a l (driftedReflectionPath lambda f) := by
  dsimp only
  let g := driftPath lambda f
  have hqg : q ∈ positiveSet (reflectionPath g) := hq
  have hbg : BddAbove (component (reflectionPath g) q) := hb
  let a := Real.toNNReal (leftEndpoint q (reflectionPath g))
  let b := Real.toNNReal (rightEndpoint q (reflectionPath g))
  have hbound := endpoint_bounds hq hb
  have ha : (a : ℝ) = leftEndpoint q (reflectionPath g) := Real.coe_toNNReal _ hbound.1
  have hb' : (b : ℝ) = rightEndpoint q (reflectionPath g) :=
    Real.coe_toNNReal _ (hbound.1.trans (hbound.2.1.trans hbound.2.2).le)
  have hab : a < b := NNReal.coe_lt_coe.mp (by rw [ha,hb']; exact hbound.2.1.trans hbound.2.2)
  have he : a+(b-a) = b := add_tsub_cancel_of_le hab.le
  have hclosed : g (a+(b-a)) = g a := by
    rw [he]
    exact excursion_endpoints_closed g q hq hb
  have hpos : ∀ t ∈ Ioo a b, 0 < reflectionPath g t := by
    intro t ht
    have htr : (t : ℝ) ∈ component (reflectionPath g) q := by
      rw [component_eq_Ioo hqg hbg]
      exact ⟨by rw [← ha]; exact ht.1,by rw [← hb']; exact ht.2⟩
    have hp := (component_subset (reflectionPath g) q htr).2
    change 0 < reflectionPath g (Real.toNNReal (t : ℝ)) at hp
    simpa only [Real.toNNReal_coe] using hp
  have hzero := leftEndpoint_zero hq hb (show reflectionPath g 0 = 0 from reflected_zero g)
  change g a-runningMinimum g a = 0 at hzero
  have hfloor : ∀ u ∈ Icc a (a+(b-a)), g a ≤ g u := by
    intro u hu
    rw [he] at hu
    have hm := runningMinimum_constant_on_positive_interval g a b hab hpos u hu
    have hl := runningMinimum_le (continuous_path g) (s := u) (t := u) le_rfl
    rw [hm] at hl
    linarith
  change reflectionPath (driftPath (lambda-((b-a : ℝ≥0) : ℝ))
    (correctedDeletionPath a (b-a) f)) = deletionPath a (b-a) (reflectionPath g)
  rw [← parabolic_deletion_eq]
  exact reflection_deletion_eq_of_closed_floor g a (b-a) hclosed hfloor

end PerronWright.ContinuousExcursionDeletionReflection
