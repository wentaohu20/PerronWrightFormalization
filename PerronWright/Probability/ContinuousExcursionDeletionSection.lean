import PerronWright.Probability.ContinuousExcursionDeletionComponents

/-! # Genuine reselected rational representatives after deleting a component

The map acts on actual connected intervals. Only after transporting an
interval is its unique least rational-code representative reselected.
No rationality of the removed length or of a translated anchor is used.
-/

open MeasureTheory Topology Set
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ContinuousExcursionDeletionSection

open BrownianPathLaw FullHorizonExcursionComponents FullHorizonExcursionSection
open BrownianWindowExcursions (realEval)
open ContinuousPathIntervalDeletion ContinuousExcursionDeletionComponents

def eraseTime (a l : ℝ≥0) (t : ℝ) : ℝ := if t < a then t else t-l

private def restoreTime (a l : ℝ≥0) (t : ℝ) : ℝ := if t < a then t else t+l

private theorem eval_before (f : Path) (a l : ℝ≥0) (t : ℝ) (ht : t ≤ a) :
    realEval (deletionPath a l f) t = realEval f t := by
  change deletionPath a l f (Real.toNNReal t) = f (Real.toNNReal t)
  rw [deletionPath_apply,if_pos (Real.toNNReal_le_iff_le_coe.mpr ht)]

private theorem eval_after (f : Path) (a l : ℝ≥0) (t : ℝ) (ht : (a : ℝ) < t)
    (hclosed : f (a+l) = f a) :
    realEval (deletionPath a l f) t = realEval f (t+l) := by
  change deletionPath a l f (Real.toNNReal t) = f (Real.toNNReal (t+l))
  rw [deletionPath_closed_apply a l f hclosed,
    if_neg (fun h ↦ (not_le.mpr ht) (Real.toNNReal_le_iff_le_coe.mp h))]
  have hs : Real.toNNReal (t+(l : ℝ)) = Real.toNNReal t+l := by
    simpa only [Real.toNNReal_coe] using
      (Real.toNNReal_add (r := t) (p := (l : ℝ)) (a.2.trans ht.le) l.2)
  exact congrArg f hs.symm

theorem surviving_anchor_side (f : Path) (a l : ℝ≥0) (q r : ℝ)
    (hz : f a = 0) (he : f (a+l) = 0)
    (hc : component f q = Ioo (a : ℝ) (a+l : ℝ≥0))
    (hr : r ∈ positiveSet f) (hn : component f r ≠ component f q) :
    r < a ∨ (a+l : ℝ≥0) < r := by
  have hza : realEval f (a : ℝ) = 0 := by simpa [realEval] using hz
  have hzb : realEval f (a+l : ℝ≥0) = 0 := by simpa [realEval] using he
  by_cases hra : r < a
  · exact Or.inl hra
  · right
    by_contra hbr
    have har : (a : ℝ) < r := by
      have hle : (a : ℝ) ≤ r := le_of_not_gt hra
      rcases hle.eq_or_lt with h | h
      · have hp := hr.2
        change 0 < realEval f r at hp
        rw [← h,hza] at hp
        exact (lt_irrefl _ hp).elim
      · exact h
    have hrb : r < (a+l : ℝ≥0) := by
      rcases (le_of_not_gt hbr).eq_or_lt with h | h
      · have hp := hr.2
        change 0 < realEval f r at hp
        rw [h,hzb] at hp
        exact (lt_irrefl _ hp).elim
      · exact h
    have hm : r ∈ component f q := by rw [hc]; exact ⟨har,hrb⟩
    exact hn (component_eq_of_mem hm).symm

theorem transported_component (f : Path) (a l : ℝ≥0) (q r : ℝ)
    (hz : f a = 0) (he : f (a+l) = 0)
    (hc : component f q = Ioo (a : ℝ) (a+l : ℝ≥0))
    (hr : r ∈ positiveSet f) (hn : component f r ≠ component f q) :
    component (deletionPath a l f) (eraseTime a l r) = eraseTime a l '' component f r := by
  rcases surviving_anchor_side f a l q r hz he hc hr hn with hra | hbr
  · rw [eraseTime,if_pos hra,component_before_deletion f a l r hr hra hz]
    symm
    apply Set.EqOn.image_eq_self
    intro t ht
    have hza : realEval f (a : ℝ) = 0 := by simpa [realEval] using hz
    simp only [eraseTime,if_pos (component_lt_zero hra hza t ht),id_eq]
  · have hh : (a : ℝ) ≤ (a+l : ℝ≥0) := by
      simp only [NNReal.coe_add]
      linarith [l.2]
    rw [eraseTime,if_neg (not_lt.mpr (hh.trans hbr.le)),
        component_after_deletion f a l r hr hbr hz he]
    apply image_congr
    intro t ht
    have hzb : realEval f (a+l : ℝ≥0) = 0 := by simpa [realEval] using he
    have hbt := component_gt_zero hbr hzb t ht
    have hat : (a : ℝ) < t := by
      have hh : (a : ℝ) ≤ (a+l : ℝ≥0) := by simp only [NNReal.coe_add]; linarith [l.2]
      exact hh.trans_lt hbt
    simp only [eraseTime,if_neg (not_lt.mpr hat.le)]

private theorem restore_erased_component (f : Path) (a l : ℝ≥0) (q r : ℝ)
    (hz : f a = 0) (he : f (a+l) = 0)
    (hc : component f q = Ioo (a : ℝ) (a+l : ℝ≥0))
    (hn : component f r ≠ component f q) :
    restoreTime a l '' (eraseTime a l '' component f r) = component f r := by
  rw [image_image]
  apply Set.EqOn.image_eq_self
  intro t ht
  have htpos := component_subset f r ht
  have htn : component f t ≠ component f q := by
    rw [← component_eq_of_mem ht]
    exact hn
  rcases surviving_anchor_side f a l q t hz he hc htpos htn with hta | hbt
  · simp only [eraseTime,restoreTime,if_pos hta,id_eq]
  · have hat : (a : ℝ) < t-l := by
      simpa only [NNReal.coe_add,add_sub_cancel_right] using sub_lt_sub_right hbt l
    have hat' : ¬t < (a : ℝ) := by linarith [l.2]
    simp only [eraseTime,if_neg hat',restoreTime,
      if_neg (not_lt.mpr hat.le),sub_add_cancel,id_eq]

private theorem restored_active (f : Path) (a l : ℝ≥0) (q s : ℝ)
    (hz : f a = 0) (he : f (a+l) = 0)
    (hc : component f q = Ioo (a : ℝ) (a+l : ℝ≥0))
    (hs : s ∈ positiveSet (deletionPath a l f)) :
    restoreTime a l s ∈ positiveSet f ∧
      component f (restoreTime a l s) ≠ component f q ∧
        eraseTime a l (restoreTime a l s) = s := by
  have hclosed := he.trans hz.symm
  have hzD : realEval (deletionPath a l f) (a : ℝ) = 0 := by
    rw [eval_before f a l a le_rfl]
    simpa [realEval] using hz
  have hne : s ≠ (a : ℝ) := by
    intro h
    have hp := hs.2
    change 0 < realEval (deletionPath a l f) s at hp
    rw [h,hzD] at hp
    exact lt_irrefl _ hp
  rcases lt_or_gt_of_ne hne with hsa | has
  · have hp : s ∈ positiveSet f := by
      refine ⟨hs.1,?_⟩
      change 0 < realEval f s
      rw [← eval_before f a l s hsa.le]
      exact hs.2
    simp only [restoreTime,eraseTime,if_pos hsa]
    refine ⟨hp,?_,True.intro⟩
    intro h
    have hm := mem_component_self hp
    rw [h,hc] at hm
    exact (not_lt_of_ge hsa.le) hm.1
  · have hbs : (a+l : ℝ≥0) < s+l := by
      simp only [NNReal.coe_add]
      linarith
    have hsat : ¬s < (a : ℝ) := not_lt.mpr has.le
    have hsat' : ¬s+l < (a : ℝ) := by linarith [l.2]
    have hp : s+l ∈ positiveSet f := by
      refine ⟨add_pos_of_pos_of_nonneg hs.1 l.2,?_⟩
      change 0 < realEval f (s+l)
      rw [← eval_after f a l s has hclosed]
      exact hs.2
    simp only [restoreTime,if_neg hsat,eraseTime,if_neg hsat',add_sub_cancel_right]
    refine ⟨hp,?_,True.intro⟩
    intro h
    have hm := mem_component_self hp
    rw [h,hc] at hm
    exact (not_lt_of_ge hbs.le) hm.2

theorem representativeEquiv_exists (f : Path) (a l : ℝ≥0) (q : ℝ)
    (hz : f a = 0) (he : f (a+l) = 0)
    (hc : component f q = Ioo (a : ℝ) (a+l : ℝ≥0)) :
    ∃ E : {r : ℚ // Representative f r ∧ component f (r : ℝ) ≠ component f q} ≃
        {r : ℚ // Representative (deletionPath a l f) r},
      ∀ r, component (deletionPath a l f) ((E r).1 : ℝ) =
        eraseTime a l '' component f (r.1 : ℝ) := by
  let A := {r : ℚ // Representative f r ∧ component f (r : ℝ) ≠ component f q}
  let B := {r : ℚ // Representative (deletionPath a l f) r}
  have hforward (r : A) : ∃ s : B, component (deletionPath a l f) (s.1 : ℝ) =
      eraseTime a l '' component f (r.1 : ℝ) := by
    have ht := transported_component f a l q r.1 hz he hc r.2.1.1 r.2.2
    have hactive : eraseTime a l (r.1 : ℝ) ∈ positiveSet (deletionPath a l f) :=
      (component_nonempty_iff _ _).mp (by
        rw [ht]
        exact ((component_nonempty_iff f r.1).mpr r.2.1.1).image _)
    obtain ⟨s,hs,hcs⟩ := exists_representative hactive
    exact ⟨⟨s,hs⟩,hcs.trans ht⟩
  let F : A → B := fun r ↦ Classical.choose (hforward r)
  have hF (r : A) : component (deletionPath a l f) ((F r).1 : ℝ) =
      eraseTime a l '' component f (r.1 : ℝ) := Classical.choose_spec (hforward r)
  have hinj : Function.Injective F := by
    intro r t hrt
    have hi : eraseTime a l '' component f (r.1 : ℝ) =
        eraseTime a l '' component f (t.1 : ℝ) := by rw [← hF r,← hF t,hrt]
    have hir := congrArg (fun s : Set ℝ ↦ restoreTime a l '' s) hi
    rw [restore_erased_component f a l q r.1 hz he hc r.2.2,
      restore_erased_component f a l q t.1 hz he hc t.2.2] at hir
    exact Subtype.ext (representatives_eq_of_component_eq r.2.1 t.2.1 hir)
  have hsurj : Function.Surjective F := by
    intro s
    have hs := restored_active f a l q s.1 hz he hc s.2.1
    obtain ⟨r,hr,hcr⟩ := exists_representative hs.1
    have hrn : component f (r : ℝ) ≠ component f q := by rw [hcr]; exact hs.2.1
    let rr : A := ⟨r,hr,hrn⟩
    have hcs : component (deletionPath a l f) ((F rr).1 : ℝ) =
        component (deletionPath a l f) (s.1 : ℝ) := by
      apply component_eq_of_mem
      rw [hF rr,hcr]
      exact ⟨restoreTime a l (s.1 : ℝ),mem_component_self hs.1,hs.2.2⟩
    exact ⟨rr,Subtype.ext (representatives_eq_of_component_eq (F rr).2 s.2 hcs)⟩
  exact ⟨Equiv.ofBijective F ⟨hinj,hsurj⟩,hF⟩

end PerronWright.ContinuousExcursionDeletionSection
