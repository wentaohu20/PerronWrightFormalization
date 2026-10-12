import PerronWright.Probability.ContinuousExcursionDeletionReflection
import PerronWright.Probability.BrownianFullHorizonExcursionAreas

/-! # Literal remaining excursion components after an actual interval deletion

The zero cut separates the unchanged prefix from the translated suffix.
Components correspond as actual subsets of real time, not by assuming
that rational representative labels survive a nonrational translation.
-/

open MeasureTheory Topology Set
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ContinuousExcursionDeletionComponents

open BrownianPathLaw BrownianPathReflectionLaw
open BrownianWindowExcursions (realEval)
open ContinuousPathIntervalDeletion FullHorizonExcursionComponents

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

theorem component_gt_zero {f : Path} {q z : ℝ} (hzq : z < q)
    (hz : realEval f z = 0) : ∀ t ∈ component f q, z < t := by
  intro t ht
  have hq := (component_nonempty_iff f q).mp ⟨t,ht⟩
  by_contra h
  have htz : t ≤ z := le_of_not_gt h
  have hc : z ∈ component f q := (component_ordConnected f q).uIcc_subset ht
    (mem_component_self hq) (mem_uIcc.mpr (Or.inl ⟨htz,hzq.le⟩))
  have hp := (component_subset f q hc).2
  change 0 < realEval f z at hp
  simp only [hz,lt_self_iff_false] at hp

theorem component_before_deletion (f : Path) (a l : ℝ≥0) (q : ℝ)
    (hq : q ∈ positiveSet f) (hqa : q < a) (hzero : f a = 0) :
    component (deletionPath a l f) q = component f q := by
  have hz : realEval f (a : ℝ) = 0 := by simpa [realEval] using hzero
  have hzD : realEval (deletionPath a l f) (a : ℝ) = 0 := by
    rw [eval_before f a l a le_rfl,hz]
  have hqD : q ∈ positiveSet (deletionPath a l f) := by
    refine ⟨hq.1,?_⟩
    change 0 < realEval (deletionPath a l f) q
    rw [eval_before f a l q hqa.le]
    exact hq.2
  apply Subset.antisymm
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_component_self hqD) (by
        intro t ht
        have hta := component_lt_zero hqa hzD t ht
        have hp := component_subset (deletionPath a l f) q ht
        refine ⟨hp.1,?_⟩
        change 0 < realEval f t
        rw [← eval_before f a l t hta.le]
        exact hp.2)
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_component_self hq) (by
        intro t ht
        have hta := component_lt_zero hqa hz t ht
        have hp := component_subset f q ht
        refine ⟨hp.1,?_⟩
        change 0 < realEval (deletionPath a l f) t
        rw [eval_before f a l t hta.le]
        exact hp.2)

theorem component_after_deletion (f : Path) (a l : ℝ≥0) (q : ℝ)
    (hq : q ∈ positiveSet f) (haq : (a+l : ℝ≥0) < q)
    (hzero : f a = 0) (hend : f (a+l) = 0) :
    component (deletionPath a l f) (q-l) =
      (fun t : ℝ ↦ t-l) '' component f q := by
  have hclosed : f (a+l) = f a := hend.trans hzero.symm
  have hz : realEval f (a+l : ℝ≥0) = 0 := by simpa [realEval] using hend
  have hzD : realEval (deletionPath a l f) (a : ℝ) = 0 := by
    rw [eval_before f a l a le_rfl]
    simpa [realEval] using hzero
  have haq' : (a : ℝ) < q-l := by
    simpa only [NNReal.coe_add,add_sub_cancel_right] using sub_lt_sub_right haq l
  have hqD : q-l ∈ positiveSet (deletionPath a l f) := by
    refine ⟨a.2.trans_lt haq',?_⟩
    change 0 < realEval (deletionPath a l f) (q-l)
    rw [eval_after f a l (q-l) haq' hclosed,sub_add_cancel]
    exact hq.2
  have hforward : (fun t : ℝ ↦ t-l) '' component f q ⊆
      component (deletionPath a l f) (q-l) := by
    apply (isPreconnected_connectedComponentIn.image _
      (continuous_id.sub continuous_const).continuousOn).subset_connectedComponentIn
        (mem_image_of_mem _ (mem_component_self hq))
    rintro t ⟨u,hu,rfl⟩
    have hau := component_gt_zero haq hz u hu
    have hat : (a : ℝ) < u-l := by
      simpa only [NNReal.coe_add,add_sub_cancel_right] using sub_lt_sub_right hau l
    refine ⟨a.2.trans_lt hat,?_⟩
    change 0 < realEval (deletionPath a l f) (u-l)
    rw [eval_after f a l (u-l) hat hclosed,sub_add_cancel]
    exact (component_subset f q hu).2
  have hbackward : (fun t : ℝ ↦ t+l) '' component (deletionPath a l f) (q-l) ⊆
      component f q := by
    apply (isPreconnected_connectedComponentIn.image _
      (continuous_id.add continuous_const).continuousOn).subset_connectedComponentIn
        (by exact ⟨q-l,mem_component_self hqD,sub_add_cancel q l⟩)
    rintro t ⟨u,hu,rfl⟩
    have hau := component_gt_zero haq' hzD u hu
    have hp := component_subset (deletionPath a l f) (q-l) hu
    refine ⟨add_pos_of_pos_of_nonneg hp.1 l.2,?_⟩
    change 0 < realEval f (u+l)
    rw [← eval_after f a l u hau hclosed]
    exact hp.2
  apply Subset.antisymm
  · intro t ht
    exact ⟨t+l,hbackward ⟨t,ht,rfl⟩,add_sub_cancel_right t l⟩
  · exact hforward

theorem endpoints_before_deletion (f : Path) (a l : ℝ≥0) (q : ℝ)
    (hq : q ∈ positiveSet f) (hqa : q < a) (hzero : f a = 0) :
    leftEndpoint q (deletionPath a l f) = leftEndpoint q f ∧
      rightEndpoint q (deletionPath a l f) = rightEndpoint q f := by
  have he := component_before_deletion f a l q hq hqa hzero
  have hqD : q ∈ positiveSet (deletionPath a l f) :=
    (component_nonempty_iff _ _).mp ⟨q,by rw [he]; exact mem_component_self hq⟩
  simp only [leftEndpoint,rightEndpoint,if_pos hqD,if_pos hq,he,and_self]

theorem endpoints_after_deletion (f : Path) (a l : ℝ≥0) (q : ℝ)
    (hq : q ∈ positiveSet f) (haq : (a+l : ℝ≥0) < q)
    (hzero : f a = 0) (hend : f (a+l) = 0) (hb : BddAbove (component f q)) :
    leftEndpoint (q-l) (deletionPath a l f) = leftEndpoint q f-l ∧
      rightEndpoint (q-l) (deletionPath a l f) = rightEndpoint q f-l := by
  have he := component_after_deletion f a l q hq haq hzero hend
  have hqD : q-l ∈ positiveSet (deletionPath a l f) :=
    (component_nonempty_iff _ _).mp ⟨q-l,by rw [he]; exact mem_image_of_mem _ (mem_component_self hq)⟩
  have hne := (component_nonempty_iff f q).mpr hq
  simp only [leftEndpoint,rightEndpoint,if_pos hqD,if_pos hq,he]
  constructor
  · simpa only [OrderIso.addRight_apply,sub_eq_add_neg] using
      ((OrderIso.addRight (-(l : ℝ))).map_csInf' hne (component_bddBelow f q)).symm
  · simpa only [OrderIso.addRight_apply,sub_eq_add_neg] using
      ((OrderIso.addRight (-(l : ℝ))).map_csSup' hne hb).symm

theorem length_before_deletion (f : Path) (a l : ℝ≥0) (q : ℝ)
    (hq : q ∈ positiveSet f) (hqa : q < a) (hzero : f a = 0) :
    FullHorizonExcursionComponents.length q (deletionPath a l f) =
      FullHorizonExcursionComponents.length q f := by
  have he := endpoints_before_deletion f a l q hq hqa hzero
  simp only [FullHorizonExcursionComponents.length,he.1,he.2]

theorem length_after_deletion (f : Path) (a l : ℝ≥0) (q : ℝ)
    (hq : q ∈ positiveSet f) (haq : (a+l : ℝ≥0) < q)
    (hzero : f a = 0) (hend : f (a+l) = 0) (hb : BddAbove (component f q)) :
    FullHorizonExcursionComponents.length (q-l) (deletionPath a l f) =
      FullHorizonExcursionComponents.length q f := by
  have he := endpoints_after_deletion f a l q hq haq hzero hend hb
  simp only [FullHorizonExcursionComponents.length,he.1,he.2]
  ring

theorem component_integral_before_deletion (f : Path) (a l : ℝ≥0) (q : ℝ)
    (hq : q ∈ positiveSet f) (hqa : q < a) (hzero : f a = 0) :
    ∫ t in component (deletionPath a l f) q, realEval (deletionPath a l f) t =
      ∫ t in component f q, realEval f t := by
  rw [component_before_deletion f a l q hq hqa hzero]
  apply setIntegral_congr_fun (isOpen_component f q).measurableSet
  intro t ht
  have hz : realEval f (a : ℝ) = 0 := by simpa [realEval] using hzero
  exact eval_before f a l t (component_lt_zero hqa hz t ht).le

theorem component_integral_after_deletion (f : Path) (a l : ℝ≥0) (q : ℝ)
    (hq : q ∈ positiveSet f) (haq : (a+l : ℝ≥0) < q)
    (hzero : f a = 0) (hend : f (a+l) = 0) :
    ∫ t in component (deletionPath a l f) (q-l), realEval (deletionPath a l f) t =
      ∫ t in component f q, realEval f t := by
  have he := component_after_deletion f a l q hq haq hzero hend
  have hset : component (deletionPath a l f) (q-l) =
      (fun t : ℝ ↦ t+l) ⁻¹' component f q := by
    rw [he]
    ext t
    constructor
    · rintro ⟨u,hu,rfl⟩
      simpa only [mem_preimage,sub_add_cancel] using hu
    · intro ht
      exact ⟨t+l,ht,add_sub_cancel_right t l⟩
  have haq' : (a : ℝ) < q-l := by
    simpa only [NNReal.coe_add,add_sub_cancel_right] using sub_lt_sub_right haq l
  have hzD : realEval (deletionPath a l f) (a : ℝ) = 0 := by
    rw [eval_before f a l a le_rfl]
    simpa [realEval] using hzero
  calc
    _ = ∫ t in component (deletionPath a l f) (q-l), realEval f (t+l) := by
      apply setIntegral_congr_fun (isOpen_component _ _).measurableSet
      intro t ht
      exact eval_after f a l t (component_gt_zero haq' hzD t ht) (hend.trans hzero.symm)
    _ = ∫ t in component f q, realEval f t := by
      rw [hset]
      have hm := (Homeomorph.addRight (l : ℝ)).isClosedEmbedding.measurableEmbedding.setIntegral_map
        (μ := (volume : Measure ℝ)) (realEval f) (component f q)
      change (∫ y in component f q, realEval f y
        ∂Measure.map (fun x : ℝ ↦ x+l) volume) =
          ∫ x in (fun x : ℝ ↦ x+l) ⁻¹' component f q, realEval f (x+l) at hm
      rw [map_add_right_eq_self] at hm
      exact hm.symm

end PerronWright.ContinuousExcursionDeletionComponents
