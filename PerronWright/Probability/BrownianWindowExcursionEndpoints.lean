import PerronWright.Probability.BrownianWindowExcursions
import Mathlib.Topology.Order.Monotone
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Actual measurable endpoints of bounded-window excursions

Every nonempty component is exactly the open interval between its genuine
infimum and supremum. The clipped endpoints lie in `[0,H]`; interior
endpoints are zeros of the path. Measurability is proved from countably
many rational component-membership events, not assumed as an interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianWindowExcursionEndpoints

open BrownianPathLaw BrownianWindowExcursions

def leftEndpoint (H q : ℝ) (f : Path) : ℝ :=
  if q ∈ positiveWindow H f then sInf (component H f q) else 0

def rightEndpoint (H q : ℝ) (f : Path) : ℝ :=
  if q ∈ positiveWindow H f then sSup (component H f q) else 0

def length (H q : ℝ) (f : Path) : ℝ := rightEndpoint H q f - leftEndpoint H q f

private theorem measurableSet_const_pred (p : Prop) : MeasurableSet {_f : Path | p} := by
  by_cases hp : p <;> simp [hp]

theorem component_bddBelow (H q : ℝ) (f : Path) : BddBelow (component H f q) :=
  ⟨0,fun _ ht ↦ (component_subset H f q ht).1.1.le⟩

theorem component_bddAbove (H q : ℝ) (f : Path) : BddAbove (component H f q) :=
  ⟨H,fun _ ht ↦ (component_subset H f q ht).1.2.le⟩

theorem leftEndpoint_lt_of_mem {H q t : ℝ} {f : Path} (ht : t ∈ component H f q) :
    leftEndpoint H q f < t := by
  have hq := (component_nonempty_iff H f q).mp ⟨t,ht⟩
  obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp ((isOpen_component H f q).mem_nhds ht)
  obtain ⟨u,hau,hut⟩ := exists_between hab.1
  have hu : u ∈ component H f q := hsub ⟨hau,hut.trans hab.2⟩
  simp only [leftEndpoint,if_pos hq]
  exact (csInf_le (component_bddBelow H q f) hu).trans_lt hut

theorem lt_rightEndpoint_of_mem {H q t : ℝ} {f : Path} (ht : t ∈ component H f q) :
    t < rightEndpoint H q f := by
  have hq := (component_nonempty_iff H f q).mp ⟨t,ht⟩
  obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp ((isOpen_component H f q).mem_nhds ht)
  obtain ⟨u,htu,hub⟩ := exists_between hab.2
  have hu : u ∈ component H f q := hsub ⟨hab.1.trans htu,hub⟩
  simp only [rightEndpoint,if_pos hq]
  exact htu.trans_le (le_csSup (component_bddAbove H q f) hu)

/-- These are actual connected intervals, not intervals supplied by a hypothesis. -/
theorem component_eq_Ioo {H q : ℝ} {f : Path} (hq : q ∈ positiveWindow H f) :
    component H f q = Ioo (leftEndpoint H q f) (rightEndpoint H q f) := by
  apply Subset.antisymm
  · intro t ht
    exact ⟨leftEndpoint_lt_of_mem ht,lt_rightEndpoint_of_mem ht⟩
  · simp only [leftEndpoint,rightEndpoint,if_pos hq]
    exact (component_isConnected hq).Ioo_csInf_csSup_subset
      (component_bddBelow H q f) (component_bddAbove H q f)

theorem endpoint_bounds {H q : ℝ} {f : Path} (hq : q ∈ positiveWindow H f) :
    0 ≤ leftEndpoint H q f ∧ leftEndpoint H q f < q ∧
      q < rightEndpoint H q f ∧ rightEndpoint H q f ≤ H := by
  have hn := (component_nonempty_iff H f q).mpr hq
  refine ⟨?_,leftEndpoint_lt_of_mem (mem_component_self hq),
    lt_rightEndpoint_of_mem (mem_component_self hq),?_⟩
  · simp only [leftEndpoint,if_pos hq]
    exact le_csInf hn (fun t ht ↦ (component_subset H f q ht).1.1.le)
  · simp only [rightEndpoint,if_pos hq]
    exact csSup_le hn (fun t ht ↦ (component_subset H f q ht).1.2.le)

theorem length_pos {H q : ℝ} {f : Path} (hq : q ∈ positiveWindow H f) : 0 < length H q f :=
  sub_pos.mpr ((endpoint_bounds hq).2.1.trans (endpoint_bounds hq).2.2.1)

theorem leftEndpoint_mem_closure {H q : ℝ} {f : Path} (hq : q ∈ positiveWindow H f) :
    leftEndpoint H q f ∈ closure (component H f q) := by
  simp only [leftEndpoint,if_pos hq]
  exact csInf_mem_closure ((component_nonempty_iff H f q).mpr hq) (component_bddBelow H q f)

theorem rightEndpoint_mem_closure {H q : ℝ} {f : Path} (hq : q ∈ positiveWindow H f) :
    rightEndpoint H q f ∈ closure (component H f q) := by
  simp only [rightEndpoint,if_pos hq]
  exact csSup_mem_closure ((component_nonempty_iff H f q).mpr hq) (component_bddAbove H q f)

theorem closure_component_inter_window_subset (H q : ℝ) (f : Path) :
    closure (component H f q) ∩ positiveWindow H f ⊆ component H f q := by
  rintro t ⟨ht,hwin⟩
  by_cases hq : q ∈ positiveWindow H f
  · have hp : IsPreconnected (insert t (component H f q)) :=
      (show IsPreconnected (component H f q) from isPreconnected_connectedComponentIn).subset_closure
        (subset_insert t _) (insert_subset ht subset_closure)
    exact hp.subset_connectedComponentIn (mem_insert_of_mem _ (mem_component_self hq))
      (insert_subset hwin (component_subset H f q)) (mem_insert t _)
  · have he : component H f q = ∅ := connectedComponentIn_eq_empty hq
    rw [he,closure_empty] at ht
    exact ht.elim

theorem nonneg_on_closure_component (H q : ℝ) (f : Path) :
    closure (component H f q) ⊆ {t | 0 ≤ realEval f t} := by
  apply closure_minimal _ (isClosed_le continuous_const (continuous_realEval f))
  intro t ht
  change 0 ≤ realEval f t
  exact (component_subset H f q ht).2.le

theorem leftEndpoint_zero_of_pos {H q : ℝ} {f : Path}
    (hq : q ∈ positiveWindow H f) (hl : 0 < leftEndpoint H q f) :
    realEval f (leftEndpoint H q f) = 0 := by
  have hcl := leftEndpoint_mem_closure hq
  have hnonneg := nonneg_on_closure_component H q f hcl
  apply le_antisymm _ hnonneg
  by_contra hp
  have hw : leftEndpoint H q f ∈ positiveWindow H f :=
    ⟨⟨hl,(endpoint_bounds hq).2.1.trans hq.1.2⟩,lt_of_not_ge hp⟩
  have hc := closure_component_inter_window_subset H q f ⟨hcl,hw⟩
  exact (lt_irrefl _ : ¬leftEndpoint H q f < leftEndpoint H q f) (leftEndpoint_lt_of_mem hc)

theorem rightEndpoint_zero_of_lt {H q : ℝ} {f : Path}
    (hq : q ∈ positiveWindow H f) (hr : rightEndpoint H q f < H) :
    realEval f (rightEndpoint H q f) = 0 := by
  have hcl := rightEndpoint_mem_closure hq
  have hnonneg := nonneg_on_closure_component H q f hcl
  apply le_antisymm _ hnonneg
  by_contra hp
  have hw : rightEndpoint H q f ∈ positiveWindow H f :=
    ⟨⟨hq.1.1.trans (endpoint_bounds hq).2.2.1,hr⟩,lt_of_not_ge hp⟩
  have hc := closure_component_inter_window_subset H q f ⟨hcl,hw⟩
  exact (lt_irrefl _ : ¬rightEndpoint H q f < rightEndpoint H q f) (lt_rightEndpoint_of_mem hc)

theorem leftEndpoint_lt_iff (H q a : ℝ) (f : Path) :
    leftEndpoint H q f < a ↔
      (q ∉ positiveWindow H f ∧ 0 < a) ∨
        ∃ r : ℚ, (r : ℝ) ∈ component H f q ∧ (r : ℝ) < a := by
  by_cases hq : q ∈ positiveWindow H f
  · simp only [leftEndpoint,hq,ite_true,not_true_eq_false,false_and,false_or]
    constructor
    · intro h
      obtain ⟨t,ht,hta⟩ := (csInf_lt_iff (component_bddBelow H q f)
        ((component_nonempty_iff H f q).mpr hq)).mp h
      exact exists_rat_in_open ((isOpen_component H f q).inter isOpen_Iio) ⟨t,ht,hta⟩
    · rintro ⟨r,hr,hra⟩
      exact (csInf_le (component_bddBelow H q f) hr).trans_lt hra
  · have he : component H f q = ∅ := connectedComponentIn_eq_empty hq
    simp only [leftEndpoint,hq,ite_false,not_false_eq_true,true_and,he,mem_empty_iff_false,
      false_and,exists_const,or_false]

theorem lt_rightEndpoint_iff (H q a : ℝ) (f : Path) :
    a < rightEndpoint H q f ↔
      (q ∉ positiveWindow H f ∧ a < 0) ∨
        ∃ r : ℚ, (r : ℝ) ∈ component H f q ∧ a < (r : ℝ) := by
  by_cases hq : q ∈ positiveWindow H f
  · simp only [rightEndpoint,hq,ite_true,not_true_eq_false,false_and,false_or]
    constructor
    · intro h
      obtain ⟨t,ht,hat⟩ := (lt_csSup_iff (component_bddAbove H q f)
        ((component_nonempty_iff H f q).mpr hq)).mp h
      exact exists_rat_in_open ((isOpen_component H f q).inter isOpen_Ioi) ⟨t,ht,hat⟩
    · rintro ⟨r,hr,har⟩
      exact har.trans_le (le_csSup (component_bddAbove H q f) hr)
  · have he : component H f q = ∅ := connectedComponentIn_eq_empty hq
    simp only [rightEndpoint,hq,ite_false,not_false_eq_true,true_and,he,mem_empty_iff_false,
      false_and,exists_const,or_false]

theorem measurable_leftEndpoint (H q : ℝ) : Measurable (leftEndpoint H q) := by
  apply measurable_of_Iio
  intro a
  have hactive : MeasurableSet {f : Path | q ∈ positiveWindow H f} := by
    convert measurableSet_componentMembership H q q using 1
    ext f
    exact ⟨mem_component_self,fun h ↦ component_subset H f q h⟩
  have hn : MeasurableSet {f : Path | q ∉ positiveWindow H f ∧ 0 < a} :=
    hactive.compl.inter (measurableSet_const_pred _)
  have he : MeasurableSet (⋃ r : ℚ, {f : Path | (r : ℝ) ∈ component H f q ∧ (r : ℝ) < a}) := by
    apply MeasurableSet.iUnion
    intro r
    exact (measurableSet_componentMembership H q (r : ℝ)).inter (measurableSet_const_pred _)
  convert hn.union he using 1
  ext f
  simp only [mem_preimage,mem_Iio,leftEndpoint_lt_iff,mem_union,mem_ofPred_eq,mem_iUnion]

theorem measurable_rightEndpoint (H q : ℝ) : Measurable (rightEndpoint H q) := by
  apply measurable_of_Ioi
  intro a
  have hactive : MeasurableSet {f : Path | q ∈ positiveWindow H f} := by
    convert measurableSet_componentMembership H q q using 1
    ext f
    exact ⟨mem_component_self,fun h ↦ component_subset H f q h⟩
  have hn : MeasurableSet {f : Path | q ∉ positiveWindow H f ∧ a < 0} :=
    hactive.compl.inter (measurableSet_const_pred _)
  have he : MeasurableSet (⋃ r : ℚ, {f : Path | (r : ℝ) ∈ component H f q ∧ a < (r : ℝ)}) := by
    apply MeasurableSet.iUnion
    intro r
    exact (measurableSet_componentMembership H q (r : ℝ)).inter (measurableSet_const_pred _)
  convert hn.union he using 1
  ext f
  simp only [mem_preimage,mem_Ioi,lt_rightEndpoint_iff,mem_union,mem_ofPred_eq,mem_iUnion]

theorem measurable_length (H q : ℝ) : Measurable (length H q) :=
  (measurable_rightEndpoint H q).sub (measurable_leftEndpoint H q)

theorem endpoints_eq_of_component_eq {H q r : ℝ} {f : Path}
    (hq : q ∈ positiveWindow H f) (hr : r ∈ positiveWindow H f)
    (he : component H f q = component H f r) :
    leftEndpoint H q f = leftEndpoint H r f ∧ rightEndpoint H q f = rightEndpoint H r f := by
  simp only [leftEndpoint,rightEndpoint,if_pos hq,if_pos hr,he,and_self]

end PerronWright.BrownianWindowExcursionEndpoints
