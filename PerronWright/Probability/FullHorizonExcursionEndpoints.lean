import PerronWright.Probability.FullHorizonExcursionSection

/-!
# Measurable full-horizon endpoints

Boundedness of the genuine component is itself a measurable event,
proved using countably many rational membership tests. Thus its actual
infimum and supremum are measurable on path space. The real supremum has
the standard value zero for an unbounded component; reflections of paths
tending to minus infinity never use this exceptional branch.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.FullHorizonExcursionEndpoints

open BrownianPathLaw FullHorizonExcursionComponents FullHorizonExcursionSection

private theorem measurableSet_const_pred (p : Prop) : MeasurableSet {_f : Path | p} := by
  by_cases hp : p <;> simp [hp]

theorem component_bddAbove_iff (f : Path) (q : ℝ) :
    BddAbove (component f q) ↔ ∃ n : ℕ, ∀ r : ℚ,
      (r : ℝ) ∈ component f q → (r : ℝ) < n := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨n,hn⟩ := exists_nat_gt z
    exact ⟨n,fun r hr ↦ (hz hr).trans_lt hn⟩
  · rintro ⟨n,hn⟩
    refine ⟨(n : ℝ),?_⟩
    intro t ht
    by_contra h
    have hnt : (n : ℝ) < t := lt_of_not_ge h
    obtain ⟨r,hr,hnr⟩ := BrownianWindowExcursions.exists_rat_in_open
      ((isOpen_component f q).inter isOpen_Ioi) ⟨t,ht,hnt⟩
    exact (not_lt_of_ge (hn r hr).le) hnr

theorem measurableSet_component_bddAbove (q : ℝ) :
    MeasurableSet {f : Path | BddAbove (component f q)} := by
  have hm : MeasurableSet (⋃ n : ℕ, ⋂ r : ℚ,
      {f : Path | (r : ℝ) ∈ component f q → (r : ℝ) < n}) := by
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.iInter
    intro r
    by_cases hrn : (r : ℝ) < n
    · simp only [hrn,implies_true,ofPred_true]
      exact MeasurableSet.univ
    · simp only [hrn,imp_false]
      exact (measurableSet_componentMembership q (r : ℝ)).compl
  convert hm using 1
  ext f
  simp only [mem_ofPred_eq,mem_iUnion,mem_iInter,component_bddAbove_iff]

theorem leftEndpoint_lt_iff (q a : ℝ) (f : Path) :
    leftEndpoint q f < a ↔
      (q ∉ positiveSet f ∧ 0 < a) ∨
        ∃ r : ℚ, (r : ℝ) ∈ component f q ∧ (r : ℝ) < a := by
  by_cases hq : q ∈ positiveSet f
  · simp only [leftEndpoint,hq,ite_true,not_true_eq_false,false_and,false_or]
    constructor
    · intro h
      obtain ⟨t,ht,hta⟩ := (csInf_lt_iff (component_bddBelow f q)
        ((component_nonempty_iff f q).mpr hq)).mp h
      exact BrownianWindowExcursions.exists_rat_in_open
        ((isOpen_component f q).inter isOpen_Iio) ⟨t,ht,hta⟩
    · rintro ⟨r,hr,hra⟩
      exact (csInf_le (component_bddBelow f q) hr).trans_lt hra
  · have he : component f q = ∅ := connectedComponentIn_eq_empty hq
    simp only [leftEndpoint,hq,ite_false,not_false_eq_true,true_and,he,mem_empty_iff_false,
      false_and,exists_const,or_false]

theorem lt_rightEndpoint_iff (q a : ℝ) (f : Path) :
    a < rightEndpoint q f ↔
      ((q ∉ positiveSet f ∨ ¬ BddAbove (component f q)) ∧ a < 0) ∨
        (BddAbove (component f q) ∧
          ∃ r : ℚ, (r : ℝ) ∈ component f q ∧ a < (r : ℝ)) := by
  by_cases hq : q ∈ positiveSet f
  · by_cases hb : BddAbove (component f q)
    · simp only [rightEndpoint,hq,ite_true,not_true_eq_false,hb,false_or,
        false_and,false_or,true_and]
      constructor
      · intro h
        obtain ⟨t,ht,hat⟩ := (lt_csSup_iff hb ((component_nonempty_iff f q).mpr hq)).mp h
        exact BrownianWindowExcursions.exists_rat_in_open
          ((isOpen_component f q).inter isOpen_Ioi) ⟨t,ht,hat⟩
      · rintro ⟨r,hr,har⟩
        exact har.trans_le (le_csSup hb hr)
    · simp only [rightEndpoint,hq,ite_true,Real.sSup_of_not_bddAbove hb,hb,
        not_false_eq_true,not_true_eq_false,false_or,true_and,false_and,or_false]
  · have he : component f q = ∅ := connectedComponentIn_eq_empty hq
    simp only [rightEndpoint,hq,ite_false,not_false_eq_true,true_or,true_and,
      he,mem_empty_iff_false,false_and,exists_const,and_false,or_false]

theorem measurable_leftEndpoint (q : ℝ) : Measurable (leftEndpoint q) := by
  apply measurable_of_Iio
  intro a
  have hn : MeasurableSet {f : Path | q ∉ positiveSet f ∧ 0 < a} :=
    (measurableSet_active q).compl.inter (measurableSet_const_pred _)
  have he : MeasurableSet (⋃ r : ℚ, {f : Path | (r : ℝ) ∈ component f q ∧ (r : ℝ) < a}) := by
    apply MeasurableSet.iUnion
    intro r
    exact (measurableSet_componentMembership q (r : ℝ)).inter (measurableSet_const_pred _)
  convert hn.union he using 1
  ext f
  simp only [mem_preimage,mem_Iio,leftEndpoint_lt_iff,mem_union,mem_ofPred_eq,mem_iUnion]

theorem measurable_rightEndpoint (q : ℝ) : Measurable (rightEndpoint q) := by
  apply measurable_of_Ioi
  intro a
  have hn : MeasurableSet {f : Path |
      (q ∉ positiveSet f ∨ ¬ BddAbove (component f q)) ∧ a < 0} :=
    ((measurableSet_active q).compl.union (measurableSet_component_bddAbove q).compl).inter
      (measurableSet_const_pred _)
  have he : MeasurableSet (⋃ r : ℚ, {f : Path | (r : ℝ) ∈ component f q ∧ a < (r : ℝ)}) := by
    apply MeasurableSet.iUnion
    intro r
    exact (measurableSet_componentMembership q (r : ℝ)).inter (measurableSet_const_pred _)
  convert hn.union ((measurableSet_component_bddAbove q).inter he) using 1
  ext f
  simp only [mem_preimage,mem_Ioi,lt_rightEndpoint_iff,mem_union,mem_inter_iff,
    mem_ofPred_eq,mem_iUnion]

theorem measurable_length (q : ℝ) : Measurable (length q) :=
  (measurable_rightEndpoint q).sub (measurable_leftEndpoint q)

theorem leftEndpoint_nonneg (q : ℝ) (f : Path) : 0 ≤ leftEndpoint q f := by
  by_cases hq : q ∈ positiveSet f
  · simp only [leftEndpoint,if_pos hq]
    exact le_csInf ((component_nonempty_iff f q).mpr hq)
      (fun t ht ↦ (component_subset f q ht).1.le)
  · simp only [leftEndpoint,if_neg hq,le_refl]

theorem rightEndpoint_nonneg (q : ℝ) (f : Path) : 0 ≤ rightEndpoint q f := by
  by_cases hq : q ∈ positiveSet f
  · by_cases hb : BddAbove (component f q)
    · exact hq.1.le.trans (endpoint_bounds hq hb).2.2.le
    · simp only [rightEndpoint,if_pos hq,Real.sSup_of_not_bddAbove hb,le_refl]
  · simp only [rightEndpoint,if_neg hq,le_refl]

end PerronWright.FullHorizonExcursionEndpoints
