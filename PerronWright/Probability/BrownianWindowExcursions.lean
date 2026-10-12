import PerronWright.Probability.BrownianPathReflectionLaw
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Rat

/-!
# Genuine bounded-window excursions and a measurable rational section

These are the actual connected components of the strict positivity set
inside `(0,H)`. They are clipped excursions, not assertions that a full
unbounded-time excursion has both endpoints inside the window. Compact
interval positivity proves that fixed component-membership events are
open in the actual continuous-path space. Least rational codes then give
a countable, nonrepeating, measurable section of all components.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianWindowExcursions

open BrownianPathLaw BrownianPathReflectionLaw

def realEval (f : Path) (t : ℝ) : ℝ := f (Real.toNNReal t)

theorem continuous_realEval (f : Path) : Continuous (realEval f) :=
  (continuous_path f).comp continuous_real_toNNReal

theorem continuous_joint_realEval : Continuous (fun p : Path × ℝ ↦ realEval p.1 p.2) :=
  (continuous_fst : Continuous (fun p : Path × ℝ ↦ p.1)).eval
    (continuous_real_toNNReal.comp continuous_snd)

def positiveWindow (H : ℝ) (f : Path) : Set ℝ := Ioo 0 H ∩ {t | 0 < realEval f t}

def component (H : ℝ) (f : Path) (q : ℝ) : Set ℝ :=
  connectedComponentIn (positiveWindow H f) q

theorem isOpen_positiveWindow (H : ℝ) (f : Path) : IsOpen (positiveWindow H f) :=
  isOpen_Ioo.inter (isOpen_lt continuous_const (continuous_realEval f))

theorem isOpen_component (H : ℝ) (f : Path) (q : ℝ) : IsOpen (component H f q) :=
  (isOpen_positiveWindow H f).connectedComponentIn

theorem component_subset (H : ℝ) (f : Path) (q : ℝ) : component H f q ⊆ positiveWindow H f :=
  connectedComponentIn_subset _ _

theorem mem_component_self {H q : ℝ} {f : Path} (hq : q ∈ positiveWindow H f) :
    q ∈ component H f q := mem_connectedComponentIn hq

theorem component_nonempty_iff (H : ℝ) (f : Path) (q : ℝ) :
    (component H f q).Nonempty ↔ q ∈ positiveWindow H f :=
  connectedComponentIn_nonempty_iff

theorem component_ordConnected (H : ℝ) (f : Path) (q : ℝ) : (component H f q).OrdConnected :=
  isPreconnected_connectedComponentIn.ordConnected

theorem component_isConnected {H q : ℝ} {f : Path} (hq : q ∈ positiveWindow H f) :
    IsConnected (component H f q) := isConnected_connectedComponentIn_iff.mpr hq

theorem component_eq_of_mem {H q r : ℝ} {f : Path} (hr : r ∈ component H f q) :
    component H f q = component H f r := connectedComponentIn_eq hr

theorem component_eq_ordConnectedComponent (H : ℝ) (f : Path) (q : ℝ) :
    component H f q = ordConnectedComponent (positiveWindow H f) q := by
  ext r
  constructor
  · intro hr
    have hq := component_nonempty_iff H f q |>.mp ⟨r,hr⟩
    exact ((component_ordConnected H f q).uIcc_subset (mem_component_self hq) hr).trans
      (component_subset H f q)
  · intro hr
    exact isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hr right_mem_uIcc

def intervalMinimum (f : Path) (q r : ℝ) : ℝ := sInf (realEval f '' uIcc q r)

theorem continuous_intervalMinimum (q r : ℝ) : Continuous (fun f : Path ↦ intervalMinimum f q r) :=
  (isCompact_uIcc : IsCompact (uIcc q r)).continuous_sInf continuous_joint_realEval

theorem intervalMinimum_pos_iff (f : Path) (q r : ℝ) :
    0 < intervalMinimum f q r ↔ ∀ t ∈ uIcc q r, 0 < realEval f t := by
  constructor
  · intro h t ht
    exact h.trans_le (csInf_le
      (isCompact_uIcc.bddBelow_image (continuous_realEval f).continuousOn)
      (mem_image_of_mem (realEval f) ht))
  · intro h
    obtain ⟨t,ht,he⟩ := (isCompact_uIcc : IsCompact (uIcc q r)).exists_sInf_image_eq_and_le
      nonempty_uIcc (continuous_realEval f).continuousOn
    change 0 < sInf (realEval f '' uIcc q r)
    rw [he.1]
    exact h t ht

theorem mem_component_iff (H : ℝ) (f : Path) (q r : ℝ) :
    r ∈ component H f q ↔ q ∈ Ioo 0 H ∧ r ∈ Ioo 0 H ∧ 0 < intervalMinimum f q r := by
  rw [component_eq_ordConnectedComponent,mem_ordConnectedComponent]
  constructor
  · intro h
    refine ⟨(h left_mem_uIcc).1,(h right_mem_uIcc).1,?_⟩
    exact (intervalMinimum_pos_iff f q r).mpr (fun t ht ↦ (h ht).2)
  · rintro ⟨hq,hr,hmin⟩ t ht
    exact ⟨ordConnected_Ioo.uIcc_subset hq hr ht,(intervalMinimum_pos_iff f q r).mp hmin t ht⟩

/-- Fixed-time membership in the literal component is an open path-space event. -/
theorem isOpen_componentMembership (H q r : ℝ) : IsOpen {f : Path | r ∈ component H f q} := by
  by_cases hq : q ∈ Ioo 0 H
  · by_cases hr : r ∈ Ioo 0 H
    · convert isOpen_lt (continuous_const : Continuous (fun _ : Path ↦ (0 : ℝ)))
        (continuous_intervalMinimum q r) using 1
      ext f
      simp only [mem_ofPred_eq,mem_component_iff,hq,hr,true_and]
    · have he : {f : Path | r ∈ component H f q} = ∅ := by
        ext f
        simp only [mem_ofPred_eq,mem_component_iff,hr,false_and,and_false,mem_empty_iff_false]
      rw [he]
      exact isOpen_empty
  · have he : {f : Path | r ∈ component H f q} = ∅ := by
      ext f
      simp only [mem_ofPred_eq,mem_component_iff,hq,false_and,mem_empty_iff_false]
    rw [he]
    exact isOpen_empty

theorem measurableSet_componentMembership (H q r : ℝ) :
    MeasurableSet {f : Path | r ∈ component H f q} := (isOpen_componentMembership H q r).measurableSet

theorem exists_rat_in_open {s : Set ℝ} (hs : IsOpen s) (hn : s.Nonempty) :
    ∃ q : ℚ, (q : ℝ) ∈ s := by
  obtain ⟨a,b,hab,hsub⟩ := hs.exists_Ioo_subset hn
  obtain ⟨q,haq,hqb⟩ := exists_rat_btwn hab
  exact ⟨q,hsub ⟨haq,hqb⟩⟩

/-- The minimum rational code in each component. This is a predicate
on an explicit rational anchor, not an assumed excursion enumeration. -/
def Representative (H : ℝ) (f : Path) (q : ℚ) : Prop :=
  (q : ℝ) ∈ positiveWindow H f ∧
    ∀ r : ℚ, (r : ℝ) ∈ component H f (q : ℝ) → Encodable.encode q ≤ Encodable.encode r

theorem exists_representative {H x : ℝ} {f : Path} (hx : x ∈ positiveWindow H f) :
    ∃ q : ℚ, Representative H f q ∧ component H f (q : ℝ) = component H f x := by
  obtain ⟨r,hr⟩ := exists_rat_in_open (isOpen_component H f x)
    ((component_nonempty_iff H f x).mpr hx)
  have hn : ∃ n : ℕ, ∃ q : ℚ, Encodable.encode q = n ∧ (q : ℝ) ∈ component H f x :=
    ⟨Encodable.encode r,r,rfl,hr⟩
  obtain ⟨q,hcode,hq⟩ := Nat.find_spec hn
  have he := component_eq_of_mem hq
  refine ⟨q,⟨component_subset H f x hq,?_⟩,he.symm⟩
  intro r hr
  rw [hcode]
  exact Nat.find_min' hn ⟨r,rfl,by rw [he]; exact hr⟩

theorem representatives_eq_of_component_eq {H : ℝ} {f : Path} {q r : ℚ}
    (hq : Representative H f q) (hr : Representative H f r)
    (he : component H f (q : ℝ) = component H f (r : ℝ)) : q = r := by
  apply Encodable.encode_injective
  apply le_antisymm
  · exact hq.2 r (he.symm ▸ mem_component_self hr.1)
  · exact hr.2 q (he ▸ mem_component_self hq.1)

theorem components_disjoint_of_ne {H q r : ℝ} {f : Path}
    (he : component H f q ≠ component H f r) : Disjoint (component H f q) (component H f r) := by
  apply disjoint_left.mpr
  intro x hx hy
  exact he ((component_eq_of_mem hx).trans (component_eq_of_mem hy).symm)

theorem representative_components_disjoint {H : ℝ} {f : Path} {q r : ℚ}
    (hq : Representative H f q) (hr : Representative H f r) (hqr : q ≠ r) :
    Disjoint (component H f (q : ℝ)) (component H f (r : ℝ)) :=
  components_disjoint_of_ne (fun he ↦ hqr (representatives_eq_of_component_eq hq hr he))

theorem positiveWindow_eq_union_representatives (H : ℝ) (f : Path) :
    positiveWindow H f = ⋃ q : ℚ, ⋃ (_ : Representative H f q), component H f (q : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨q,hq,he⟩ := exists_representative hx
    exact mem_iUnion_of_mem q (mem_iUnion_of_mem hq (he.symm ▸ mem_component_self hx))
  · intro hx
    obtain ⟨q,hinner⟩ := mem_iUnion.mp hx
    obtain ⟨_,hx⟩ := mem_iUnion.mp hinner
    exact component_subset H f (q : ℝ) hx

theorem measurableSet_representative (H : ℝ) (q : ℚ) : MeasurableSet {f : Path | Representative H f q} := by
  have hactive : MeasurableSet {f : Path | (q : ℝ) ∈ positiveWindow H f} := by
    convert measurableSet_componentMembership H (q : ℝ) (q : ℝ) using 1
    ext f
    exact ⟨mem_component_self,fun h ↦ component_subset H f (q : ℝ) h⟩
  have hall : MeasurableSet (⋂ r : ℚ,
      {f : Path | (r : ℝ) ∈ component H f (q : ℝ) → Encodable.encode q ≤ Encodable.encode r}) := by
    apply MeasurableSet.iInter
    intro r
    by_cases hle : Encodable.encode q ≤ Encodable.encode r
    · simp only [hle,implies_true,ofPred_true]
      exact MeasurableSet.univ
    · simp only [hle,imp_false]
      change MeasurableSet ({f : Path | (r : ℝ) ∈ component H f (q : ℝ)}ᶜ)
      exact (measurableSet_componentMembership H (q : ℝ) (r : ℝ)).compl
  convert hactive.inter hall using 1
  ext f
  simp only [Representative,mem_ofPred_eq,mem_inter_iff,mem_iInter]

end PerronWright.BrownianWindowExcursions
