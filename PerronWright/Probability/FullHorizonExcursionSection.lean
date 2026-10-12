import PerronWright.Probability.FullHorizonExcursionComponents

/-!
# A genuine measurable rational section of full-horizon excursions

The least rational code in each actual connected positivity component
gives a countable nonrepeating section. Fixed membership events are
proved open by strict positivity on the compact interval between anchors.
This construction does not require a finite time horizon or boundedness.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.FullHorizonExcursionSection

open BrownianPathLaw
open FullHorizonExcursionComponents

theorem component_eq_ordConnectedComponent (f : Path) (q : ℝ) :
    component f q = ordConnectedComponent (positiveSet f) q := by
  ext r
  constructor
  · intro hr
    have hq := (component_nonempty_iff f q).mp ⟨r,hr⟩
    exact ((component_ordConnected f q).uIcc_subset (mem_component_self hq) hr).trans
      (component_subset f q)
  · intro hr
    exact isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hr right_mem_uIcc

theorem mem_component_iff (f : Path) (q r : ℝ) :
    r ∈ component f q ↔ 0 < q ∧ 0 < r ∧
      0 < BrownianWindowExcursions.intervalMinimum f q r := by
  rw [component_eq_ordConnectedComponent,mem_ordConnectedComponent]
  constructor
  · intro h
    refine ⟨(h left_mem_uIcc).1,(h right_mem_uIcc).1,?_⟩
    exact (BrownianWindowExcursions.intervalMinimum_pos_iff f q r).mpr
      (fun t ht ↦ (h ht).2)
  · rintro ⟨hq,hr,hmin⟩ t ht
    exact ⟨ordConnected_Ioi.uIcc_subset hq hr ht,
      (BrownianWindowExcursions.intervalMinimum_pos_iff f q r).mp hmin t ht⟩

theorem isOpen_componentMembership (q r : ℝ) :
    IsOpen {f : Path | r ∈ component f q} := by
  by_cases hq : 0 < q
  · by_cases hr : 0 < r
    · convert isOpen_lt (continuous_const : Continuous (fun _ : Path ↦ (0 : ℝ)))
        (BrownianWindowExcursions.continuous_intervalMinimum q r) using 1
      ext f
      simp only [mem_ofPred_eq,mem_component_iff,hq,hr,true_and]
    · have he : {f : Path | r ∈ component f q} = ∅ := by
        ext f
        simp only [mem_ofPred_eq,mem_component_iff,hr,false_and,and_false,mem_empty_iff_false]
      rw [he]
      exact isOpen_empty
  · have he : {f : Path | r ∈ component f q} = ∅ := by
      ext f
      simp only [mem_ofPred_eq,mem_component_iff,hq,false_and,mem_empty_iff_false]
    rw [he]
    exact isOpen_empty

theorem measurableSet_componentMembership (q r : ℝ) :
    MeasurableSet {f : Path | r ∈ component f q} := (isOpen_componentMembership q r).measurableSet

theorem measurableSet_active (q : ℝ) : MeasurableSet {f : Path | q ∈ positiveSet f} := by
  convert measurableSet_componentMembership q q using 1
  ext f
  exact ⟨mem_component_self,fun h ↦ component_subset f q h⟩

def Representative (f : Path) (q : ℚ) : Prop :=
  (q : ℝ) ∈ positiveSet f ∧ ∀ r : ℚ, (r : ℝ) ∈ component f (q : ℝ) →
    Encodable.encode q ≤ Encodable.encode r

theorem exists_representative {x : ℝ} {f : Path} (hx : x ∈ positiveSet f) :
    ∃ q : ℚ, Representative f q ∧ component f (q : ℝ) = component f x := by
  obtain ⟨r,hr⟩ := BrownianWindowExcursions.exists_rat_in_open (isOpen_component f x)
    ((component_nonempty_iff f x).mpr hx)
  have hn : ∃ n : ℕ, ∃ q : ℚ, Encodable.encode q = n ∧ (q : ℝ) ∈ component f x :=
    ⟨Encodable.encode r,r,rfl,hr⟩
  obtain ⟨q,hcode,hq⟩ := Nat.find_spec hn
  have he := component_eq_of_mem hq
  refine ⟨q,⟨component_subset f x hq,?_⟩,he.symm⟩
  intro r hr
  rw [hcode]
  exact Nat.find_min' hn ⟨r,rfl,by rw [he]; exact hr⟩

theorem representatives_eq_of_component_eq {f : Path} {q r : ℚ}
    (hq : Representative f q) (hr : Representative f r)
    (he : component f (q : ℝ) = component f (r : ℝ)) : q = r := by
  apply Encodable.encode_injective
  apply le_antisymm
  · exact hq.2 r (he.symm ▸ mem_component_self hr.1)
  · exact hr.2 q (he ▸ mem_component_self hq.1)

theorem components_disjoint_of_ne {q r : ℝ} {f : Path}
    (he : component f q ≠ component f r) : Disjoint (component f q) (component f r) := by
  apply disjoint_left.mpr
  intro x hx hy
  exact he ((component_eq_of_mem hx).trans (component_eq_of_mem hy).symm)

theorem representative_components_disjoint {f : Path} {q r : ℚ}
    (hq : Representative f q) (hr : Representative f r) (hqr : q ≠ r) :
    Disjoint (component f (q : ℝ)) (component f (r : ℝ)) :=
  components_disjoint_of_ne (fun he ↦ hqr (representatives_eq_of_component_eq hq hr he))

theorem positiveSet_eq_union_representatives (f : Path) :
    positiveSet f = ⋃ q : ℚ, ⋃ (_ : Representative f q), component f (q : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨q,hq,he⟩ := exists_representative hx
    exact mem_iUnion_of_mem q (mem_iUnion_of_mem hq (he.symm ▸ mem_component_self hx))
  · intro hx
    obtain ⟨q,hinner⟩ := mem_iUnion.mp hx
    obtain ⟨_,hx⟩ := mem_iUnion.mp hinner
    exact component_subset f (q : ℝ) hx

theorem measurableSet_representative (q : ℚ) :
    MeasurableSet {f : Path | Representative f q} := by
  have hall : MeasurableSet (⋂ r : ℚ,
      {f : Path | (r : ℝ) ∈ component f (q : ℝ) → Encodable.encode q ≤ Encodable.encode r}) := by
    apply MeasurableSet.iInter
    intro r
    by_cases hle : Encodable.encode q ≤ Encodable.encode r
    · simp only [hle,implies_true,ofPred_true]
      exact MeasurableSet.univ
    · simp only [hle,imp_false]
      change MeasurableSet ({f : Path | (r : ℝ) ∈ component f (q : ℝ)}ᶜ)
      exact (measurableSet_componentMembership (q : ℝ) (r : ℝ)).compl
  convert (measurableSet_active (q : ℝ)).inter hall using 1
  ext f
  simp only [Representative,mem_ofPred_eq,mem_inter_iff,mem_iInter]

end PerronWright.FullHorizonExcursionSection
