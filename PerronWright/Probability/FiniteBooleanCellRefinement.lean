import PerronWright.Probability.ComponentWindowMixedFactorials
import PerronWright.Probability.SizeCellIndicators

/-! # Literal finite Boolean refinement of possibly overlapping cells

Every queried size set is resolved into disjoint Boolean atoms, and each
surplus value is kept separately. Counts on the original overlapping
cells are actual finite sums of the refined point counts.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators Classical Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteBooleanCellRefinement

open ComponentWindowPointMeasures ComponentWindowMixedFactorials FinitePointMeasureCompact

variable {D : Type*} [Fintype D]

def sizeAtom (J : D → Set ℝ) (p : D → Bool) : Set ℝ :=
  ⋂ i, if p i = true then J i else (J i)ᶜ

def membershipPattern (J : D → Set ℝ) (x : ℝ) : D → Bool := fun i ↦ decide (x ∈ J i)

omit [Fintype D] in
theorem mem_sizeAtom (J : D → Set ℝ) (p : D → Bool) (x : ℝ) :
    x ∈ sizeAtom J p ↔ p = membershipPattern J x := by
  simp only [sizeAtom,Set.mem_iInter]
  constructor
  · intro hx
    funext i
    have hi := hx i
    change p i = decide (x ∈ J i)
    cases h : p i <;> simp [h] at hi ⊢ <;> exact hi
  · intro hp i
    rw [hp]
    change x ∈ if decide (x ∈ J i) = true then J i else (J i)ᶜ
    by_cases h : x ∈ J i <;> simp [h]

theorem measurableSet_sizeAtom (J : D → Set ℝ) (hJ : ∀ i, MeasurableSet (J i))
    (p : D → Bool) : MeasurableSet (sizeAtom J p) := by
  apply MeasurableSet.iInter
  intro i
  split_ifs
  · exact hJ i
  · exact (hJ i).compl

theorem volume_frontier_sizeAtom (J : D → Set ℝ)
    (hJ : ∀ i, (volume : Measure ℝ) (frontier (J i)) = 0) (p : D → Bool) :
    (volume : Measure ℝ) (frontier (sizeAtom J p)) = 0 := by
  let C : D → Set ℝ := fun i ↦ if p i = true then J i else (J i)ᶜ
  have hC (i) : (volume : Measure ℝ) (frontier (C i)) = 0 := by
    dsimp only [C]
    split_ifs
    · exact hJ i
    · simpa only [frontier_compl] using hJ i
  have hf (s : Finset D) : (volume : Measure ℝ) (frontier (⋂ i ∈ s, C i)) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
      have he : (⋂ j ∈ insert i s, C j) = C i ∩ ⋂ j ∈ s, C j := by
        ext x
        simp
      rw [he]
      exact measure_mono_null (frontier_inter_subset _ _) (measure_union_null
        (measure_mono_null Set.inter_subset_left (hC i))
        (measure_mono_null Set.inter_subset_right ih))
  simpa only [Finset.mem_univ,Set.iInter_true,sizeAtom,C] using hf Finset.univ

abbrev AtomIndex (D : Type*) (R : ℕ) := (D → Bool) × Fin (R+1)

def atomSizes (J : D → Set ℝ) (R : ℕ) (k : AtomIndex D R) : Set ℝ := sizeAtom J k.1
def atomSurpluses (D : Type*) (R : ℕ) (k : AtomIndex D R) : Finset ℕ := {k.2.val}

omit [Fintype D] in
theorem atomCells_disjoint (J : D → Set ℝ) (R : ℕ) :
    Pairwise (fun k l : AtomIndex D R ↦
      Disjoint (sizeSurplusCells (atomSizes J R) (atomSurpluses D R) k)
        (sizeSurplusCells (atomSizes J R) (atomSurpluses D R) l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  rintro ⟨x,r⟩ hk hl
  have hk' : x ∈ sizeAtom J k.1 ∧ r = k.2.val := by
    simpa [sizeSurplusCells,atomSizes,atomSurpluses] using hk
  have hl' : x ∈ sizeAtom J l.1 ∧ r = l.2.val := by
    simpa [sizeSurplusCells,atomSizes,atomSurpluses] using hl
  apply hkl
  apply Prod.ext
  · exact (mem_sizeAtom J k.1 x |>.mp hk'.1).trans
      (mem_sizeAtom J l.1 x |>.mp hl'.1).symm
  · exact Fin.ext (hk'.2.symm.trans hl'.2)

def atomLabel (J : D → Set ℝ) (a b : ℝ) (R : ℕ) (z : SurplusWindow a b R) : AtomIndex D R :=
  (membershipPattern J z.1.val,z.2)

omit [Fintype D] in
theorem atomRegion_eq_fiber (J : D → Set ℝ) (a b : ℝ) (R : ℕ) (k : AtomIndex D R) :
    windowEmbedding a b R ⁻¹' sizeSurplusCells (atomSizes J R) (atomSurpluses D R) k =
      {z | atomLabel J a b R z = k} := by
  rcases k with ⟨p,r⟩
  ext z
  simp only [Set.mem_preimage,sizeSurplusCells,Set.mem_prod,atomSizes,atomSurpluses,
    Finset.mem_coe,Finset.mem_singleton,windowEmbedding,mem_sizeAtom,atomLabel,
    Set.mem_ofPred_eq,Prod.mk.injEq,Fin.ext_iff]
  exact and_congr eq_comm Iff.rfl

def selects (S : D → Finset ℕ) (i : D) (k : AtomIndex D R) : Prop :=
  k.1 i = true ∧ k.2.val ∈ S i

def reconstruct (S : D → Finset ℕ) (R : ℕ) (y : AtomIndex D R → ℕ) : D → ℕ :=
  fun i ↦ ∑ k, if selects S i k then y k else 0

omit [Fintype D] in
theorem queryRegion_eq (J : D → Set ℝ) (S : D → Finset ℕ) (a b : ℝ) (R : ℕ) (i : D) :
    windowEmbedding a b R ⁻¹' sizeSurplusCells J S i =
      {z | selects S i (atomLabel J a b R z)} := by
  ext z
  simp [sizeSurplusCells,selects,atomLabel,membershipPattern,windowEmbedding]

theorem count_partition_sum {E K : Type*} [MeasurableSpace E] [Fintype K]
    (η : PointMeasure E) (p : E → K) (hp : ∀ k, MeasurableSet {x | p x = k})
    (V : K → Prop) :
    count η {x | V (p x)} = ∑ k, if V k then count η {x | p x = k} else 0 := by
  let B : K → Set E := fun k ↦ if V k then {x | p x = k} else ∅
  have hB (k) : MeasurableSet (B k) := by
    dsimp only [B]
    split_ifs
    · exact hp k
    · exact MeasurableSet.empty
  have hdis : Pairwise (fun k l ↦ Disjoint (B k) (B l)) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro x hk hl
    dsimp only [B] at hk hl
    split_ifs at hk hl with hVk hVl <;> simp_all
  have he : (⋃ k, B k) = {x | V (p x)} := by
    ext x
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k,hk⟩
      dsimp only [B] at hk
      split_ifs at hk with hVk
      · exact hk ▸ hVk
      · exact False.elim hk
    · intro hx
      exact ⟨p x,by simp [B,hx]⟩
  have hm : MeasurableSet {x | V (p x)} := he ▸ MeasurableSet.iUnion hB
  have hh := measureReal_iUnion_fintype (μ := ((η : FiniteMeasure E) : Measure E)) hdis hB
  rw [he,measure_real_eq_count η hm] at hh
  have ht (k) : ((η : FiniteMeasure E) : Measure E).real (B k) =
      (if V k then count η {x | p x = k} else 0 : ℕ) := by
    dsimp only [B]
    split_ifs
    · exact measure_real_eq_count η (hp k)
    · simp
  simp_rw [ht] at hh
  exact_mod_cast hh

theorem countVector_eq_reconstruct (J : D → Set ℝ) (S : D → Finset ℕ)
    (hJ : ∀ i, MeasurableSet (J i)) (a b : ℝ) (R : ℕ)
    (η : PointMeasure (SurplusWindow a b R)) :
    (fun i ↦ count η (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)) =
      reconstruct S R (fun k ↦ count η
        (windowEmbedding a b R ⁻¹' sizeSurplusCells (atomSizes J R) (atomSurpluses D R) k)) := by
  funext i
  rw [queryRegion_eq]
  have hp (k : AtomIndex D R) : MeasurableSet {z | atomLabel J a b R z = k} := by
    rw [← atomRegion_eq_fiber]
    exact (measurable_windowEmbedding a b R)
      (measurableSet_sizeSurplusCells (atomSizes J R) (atomSurpluses D R)
        (fun k ↦ measurableSet_sizeAtom J hJ k.1) k)
  rw [count_partition_sum η _ hp]
  simp only [reconstruct,atomRegion_eq_fiber]

end PerronWright.FiniteBooleanCellRefinement
