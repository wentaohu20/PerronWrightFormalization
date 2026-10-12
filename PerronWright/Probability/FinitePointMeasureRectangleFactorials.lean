import PerronWright.Probability.FinitePointMeasureMixedFactorials
import PerronWright.Probability.FinitePointMeasureMeasurable

/-!
# Intrinsic rectangle factorials, including overlapping cells

The membership-pattern partition is finite and genuinely measurable.
It turns every ordered distinct labelled-atom tuple in arbitrary cells
into cell-wise embeddings. The resulting count polynomial depends only
on the point measure, not on a chosen atom representation.
-/

open MeasureTheory Set
open scoped Classical BigOperators

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FinitePointMeasureRectangleFactorials

open FinitePointMeasureCompact FinitePointMeasureFintype

variable {E I J D : Type*} [Fintype I] [Fintype J] [Fintype D]

def labelledCellTupleEquiv (x : I → E) (C : D → Set E) (l : J → D)
    (hC : Pairwise (fun i j ↦ Disjoint (C i) (C j))) :
    {e : J ↪ I // ∀ j, x (e j) ∈ C (l j)} ≃
      (∀ d : D, {j : J // l j = d} ↪ {i : I // x i ∈ C d}) where
  toFun e d := ⟨fun j ↦ ⟨e.val j.1, by simpa only [← j.2] using e.2 j.1⟩, by
    intro j k h
    exact Subtype.ext (e.val.injective (congrArg Subtype.val h))⟩
  invFun f := ⟨⟨fun j ↦ (f (l j) ⟨j,rfl⟩).1, by
    intro j k h
    change (f (l j) ⟨j,rfl⟩).1 = (f (l k) ⟨k,rfl⟩).1 at h
    have hl : l j = l k := by
      by_contra hn
      exact Set.disjoint_left.mp (hC hn) (f (l j) ⟨j,rfl⟩).2
        (by rw [h]; exact (f (l k) ⟨k,rfl⟩).2)
    have h' : (f (l j) ⟨j,rfl⟩).1 = (f (l j) ⟨k,hl.symm⟩).1 := by
      have hf : (f (l k) ⟨k,rfl⟩).1 = (f (l j) ⟨k,hl.symm⟩).1 := by
        have hgen : ∀ (d : D) (hd : l k = d),
            (f (l k) ⟨k,rfl⟩).1 = (f d ⟨k,hd⟩).1 := by
          intro d hd
          subst d
          rfl
        exact hgen (l j) hl.symm
      exact h.trans hf
    exact congrArg Subtype.val ((f (l j)).injective (Subtype.ext h'))⟩,
    fun j ↦ (f (l j) ⟨j,rfl⟩).2⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro j
    rfl
  right_inv f := by
    funext d
    apply Function.Embedding.ext
    rintro ⟨j,hj⟩
    cases hj
    rfl

theorem labelledCellTuple_card (x : I → E) (C : D → Set E) (l : J → D)
    (hC : Pairwise (fun i j ↦ Disjoint (C i) (C j))) :
    Fintype.card {e : J ↪ I // ∀ j, x (e j) ∈ C (l j)} =
      ∏ d : D, (Fintype.card {i : I // x i ∈ C d}).descFactorial
        (Fintype.card {j : J // l j = d}) := by
  rw [Fintype.card_congr (labelledCellTupleEquiv x C l hC), Fintype.card_pi]
  simp only [Fintype.card_embedding_eq]

def pattern (A : J → Set E) (x : E) : Set J := {j | x ∈ A j}

def patternCell (A : J → Set E) (s : Set J) : Set E := {x | pattern A x = s}

omit [Fintype J] in
theorem patternCell_pairwise_disjoint (A : J → Set E) :
    Pairwise (fun s t : Set J ↦ Disjoint (patternCell A s) (patternCell A t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hst (hx.symm.trans hy)

def partitionTupleEquiv (x : I → E) (A : J → Set E) :
    {e : J ↪ I // ∀ j, x (e j) ∈ A j} ≃
      Σ l : J → Set J, {e : J ↪ I //
        (∀ j, x (e j) ∈ patternCell A (l j)) ∧ (∀ j, j ∈ l j)} where
  toFun e := ⟨fun j ↦ pattern A (x (e.val j)), e.val,
    fun _ ↦ rfl, fun j ↦ e.2 j⟩
  invFun e := ⟨e.2.val, fun j ↦ by
    have h := e.2.2.1 j
    change pattern A (x (e.2.val j)) = e.1 j at h
    change j ∈ pattern A (x (e.2.val j))
    rw [h]
    exact e.2.2.2 j⟩
  left_inv e := rfl
  right_inv e := by
    rcases e with ⟨l,e,he,hj⟩
    have hl : (fun j ↦ pattern A (x (e j))) = l := by
      funext j
      exact he j
    dsimp
    cases hl
    rfl

theorem rectangleTuple_card (x : I → E) (A : J → Set E) :
    Fintype.card {e : J ↪ I // ∀ j, x (e j) ∈ A j} =
      ∑ l : J → Set J, if ∀ j, j ∈ l j then
        ∏ s : Set J, (Fintype.card {i : I // x i ∈ patternCell A s}).descFactorial
          (Fintype.card {j : J // l j = s}) else 0 := by
  rw [Fintype.card_congr (partitionTupleEquiv x A),Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : ∀ j, j ∈ l j
  · simpa [h] using labelledCellTuple_card x (patternCell A) l (patternCell_pairwise_disjoint A)
  · simp [h]

variable [MeasurableSpace E]

omit [Fintype J] in
theorem measurable_pattern (A : J → Set E) (hA : ∀ j, MeasurableSet (A j)) :
    Measurable (pattern A) := by
  apply measurable_set_iff.mpr
  intro j
  exact measurableSet_setOfPred.mp (hA j)

theorem measurableSet_patternCell (A : J → Set E) (hA : ∀ j, MeasurableSet (A j))
    (s : Set J) : MeasurableSet (patternCell A s) :=
  (measurable_pattern A hA) (measurableSet_singleton s)

/-- The intrinsic ordered distinct-atom rectangle count. Arbitrary
overlaps are resolved by the actual finite membership partition. -/
def rectangleFactorial (η : PointMeasure E) (A : J → Set E) : ℕ :=
  ∑ l : J → Set J, if ∀ j, j ∈ l j then
    ∏ s : Set J, (count η (patternCell A s)).descFactorial
      (Fintype.card {j : J // l j = s}) else 0

theorem rectangleFactorial_ofFintype (x : I → E) (A : J → Set E)
    (hA : ∀ j, MeasurableSet (A j)) :
    rectangleFactorial (ofFintype x) A =
      Fintype.card {e : J ↪ I // ∀ j, x (e j) ∈ A j} := by
  unfold rectangleFactorial
  simp_rw [count_ofFintype x (measurableSet_patternCell A hA _)]
  exact (rectangleTuple_card x A).symm

/-- Different finite atom presentations give the same distinct-label
tuple count, including coincident atoms and their multiplicities. -/
theorem tuple_card_eq_of_pointMeasure_eq {I' : Type*} [Fintype I']
    (x : I → E) (y : I' → E) (h : ofFintype x = ofFintype y)
    (A : J → Set E) (hA : ∀ j, MeasurableSet (A j)) :
    Fintype.card {e : J ↪ I // ∀ j, x (e j) ∈ A j} =
      Fintype.card {e : J ↪ I' // ∀ j, y (e j) ∈ A j} := by
  rw [← rectangleFactorial_ofFintype x A hA,← rectangleFactorial_ofFintype y A hA,h]

theorem rectangleFactorial_disjoint_labels (η : PointMeasure E) (C : D → Set E)
    (l : J → D) (hC : Pairwise (fun i j ↦ Disjoint (C i) (C j)))
    (hCm : ∀ i, MeasurableSet (C i)) :
    rectangleFactorial η (fun j ↦ C (l j)) =
      ∏ i : D, (count η (C i)).descFactorial (Fintype.card {j : J // l j = i}) := by
  obtain ⟨n,x,hx⟩ := η.property
  have hη : η = ofFintype x := Subtype.ext hx
  rw [hη,rectangleFactorial_ofFintype x _ (fun j ↦ hCm (l j))]
  simp_rw [count_ofFintype x (hCm _)]
  exact labelledCellTuple_card x C l hC

theorem rectangleFactorial_constant (η : PointMeasure E) (A : Set E) (hA : MeasurableSet A) :
    rectangleFactorial η (fun _ : J ↦ A) = (count η A).descFactorial (Fintype.card J) := by
  simpa using rectangleFactorial_disjoint_labels η (fun _ : Unit ↦ A) (fun _ : J ↦ ())
    (fun i j hij ↦ (hij (Subsingleton.elim _ _)).elim) (fun _ ↦ hA)

variable [TopologicalSpace E] [BorelSpace E] [HasOuterApproxClosed E]

theorem measurable_rectangleFactorial (A : J → Set E) (hA : ∀ j, MeasurableSet (A j)) :
    Measurable (fun η : PointMeasure E ↦ rectangleFactorial η A) := by
  apply Finset.measurable_sum
  intro l _
  by_cases hl : ∀ j, j ∈ l j
  · simp only [if_pos hl]
    apply Finset.measurable_prod
    intro s _
    exact (measurable_of_countable (fun n : ℕ ↦
      n.descFactorial (Fintype.card {j : J // l j = s}))).comp
        (FinitePointMeasureMeasurable.measurable_count (measurableSet_patternCell A hA s))
  · simp only [if_neg hl]
    exact measurable_const

end PerronWright.FinitePointMeasureRectangleFactorials
