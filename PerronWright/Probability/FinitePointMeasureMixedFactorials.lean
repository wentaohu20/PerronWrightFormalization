import PerronWright.Probability.FinitePointMeasureFintype
import PerronWright.Probability.FactorialCountDeterminacy
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Actual mixed factorials of disjoint cells in finite labelled atom families

The tuple count is proved by a bijection with independent embeddings
into each cell fibre. Disjointness makes these local embeddings jointly
injective. Coincident atoms keep their distinct labels and multiplicity.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FinitePointMeasureMixedFactorials

open FinitePointMeasureCompact FinitePointMeasureFintype FactorialCountDeterminacy

variable {E I D : Type*} [Fintype I] [Fintype D]

abbrev Slots (q : D → ℕ) := Σ i : D, Fin (q i)

def cellTupleEquiv (x : I → E) (A : D → Set E) (q : D → ℕ)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) :
    {e : Slots q ↪ I // ∀ s, x (e s) ∈ A s.1} ≃
      (∀ i : D, Fin (q i) ↪ {j : I // x j ∈ A i}) where
  toFun e i := ⟨fun j ↦ ⟨e.val ⟨i, j⟩, e.property ⟨i, j⟩⟩, by
    intro j k hjk
    have he := e.val.injective (congrArg Subtype.val hjk)
    simpa using he⟩
  invFun f := ⟨⟨fun s ↦ (f s.1 s.2).val, by
    rintro ⟨i, j⟩ ⟨k, l⟩ he
    by_cases hik : i = k
    · subst k
      have hjl := (f i).injective (Subtype.ext he)
      change j = l at hjl
      cases hjl
      rfl
    · exact False.elim (Set.disjoint_left.mp (hA hik)
        (f i j).property (by
          change (f i j).val = (f k l).val at he
          rw [he]
          exact (f k l).property))⟩,
    fun s ↦ (f s.1 s.2).property⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro s
    rfl
  right_inv f := by
    funext i
    apply Function.Embedding.ext
    intro j
    rfl

theorem cellTuple_card (x : I → E) (A : D → Set E) (q : D → ℕ)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) :
    Fintype.card {e : Slots q ↪ I // ∀ s, x (e s) ∈ A s.1} =
      ∏ i : D, (Fintype.card {j : I // x j ∈ A i}).descFactorial (q i) := by
  rw [Fintype.card_congr (cellTupleEquiv x A q hA), Fintype.card_pi]
  simp only [Fintype.card_embedding_eq, Fintype.card_fin]

/-- A genuine enumeration of all labelled slots by `Fin (sum q)`. -/
def slotFinEquiv (q : D → ℕ) : Slots q ≃ Fin (∑ i, q i) :=
  (Fintype.equivFin (Slots q)).trans (Equiv.cast (congrArg Fin (by simp [Slots])))

def label (q : D → ℕ) (j : Fin (∑ i, q i)) : D := ((slotFinEquiv q).symm j).1

def OrderedCellTuples (x : I → E) (A : D → Set E) (q : D → ℕ) :=
  {e : Fin (∑ i, q i) ↪ I // ∀ j, x (e j) ∈ A (label q j)}

instance (x : I → E) (A : D → Set E) (q : D → ℕ) :
    Fintype (OrderedCellTuples x A q) := inferInstanceAs
      (Fintype {e : Fin (∑ i, q i) ↪ I // ∀ j, x (e j) ∈ A (label q j)})

def orderedCellTupleEquiv (x : I → E) (A : D → Set E) (q : D → ℕ) :
    OrderedCellTuples x A q ≃ {e : Slots q ↪ I // ∀ s, x (e s) ∈ A s.1} where
  toFun e := ⟨⟨fun s ↦ e.val (slotFinEquiv q s),
    fun s t hst ↦ (slotFinEquiv q).injective (e.val.injective hst)⟩, by
    intro s
    change x (e.val (slotFinEquiv q s)) ∈ A s.1
    simpa only [label, Equiv.symm_apply_apply] using e.property (slotFinEquiv q s)⟩
  invFun e := ⟨⟨fun j ↦ e.val ((slotFinEquiv q).symm j),
    fun j k hjk ↦ (slotFinEquiv q).symm.injective (e.val.injective hjk)⟩,
    fun j ↦ e.property ((slotFinEquiv q).symm j)⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro j
    exact congrArg e.val ((slotFinEquiv q).apply_symm_apply j)
  right_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro s
    exact congrArg e.val ((slotFinEquiv q).symm_apply_apply s)

theorem orderedCellTuple_card (x : I → E) (A : D → Set E) (q : D → ℕ)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) :
    Fintype.card (OrderedCellTuples x A q) =
      ∏ i : D, (Fintype.card {j : I // x j ∈ A i}).descFactorial (q i) := by
  rw [Fintype.card_congr (orderedCellTupleEquiv x A q), cellTuple_card x A q hA]

variable [MeasurableSpace E]

/-- The actual point measure's mixed descending factorial is exactly
the cardinality of labelled injective atom tuples with the cell labels. -/
theorem factorialPolynomial_eq_tuple_card (x : I → E) (A : D → Set E) (q : D → ℕ)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hAm : ∀ i, MeasurableSet (A i)) :
    factorialPolynomial q (fun i ↦ count (ofFintype x) (A i)) =
      (Fintype.card (OrderedCellTuples x A q) : ℝ) := by
  unfold factorialPolynomial
  simp_rw [count_ofFintype x (hAm _)]
  rw [orderedCellTuple_card x A q hA]
  simp only [Nat.cast_prod]

end PerronWright.FinitePointMeasureMixedFactorials
