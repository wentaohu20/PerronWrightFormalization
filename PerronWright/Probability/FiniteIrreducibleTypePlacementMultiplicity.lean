import PerronWright.Probability.IntegerTypeAssignment
import PerronWright.Probability.AnnealedTupleResidualCounting
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Exact type-preserving placement multiplicities

These finite identities concern actual embeddings into a deterministically
typed labelled vertex set. The falling-factorial depletion factor is proved
by a fibrewise embedding equivalence, for arbitrary assignments, not only
for the particular rounded realization.
-/

open scoped BigOperators Classical

noncomputable section

namespace PerronWright.FiniteIrreducibleTypePlacementMultiplicity

variable {A B S : Type*}

/-- Actual vertex injections whose images have the prescribed types. -/
abbrev TypePreservingEmbeddings (y : A → S) (x : B → S) :=
  {f : A ↪ B // ∀ v, x (f v) = y v}

/-- The selected vertices of each type inject into the corresponding ambient
type fibre, independently of the other type fibres. -/
abbrev FiberEmbeddings (y : A → S) (x : B → S) :=
  ∀ a : S, {v : A // y v = a} ↪ {w : B // x w = a}

def restrictToFibers (y : A → S) (x : B → S)
    (f : TypePreservingEmbeddings y x) : FiberEmbeddings y x :=
  fun _a ↦
    ⟨fun v ↦ ⟨f.val v.val, (f.property v.val).trans v.property⟩,
      fun _ _ h ↦ Subtype.ext (f.val.injective (congrArg Subtype.val h))⟩

/-- Assemble a genuine ambient vertex map from its type-fibre maps. -/
def assembleFibers (y : A → S) (x : B → S)
    (f : FiberEmbeddings y x) (v : A) : B :=
  (f (y v) ⟨v, rfl⟩).val

theorem assembleFibers_eq (y : A → S) (x : B → S)
    (f : FiberEmbeddings y x) (v : A) (a : S) (h : y v = a) :
    assembleFibers y x f v = (f a ⟨v, h⟩).val := by
  cases h
  rfl

theorem assembleFibers_injective (y : A → S) (x : B → S)
    (f : FiberEmbeddings y x) : Function.Injective (assembleFibers y x f) := by
  intro v w h
  have ht (u : A) : x (assembleFibers y x f u) = y u :=
    (f (y u) ⟨u, rfl⟩).property
  have hw : y w = y v := (ht w).symm.trans ((congrArg x h).symm.trans (ht v))
  have hval : (f (y v) ⟨v, rfl⟩).val = (f (y v) ⟨w, hw⟩).val :=
    h.trans (assembleFibers_eq y x f w (y v) hw)
  exact congrArg Subtype.val ((f (y v)).injective (Subtype.ext hval))

def embeddingOfFibers (y : A → S) (x : B → S)
    (f : FiberEmbeddings y x) : TypePreservingEmbeddings y x :=
  ⟨⟨assembleFibers y x f, assembleFibers_injective y x f⟩,
    fun v ↦ (f (y v) ⟨v, rfl⟩).property⟩

/-- Exact bijection, including impossible profiles and empty fibres. -/
def typePreservingEquivFibers (y : A → S) (x : B → S) :
    TypePreservingEmbeddings y x ≃ FiberEmbeddings y x where
  toFun := restrictToFibers y x
  invFun := embeddingOfFibers y x
  left_inv f := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro v
    rfl
  right_inv f := by
    funext a
    apply Function.Embedding.ext
    intro v
    apply Subtype.ext
    exact assembleFibers_eq y x f v.val a v.property

/-- Partition all genuine placements by their actual selected type vector. -/
def embeddingEquivSigmaTypePatterns (x : B → S) :
    (A ↪ B) ≃ Σ y : A → S, TypePreservingEmbeddings y x where
  toFun f := ⟨fun v ↦ x (f v), ⟨f, fun _ ↦ rfl⟩⟩
  invFun p := p.2.val
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨y, f, hf⟩
    have hy : (fun v ↦ x (f v)) = y := funext hf
    cases hy
    rfl

section Finite

variable [Fintype A] [Fintype B] [Fintype S]

/-- Literal finite fibre sizes of an actual type assignment. -/
def fiberCount (x : B → S) (a : S) : ℕ := Fintype.card {v : B // x v = a}

/-- Every prescribed selected type vector has exactly the product of the
ambient type-count falling factorials many placements. -/
theorem card_typePreservingEmbeddings (y : A → S) (x : B → S) :
    Fintype.card (TypePreservingEmbeddings y x) =
      ∏ a : S, (fiberCount x a).descFactorial (fiberCount y a) := by
  rw [Fintype.card_congr (typePreservingEquivFibers y x), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro a _
  exact Fintype.card_embedding_eq

/-- Weighted finite regrouping of actual vertex injections. The test
function can be any function of the full selected type vector. -/
theorem sum_embeddings_by_typePattern (x : B → S) (W : (A → S) → ℝ) :
    (∑ f : A ↪ B, W (fun v ↦ x (f v))) =
      ∑ y : A → S,
        (∏ a : S, ((fiberCount x a).descFactorial (fiberCount y a) : ℝ)) * W y := by
  let e := embeddingEquivSigmaTypePatterns (A := A) x
  calc
    _ = ∑ p : (Σ y : A → S, TypePreservingEmbeddings y x),
        W (fun v ↦ x (p.2.val v)) := by
      exact (e.symm.sum_comp (fun f : A ↪ B ↦ W (fun v ↦ x (f v)))).symm
    _ = ∑ p : (Σ y : A → S, TypePreservingEmbeddings y x), W p.1 := by
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      funext v
      exact p.2.property v
    _ = ∑ y : A → S, ∑ _f : TypePreservingEmbeddings y x, W y :=
      Fintype.sum_sigma _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        card_typePreservingEmbeddings, Nat.cast_prod]

end Finite

section LiteralCounts

variable [Fintype S]

/-- For any integer counts summing to n, the constructed actual vertex
assignment realizes the precise type-preserving placement multiplicity. -/
theorem card_typePreservingEmbeddings_integerTypeVector
    {n : ℕ} [Fintype A] (c : S → ℕ) (hc : ∑ a, c a = n) (y : A → S) :
    Fintype.card (TypePreservingEmbeddings y (IntegerTypeAssignment.typeVector c hc)) =
      ∏ a : S, (c a).descFactorial (fiberCount y a) := by
  rw [card_typePreservingEmbeddings]
  apply Finset.prod_congr rfl
  intro a _
  rw [fiberCount, IntegerTypeAssignment.typeVector_fiber_card]

end LiteralCounts

end PerronWright.FiniteIrreducibleTypePlacementMultiplicity
