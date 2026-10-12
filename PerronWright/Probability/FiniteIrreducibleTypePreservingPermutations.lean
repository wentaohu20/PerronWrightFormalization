import PerronWright.Probability.FiniteIrreducibleTypePlacementMultiplicity
import Mathlib.Logic.Equiv.Fintype

/-!
# Type-preserving ambient permutations

Actual placements with the same selected type vector are related by an
ambient permutation preserving the entire fixed type assignment.
No exchangeability of different types is asserted.
-/

open scoped BigOperators Classical

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleTypePreservingPermutations

open FiniteIrreducibleTypePlacementMultiplicity

variable {A B S : Type*}

/-- Any two injections into a finite set are related by a permutation. -/
theorem exists_permutation_embeddings {C D : Type*} [Fintype C] [Fintype D]
    (f g : C ↪ D) : ∃ σ : Equiv.Perm D, ∀ v, σ (f v) = g v := by
  let E := (Function.Embedding.toEquivRange f).symm.trans
    (Function.Embedding.toEquivRange g)
  refine ⟨E.extendSubtype, ?_⟩
  intro v
  rw [Equiv.extendSubtype_apply_of_mem E (f v) ⟨v, rfl⟩]
  change (E ⟨f v, ⟨v, rfl⟩⟩).val = g v
  simp only [E, Equiv.trans_apply]
  have h : (Function.Embedding.toEquivRange f).symm ⟨f v, ⟨v, rfl⟩⟩ = v :=
    (Function.Embedding.toEquivRange f).symm_apply_apply v
  rw [h]
  rfl

/-- Assemble arbitrary permutations within the actual type fibres into
an ambient permutation of the labelled vertex set. -/
def permutationOfFibers (x : B → S)
    (p : ∀ a : S, Equiv.Perm {v : B // x v = a}) : Equiv.Perm B :=
  (Equiv.sigmaFiberEquiv x).symm.trans
    ((Equiv.sigmaCongrRight p).trans (Equiv.sigmaFiberEquiv x))

@[simp] theorem permutationOfFibers_apply (x : B → S)
    (p : ∀ a : S, Equiv.Perm {v : B // x v = a}) (v : B) :
    permutationOfFibers x p v = (p (x v) ⟨v, rfl⟩).val := rfl

theorem permutationOfFibers_preserves_type (x : B → S)
    (p : ∀ a : S, Equiv.Perm {v : B // x v = a}) (v : B) :
    x (permutationOfFibers x p v) = x v :=
  (p (x v) ⟨v, rfl⟩).property

theorem permutationOfFibers_apply_of_type (x : B → S)
    (p : ∀ a : S, Equiv.Perm {v : B // x v = a})
    (v : B) (a : S) (hv : x v = a) :
    permutationOfFibers x p v = (p a ⟨v, hv⟩).val := by
  cases hv
  rfl

/-- Genuine placements with identical selected types are connected by
a permutation preserving every ambient vertex's fixed type. -/
theorem exists_typePreserving_permutation [Fintype A] [Fintype B]
    (y : A → S) (x : B → S)
    (f g : TypePreservingEmbeddings y x) :
    ∃ σ : Equiv.Perm B, (∀ v, x (σ v) = x v) ∧
      ∀ v, σ (f.val v) = g.val v := by
  have h (a : S) := exists_permutation_embeddings
    (restrictToFibers y x f a) (restrictToFibers y x g a)
  choose p hp using h
  refine ⟨permutationOfFibers x p, permutationOfFibers_preserves_type x p, ?_⟩
  intro v
  rw [permutationOfFibers_apply_of_type x p (f.val v) (y v) (f.property v)]
  have hh := hp (y v) ⟨v, rfl⟩
  exact congrArg Subtype.val hh

end PerronWright.FiniteIrreducibleTypePreservingPermutations

