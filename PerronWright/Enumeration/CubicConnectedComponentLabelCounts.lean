import PerronWright.Enumeration.CubicConnectedComponentRelabel
import Mathlib.Data.Fintype.Powerset

/-!
# Actual label-subset counts in the root decomposition

The root lies in the inside vertex subset.  Its count is therefore the
pointed binomial coefficient, whereas the edge labels are unpointed.
-/

noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

namespace PerronWright.GraphCore

variable {V : Type*} [Fintype V]

def finiteSetCardEquivFinsetCard (k : ℕ) :
    {A : Set V // Nat.card A = k} ≃ {s : Finset V // s.card = k} where
  toFun A := ⟨A.val.toFinset,by
    simpa only [Set.toFinset_card,← Nat.card_eq_fintype_card] using A.property⟩
  invFun s := ⟨(s.val : Set V),by
    rw [Nat.card_eq_fintype_card,← Set.toFinset_card]
    simpa using s.property⟩
  left_inv A := by apply Subtype.ext; simp
  right_inv s := by apply Subtype.ext; simp

theorem card_finiteSet_of_card (k : ℕ) :
    Nat.card {A : Set V // Nat.card A = k} = (Nat.card V).choose k := by
  rw [Nat.card_congr (finiteSetCardEquivFinsetCard (V := V) k),
    Nat.card_eq_fintype_card,Fintype.card_finset_len,← Nat.card_eq_fintype_card]

def rootSetCardEquivFinsetFilter (root : V) (k : ℕ) :
    {A : Set V // root ∈ A ∧ Nat.card A = k} ≃
      {s : Finset V // s ∈ (Finset.univ.powersetCard k).filter (root ∈ ·)} where
  toFun A := ⟨A.val.toFinset,by
    simp only [Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and]
    exact ⟨by simpa only [Set.toFinset_card,← Nat.card_eq_fintype_card] using
      A.property.2,by simpa using A.property.1⟩⟩
  invFun s := ⟨(s.val : Set V),by
    have hs := s.property
    simp only [Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and] at hs
    refine ⟨hs.2,?_⟩
    rw [Nat.card_eq_fintype_card,← Set.toFinset_card]
    simpa using hs.1⟩
  left_inv A := by apply Subtype.ext; simp
  right_inv s := by apply Subtype.ext; simp

theorem card_rootSet_of_card (root : V) {k : ℕ} (hk : 1 ≤ k) :
    Nat.card {A : Set V // root ∈ A ∧ Nat.card A = k} =
      (Nat.card V - 1).choose (k - 1) := by
  rw [Nat.card_congr (rootSetCardEquivFinsetFilter root k),
    Nat.card_eq_fintype_card,Fintype.card_coe]
  simpa only [Finset.singleton_subset_iff,Finset.card_singleton,
    Finset.card_univ,← Nat.card_eq_fintype_card] using
    Finset.card_filter_powersetCard_subset {root} Finset.univ k
      (Finset.subset_univ _) (by simpa using hk)

theorem natCard_set_compl (A : Set V) :
    Nat.card (Aᶜ : Set V) = Nat.card V - Nat.card A := by
  simp only [Nat.card_eq_fintype_card,Fintype.card_compl_set]

end PerronWright.GraphCore
