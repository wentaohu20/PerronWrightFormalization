import PerronWright.Enumeration.UnicyclicCore
import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Exact orientation multiplicity of a labelled simple cycle

This module realizes an oriented Hamiltonian cycle as a full-support cyclic
permutation and proves that forgetting the orientation has the exact two-element
fibres given by inversion.  In particular, it proves the denominator-free form
of the classical labelled-cycle multiplicity `q! / (2q)`.
-/

open scoped Classical BigOperators
noncomputable section

namespace PerronWright
namespace GraphCore

/-- Cyclic permutations whose unique cycle uses every element of `Fin q`. -/
abbrev FullCyclePerm (q : ℕ) :=
  {σ : Equiv.Perm (Fin q) // σ.cycleType = {q}}

namespace FullCyclePerm

theorem isCycle {q : ℕ} (σ : FullCyclePerm q) : σ.1.IsCycle := by
  rw [← Equiv.Perm.card_cycleType_eq_one]
  simp only [σ.2, Multiset.card_singleton]

theorem card_support {q : ℕ} (σ : FullCyclePerm q) :
    σ.1.support.card = q := by
  rw [← σ.1.sum_cycleType, σ.2, Multiset.sum_singleton]

theorem support_eq_univ {q : ℕ} (σ : FullCyclePerm q) :
    σ.1.support = Finset.univ := by
  apply (Finset.card_eq_iff_eq_univ σ.1.support).mp
  rw [card_support, Fintype.card_fin]

theorem apply_ne_self {q : ℕ} (σ : FullCyclePerm q) (x : Fin q) :
    σ.1 x ≠ x := by
  rw [← Equiv.Perm.mem_support, support_eq_univ]
  exact Finset.mem_univ x

/-- Reversing the orientation of a full cycle. -/
def reverse {q : ℕ} (σ : FullCyclePerm q) : FullCyclePerm q :=
  ⟨σ.1⁻¹, by simpa only [Equiv.Perm.cycleType_inv] using σ.2⟩

@[simp]
theorem coe_reverse {q : ℕ} (σ : FullCyclePerm q) :
    (reverse σ).1 = σ.1⁻¹ := rfl

@[simp]
theorem reverse_reverse {q : ℕ} (σ : FullCyclePerm q) :
    reverse (reverse σ) = σ := by
  apply Subtype.ext
  exact inv_inv σ.1

/-- A full cycle on at least three vertices does not immediately backtrack. -/
theorem apply_apply_ne_self {q : ℕ} (hq : 3 ≤ q)
    (σ : FullCyclePerm q) (x : Fin q) :
    σ.1 (σ.1 x) ≠ x := by
  intro hback
  have hswap : σ.1 = Equiv.swap x (σ.1 x) :=
    σ.isCycle.eq_swap_of_apply_apply_eq_self (σ.apply_ne_self x) hback
  have hcardtwo : σ.1.support.card = 2 := by
    rw [hswap]
    exact Equiv.Perm.card_support_swap (σ.apply_ne_self x).symm
  rw [σ.card_support] at hcardtwo
  omega

/-- The unoriented simple graph underlying a full cyclic permutation. -/
def graph {q : ℕ} (σ : FullCyclePerm q) : SimpleGraph (Fin q) :=
  SimpleGraph.fromRel (fun x y ↦ σ.1 x = y)

theorem graph_adj_iff {q : ℕ} (σ : FullCyclePerm q) (x y : Fin q) :
    (graph σ).Adj x y ↔ σ.1 x = y ∨ σ.1 y = x := by
  rw [graph, SimpleGraph.fromRel_adj]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with h | h
    · exact σ.apply_ne_self x h
    · exact σ.apply_ne_self x h

@[simp]
theorem graph_reverse {q : ℕ} (σ : FullCyclePerm q) :
    graph (σ.reverse) = graph σ := by
  ext x y
  rw [graph_adj_iff, graph_adj_iff]
  change (σ.1.symm x = y ∨ σ.1.symm y = x) ↔
    (σ.1 x = y ∨ σ.1 y = x)
  constructor
  · rintro (h | h)
    · exact Or.inr ((σ.1.symm_apply_eq).mp h).symm
    · exact Or.inl ((σ.1.symm_apply_eq).mp h).symm
  · rintro (h | h)
    · exact Or.inr ((σ.1.symm_apply_eq).mpr h.symm)
    · exact Or.inl ((σ.1.symm_apply_eq).mpr h.symm)

/-- If two orientations agree at one vertex and determine the same unoriented
cycle, then they agree everywhere. -/
theorem eq_of_graph_eq_of_apply_eq {q : ℕ} (hq : 3 ≤ q)
    (σ τ : FullCyclePerm q)
    (hgraph : graph σ = graph τ) (x₀ : Fin q)
    (hx₀ : τ.1 x₀ = σ.1 x₀) :
    τ = σ := by
  have hpropagate : ∀ x : Fin q, τ.1 x = σ.1 x →
      τ.1 (σ.1 x) = σ.1 (σ.1 x) := by
    intro x hx
    have hadjτ : (graph τ).Adj (σ.1 x) (τ.1 (σ.1 x)) :=
      (τ.graph_adj_iff _ _).mpr (Or.inl rfl)
    have hadjσ : (graph σ).Adj (σ.1 x) (τ.1 (σ.1 x)) := by
      rw [hgraph]
      exact hadjτ
    rcases (σ.graph_adj_iff _ _).mp hadjσ with hforward | hback
    · exact hforward.symm
    · exfalso
      apply τ.apply_apply_ne_self hq x
      calc
        τ.1 (τ.1 x) = τ.1 (σ.1 x) := congrArg τ.1 hx
        _ = x := σ.1.injective hback
  have hpowers : ∀ n : ℕ,
      τ.1 ((σ.1 ^ n) x₀) = σ.1 ((σ.1 ^ n) x₀) := by
    intro n
    induction n with
    | zero => simpa using hx₀
    | succ n ih =>
        simpa only [pow_succ', Equiv.Perm.mul_apply] using hpropagate _ ih
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨n, hn⟩ := σ.isCycle.exists_pow_eq
    (σ.apply_ne_self x₀) (σ.apply_ne_self x)
  calc
    τ.1 x = τ.1 ((σ.1 ^ n) x₀) := congrArg τ.1 hn.symm
    _ = σ.1 ((σ.1 ^ n) x₀) := hpowers n
    _ = σ.1 x := congrArg σ.1 hn

/-- Exact classification of the two orientations of an unoriented labelled
cycle. -/
theorem graph_eq_iff {q : ℕ} (hq : 3 ≤ q) (σ τ : FullCyclePerm q) :
    graph τ = graph σ ↔ τ = σ ∨ τ = σ.reverse := by
  constructor
  · intro hgraph
    let x₀ : Fin q := ⟨0, by omega⟩
    have hadjτ : (graph τ).Adj x₀ (τ.1 x₀) :=
      (τ.graph_adj_iff _ _).mpr (Or.inl rfl)
    have hadjσ : (graph σ).Adj x₀ (τ.1 x₀) := by
      rw [← hgraph]
      exact hadjτ
    rcases (σ.graph_adj_iff _ _).mp hadjσ with hforward | hback
    · exact Or.inl (eq_of_graph_eq_of_apply_eq hq σ τ hgraph.symm x₀ hforward.symm)
    · apply Or.inr
      apply eq_of_graph_eq_of_apply_eq hq σ.reverse τ
      · calc
          graph σ.reverse = graph σ := graph_reverse σ
          _ = graph τ := hgraph.symm
      · exact σ.1.eq_symm_apply.mpr hback
  · rintro (rfl | rfl)
    · rfl
    · exact graph_reverse σ

theorem ne_reverse {q : ℕ} (hq : 3 ≤ q) (σ : FullCyclePerm q) :
    σ ≠ σ.reverse := by
  intro h
  let x : Fin q := ⟨0, by omega⟩
  apply σ.apply_apply_ne_self hq x
  have hinv : σ.1⁻¹ x = σ.1 x := by
    have := congrArg (fun π : FullCyclePerm q ↦ π.1 x) h
    simpa only [coe_reverse] using this.symm
  calc
    σ.1 (σ.1 x) = σ.1 (σ.1⁻¹ x) := congrArg σ.1 hinv.symm
    _ = x := σ.1.apply_symm_apply x

/-- The literal fibre over the unoriented graph underlying `σ`. -/
def graphFiber {q : ℕ} (σ : FullCyclePerm q) : Finset (FullCyclePerm q) :=
  Finset.univ.filter (fun τ ↦ graph τ = graph σ)

theorem graphFiber_eq_pair {q : ℕ} (hq : 3 ≤ q) (σ : FullCyclePerm q) :
    graphFiber σ = {σ, σ.reverse} := by
  ext τ
  simp only [graphFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  exact graph_eq_iff hq σ τ

/-- Every unoriented labelled cycle has exactly two full-cycle orientations. -/
theorem card_graphFiber {q : ℕ} (hq : 3 ≤ q) (σ : FullCyclePerm q) :
    (graphFiber σ).card = 2 := by
  rw [graphFiber_eq_pair hq σ]
  simp [ne_reverse hq σ]

/-- There are `(q-1)!` oriented full cycles on `Fin q`. -/
theorem card_fullCyclePerm {q : ℕ} (hq : 2 ≤ q) :
    Fintype.card (FullCyclePerm q) = (q - 1).factorial := by
  classical
  rw [Fintype.card_subtype]
  simpa only [Fintype.card_fin, Nat.choose_self, mul_one] using
    (Equiv.Perm.card_of_cycleType_singleton (α := Fin q) hq (by simp))

/-- The literal finite range of the orientation-forgetting map. -/
def graphRange (q : ℕ) : Finset (SimpleGraph (Fin q)) :=
  Finset.univ.image graph

/-- The full-cycle permutations are partitioned into two-element orientation
fibres over their unoriented graphs. -/
theorem card_fullCyclePerm_eq_card_graphRange_mul_two {q : ℕ} (hq : 3 ≤ q) :
    Fintype.card (FullCyclePerm q) = (graphRange q).card * 2 := by
  classical
  calc
    Fintype.card (FullCyclePerm q) =
        (Finset.univ : Finset (FullCyclePerm q)).card := by simp
    _ = ∑ G ∈ graphRange q,
          ((Finset.univ : Finset (FullCyclePerm q)).filter
            (fun σ ↦ graph σ = G)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro σ _
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
    _ = ∑ _G ∈ graphRange q, 2 := by
      apply Finset.sum_congr rfl
      intro G hG
      rcases Finset.mem_image.mp hG with ⟨σ, -, rfl⟩
      exact card_graphFiber hq σ
    _ = (graphRange q).card * 2 := by simp

/-- Consequently the number of unoriented labelled `q`-cycles has the exact
factor `(q-1)!/2`.  The multiplication form avoids truncated division. -/
theorem card_graphRange_mul_two_eq_factorial {q : ℕ} (hq : 3 ≤ q) :
    (graphRange q).card * 2 = (q - 1).factorial := by
  calc
    (graphRange q).card * 2 = Fintype.card (FullCyclePerm q) :=
      (card_fullCyclePerm_eq_card_graphRange_mul_two hq).symm
    _ = (q - 1).factorial := card_fullCyclePerm (by omega)

/-- The denominator-free form of the classical `q!/(2q)` labelled-cycle
multiplicity. -/
theorem card_graphRange_mul_two_mul_q_eq_factorial {q : ℕ} (hq : 3 ≤ q) :
    (graphRange q).card * (2 * q) = q.factorial := by
  calc
    (graphRange q).card * (2 * q) = ((graphRange q).card * 2) * q :=
      (Nat.mul_assoc _ _ _).symm
    _ = (q - 1).factorial * q := by rw [card_graphRange_mul_two_eq_factorial hq]
    _ = q.factorial := by
      rw [mul_comm, Nat.mul_factorial_pred (by omega : q ≠ 0)]

end FullCyclePerm
end GraphCore
end PerronWright
