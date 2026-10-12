import PerronWright.Enumeration.CubicConnectedComponentDecomposition

/-!
# Finite root-component factorization of the actual compensation sum

The two tables are independent once their original vertex and edge subsets
have been chosen.  The equality below is a proved finite bijection/cardinal
identity, including an empty cubic remainder, not a factorization premise.
-/

noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

namespace PerronWright.GraphCore

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Actual connected cubic half-edge tables on the given finite labels. -/
abbrev ConnectedCubicHalfEdgeTable (V E : Type*) [Fintype E] :=
  {x : UniformHalfEdgeAssignment (E × Bool) V 3 //
    (labelledHalfEdgeSupport x.val).Connected}

omit [Fintype V] in
/-- Once the two original label subsets are fixed, the root component and
the arbitrary remainder are two independent literal tables. -/
def cubicRootSplitEquivSigmaPair (root : V) :
    CubicRootSplit (E := E) root ≃
      Σ A : {A : Set V // root ∈ A}, Σ B : Set E,
        ConnectedCubicHalfEdgeTable A.val B ×
          UniformHalfEdgeAssignment ((Bᶜ : Set E) × Bool) (A.valᶜ : Set V) 3 where
  toFun D := ⟨⟨D.vertices,D.root_mem⟩, D.edges,
    ⟨D.inside,D.connected⟩, D.outside⟩
  invFun p := ⟨p.1.val,p.2.1,p.2.2.1.val,p.2.2.2,p.1.property,p.2.2.1.property⟩
  left_inv D := by cases D; rfl
  right_inv p := by
    rcases p with ⟨⟨A,hr⟩,B,⟨inside,hc⟩,outside⟩
    rfl

theorem card_cubicRootSplit_eq_sum_products (root : V) :
    Nat.card (CubicRootSplit (E := E) root) =
      ∑ A : {A : Set V // root ∈ A}, ∑ B : Set E,
        Nat.card (ConnectedCubicHalfEdgeTable A.val B) *
          Nat.card (UniformHalfEdgeAssignment ((Bᶜ : Set E) × Bool) (A.valᶜ : Set V) 3) := by
  rw [Nat.card_congr (cubicRootSplitEquivSigmaPair (E := E) root), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro A _
  rw [Nat.card_sigma]
  simp only [Nat.card_prod]

/-- Genuine pointing decomposition of the original finite cubic endpoint
presentation count, before replacing label-subset counts by binomial factors. -/
theorem card_cubicOrderedPresentation_eq_rootComponentSum
    (ell : ℕ) (root : Fin (2 * ell)) :
    Nat.card (CubicOrderedPresentation ell) =
      ∑ A : {A : Set (Fin (2 * ell)) // root ∈ A}, ∑ B : Set (Fin (3 * ell)),
        Nat.card (ConnectedCubicHalfEdgeTable A.val B) *
          Nat.card (UniformHalfEdgeAssignment
            ((Bᶜ : Set (Fin (3 * ell))) × Bool) (A.valᶜ : Set (Fin (2 * ell))) 3) := by
  rw [Nat.card_congr (cubicOrderedRootDecompositionEquiv ell root),
    card_cubicRootSplit_eq_sum_products]

/-- Exact finite connected-component factorization of the existing total
compensation coefficient.  Every summand counts actual tables on actual
label subsets, and has a genuinely connected inside component. -/
theorem allCubicCompensation_eq_rootComponentSum
    (ell : ℕ) (root : Fin (2 * ell)) :
    allCubicCompensation ell =
      (∑ A : {A : Set (Fin (2 * ell)) // root ∈ A}, ∑ B : Set (Fin (3 * ell)),
        (Nat.card (ConnectedCubicHalfEdgeTable A.val B) : ℝ) *
          (Nat.card (UniformHalfEdgeAssignment
            ((Bᶜ : Set (Fin (3 * ell))) × Bool) (A.valᶜ : Set (Fin (2 * ell))) 3) : ℝ)) /
        ((2 * ell).factorial * (3 * ell).factorial * (2 : ℝ) ^ (3 * ell)) := by
  rw [allCubicCompensation_eq_orderedCard, ← Nat.card_eq_fintype_card,
    card_cubicOrderedPresentation_eq_rootComponentSum ell root]
  simp only [Nat.cast_sum, Nat.cast_mul]

end PerronWright.GraphCore
