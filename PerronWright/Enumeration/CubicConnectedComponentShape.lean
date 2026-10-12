import PerronWright.Enumeration.CubicConnectedComponentLabelCounts

/-!
# Size grouping of the actual root component

The index is recovered from the actual connected component, whose degree
fibres force exactly `2*j` vertices and `3*j` edges.  The complement keeps
its original labels and can include no vertices and no edges.
-/

noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

namespace PerronWright.GraphCore

abbrev CubicRootSize (ell : ℕ) := {j : ℕ // 0 < j ∧ j ≤ ell}

noncomputable instance cubicRootSizeFintype (ell : ℕ) : Fintype (CubicRootSize ell) :=
  Fintype.ofInjective (fun j ↦ (⟨j.val,Nat.lt_succ_of_le j.property.2⟩ : Fin (ell + 1)))
    (fun _i _j h ↦ Subtype.ext (congrArg Fin.val h))

abbrev CubicRootShapeData (ell : ℕ) (root : Fin (2 * ell)) (j : ℕ) :=
  Σ A : {A : Set (Fin (2 * ell)) // root ∈ A ∧ Nat.card A = 2 * j},
    Σ B : {B : Set (Fin (3 * ell)) // Nat.card B = 3 * j},
      ConnectedCubicHalfEdgeTable A.val B.val ×
        UniformHalfEdgeAssignment
          ((B.valᶜ : Set (Fin (3 * ell))) × Bool) (A.valᶜ : Set (Fin (2 * ell))) 3

theorem CubicRootSplit.size_index {ell : ℕ} {root : Fin (2 * ell)}
    (D : CubicRootSplit (E := Fin (3 * ell)) root) :
    0 < Nat.card D.vertices / 2 ∧ Nat.card D.vertices / 2 ≤ ell ∧
      Nat.card D.vertices = 2 * (Nat.card D.vertices / 2) ∧
      Nat.card D.edges = 3 * (Nat.card D.vertices / 2) := by
  rcases D.cardinalities with ⟨j,hj,hjl,hA,hB⟩
  rw [hA,hB]
  omega

def cubicRootSplitEquivShape (ell : ℕ) (root : Fin (2 * ell)) :
    CubicRootSplit (E := Fin (3 * ell)) root ≃
      Σ j : CubicRootSize ell, CubicRootShapeData ell root j.val where
  toFun D := ⟨⟨Nat.card D.vertices / 2,D.size_index.1,D.size_index.2.1⟩,
    ⟨⟨D.vertices,D.root_mem,D.size_index.2.2.1⟩,
      ⟨D.edges,D.size_index.2.2.2⟩,⟨D.inside,D.connected⟩,D.outside⟩⟩
  invFun p := ⟨p.2.1.val,p.2.2.1.val,p.2.2.2.1.val,p.2.2.2.2,
    p.2.1.property.1,p.2.2.2.1.property⟩
  left_inv D := by cases D; rfl
  right_inv p := by
    rcases p with ⟨⟨j,hj⟩,⟨⟨A,hr,hA⟩,⟨B,hB⟩,⟨inside,hc⟩,outside⟩⟩
    have hindex : Nat.card A / 2 = j := by
      rw [hA]
      change 2 * j / 2 = j
      omega
    cases hindex
    rfl

theorem card_cubicRootShapeData (ell : ℕ) (root : Fin (2 * ell))
    (j : CubicRootSize ell) :
    Nat.card (CubicRootShapeData ell root j.val) =
      (2 * ell - 1).choose (2 * j.val - 1) * (3 * ell).choose (3 * j.val) *
        Nat.card (ConnectedCubicHalfEdgeTable (Fin (2 * j.val)) (Fin (3 * j.val))) *
        Nat.card (UniformHalfEdgeAssignment
          (Fin (3 * (ell - j.val)) × Bool) (Fin (2 * (ell - j.val))) 3) := by
  rw [Nat.card_sigma]
  have hremA (A : {A : Set (Fin (2 * ell)) // root ∈ A ∧ Nat.card A = 2 * j.val}) :
      Nat.card (A.valᶜ : Set (Fin (2 * ell))) = 2 * (ell - j.val) := by
    rw [natCard_set_compl,A.property.2,Nat.card_fin]
    omega
  have hremB (B : {B : Set (Fin (3 * ell)) // Nat.card B = 3 * j.val}) :
      Nat.card (B.valᶜ : Set (Fin (3 * ell))) = 3 * (ell - j.val) := by
    rw [natCard_set_compl,B.property,Nat.card_fin]
    omega
  have hterm (A : {A : Set (Fin (2 * ell)) // root ∈ A ∧ Nat.card A = 2 * j.val}) :
      Nat.card (Σ B : {B : Set (Fin (3 * ell)) // Nat.card B = 3 * j.val},
        ConnectedCubicHalfEdgeTable A.val B.val ×
          UniformHalfEdgeAssignment
            ((B.valᶜ : Set (Fin (3 * ell))) × Bool) (A.valᶜ : Set (Fin (2 * ell))) 3) =
      (3 * ell).choose (3 * j.val) *
        Nat.card (ConnectedCubicHalfEdgeTable (Fin (2 * j.val)) (Fin (3 * j.val))) *
        Nat.card (UniformHalfEdgeAssignment
          (Fin (3 * (ell - j.val)) × Bool) (Fin (2 * (ell - j.val))) 3) := by
    rw [Nat.card_sigma]
    have htermB (B : {B : Set (Fin (3 * ell)) // Nat.card B = 3 * j.val}) :
        Nat.card (ConnectedCubicHalfEdgeTable A.val B.val ×
          UniformHalfEdgeAssignment
            ((B.valᶜ : Set (Fin (3 * ell))) × Bool) (A.valᶜ : Set (Fin (2 * ell))) 3) =
        Nat.card (ConnectedCubicHalfEdgeTable (Fin (2 * j.val)) (Fin (3 * j.val))) *
          Nat.card (UniformHalfEdgeAssignment
            (Fin (3 * (ell - j.val)) × Bool) (Fin (2 * (ell - j.val))) 3) := by
      rw [Nat.card_prod,
        card_connectedCubicHalfEdgeTable_of_card_eq A.property.2 B.property,
        card_uniformHalfEdgeAssignment_of_card_eq (hremA A) (hremB B)]
    simp_rw [htermB]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,
      ← Nat.card_eq_fintype_card,card_finiteSet_of_card,Nat.card_fin]
    ring
  simp_rw [hterm]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,← Nat.card_eq_fintype_card]
  rw [card_rootSet_of_card root (by omega),Nat.card_fin]
  ring

theorem card_cubicOrderedPresentation_eq_scalarRootSum
    (ell : ℕ) (root : Fin (2 * ell)) :
    Nat.card (CubicOrderedPresentation ell) =
      ∑ j : CubicRootSize ell,
        (2 * ell - 1).choose (2 * j.val - 1) * (3 * ell).choose (3 * j.val) *
          Nat.card (ConnectedCubicHalfEdgeTable (Fin (2 * j.val)) (Fin (3 * j.val))) *
          Nat.card (UniformHalfEdgeAssignment
            (Fin (3 * (ell - j.val)) × Bool) (Fin (2 * (ell - j.val))) 3) := by
  rw [Nat.card_congr (cubicOrderedRootDecompositionEquiv ell root),
    Nat.card_congr (cubicRootSplitEquivShape ell root),Nat.card_sigma]
  exact Finset.sum_congr rfl (fun j _ ↦ card_cubicRootShapeData ell root j)

end PerronWright.GraphCore
