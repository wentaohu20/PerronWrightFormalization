import PerronWright.Enumeration.CubicConnectedComponentCut
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The actual root component of a labelled half-edge table

The root cut is extracted from the genuine support graph.  Its endpoint
tables preserve degree fibres, and its inside graph is the actual connected
component, not a separately asserted connected object.
-/

noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

namespace PerronWright.GraphCore

variable {V E : Type*}

theorem cutTableInside_support_eq_induce {A : Set V} {B : Set E}
    (x : CutHalfEdgeTable A B) :
    labelledHalfEdgeSupport (cutTableInside x) = (labelledHalfEdgeSupport x.val).induce A := by
  ext u v
  change ((∃ i : B,
      s(cutTableInside x (i,false),cutTableInside x (i,true)) = s(u,v)) ∧ u ≠ v) ↔
    ((∃ i : E, s(x.val (i,false),x.val (i,true)) = s(u.val,v.val)) ∧ u.val ≠ v.val)
  constructor
  · rintro ⟨⟨i,hi⟩,hne⟩
    refine ⟨⟨i.val, ?_⟩, fun h ↦ hne (Subtype.ext h)⟩
    simpa only [Sym2.map_mk, cutTableInside] using congrArg (Sym2.map Subtype.val) hi
  · rintro ⟨⟨i,hi⟩,hne⟩
    have hmem : x.val (i,false) ∈ A := by
      rcases Sym2.eq_iff.mp hi with h | h
      · rw [h.1]; exact u.property
      · rw [h.1]; exact v.property
    let ib : B := ⟨i,(x.property _ _).1 hmem⟩
    refine ⟨⟨ib,?_⟩, fun h ↦ hne (congrArg Subtype.val h)⟩
    apply Sym2.map.injective Subtype.val_injective
    simpa only [Sym2.map_mk, cutTableInside] using hi

theorem cutTable_support_closed {A : Set V} {B : Set E}
    (x : CutHalfEdgeTable A B) {u v : V} (hu : u ∈ A)
    (h : (labelledHalfEdgeSupport x.val).Adj u v) : v ∈ A := by
  rcases h.1 with ⟨i,hi⟩
  rcases Sym2.eq_iff.mp hi with h | h
  · have he : i ∈ B := (x.property i false).1 (h.1 ▸ hu)
    exact h.2 ▸ (x.property i true).2 he
  · have he : i ∈ B := (x.property i true).1 (h.2 ▸ hu)
    exact h.1 ▸ (x.property i false).2 he

theorem cutTable_reachable_mem {A : Set V} {B : Set E}
    (x : CutHalfEdgeTable A B) {u v : V} (hu : u ∈ A)
    (h : (labelledHalfEdgeSupport x.val).Reachable u v) : v ∈ A := by
  have hw {u v : V} (p : (labelledHalfEdgeSupport x.val).Walk u v) :
      u ∈ A → v ∈ A := by
    induction p with
    | nil => exact id
    | cons hadj p ih => exact fun hu ↦ ih (cutTable_support_closed x hu hadj)
  exact hw h.some hu

/-- Connectedness of the inside graph identifies the cut with the actual
root component; no equality of components is assumed. -/
theorem cutTable_reachable_iff_mem {A : Set V} {B : Set E}
    (x : CutHalfEdgeTable A B) (root : V) (hr : root ∈ A)
    (hc : (labelledHalfEdgeSupport (cutTableInside x)).Connected) (v : V) :
    (labelledHalfEdgeSupport x.val).Reachable root v ↔ v ∈ A := by
  constructor
  · exact cutTable_reachable_mem x hr
  · intro hv
    rw [cutTableInside_support_eq_induce] at hc
    exact (hc ⟨root,hr⟩ ⟨v,hv⟩).map (SimpleGraph.Embedding.induce A).toHom

def rootHalfEdgeVertices (x : E × Bool → V) (root : V) : Set V :=
  ((labelledHalfEdgeSupport x).connectedComponentMk root).supp

def rootHalfEdgeEdges (x : E × Bool → V) (root : V) : Set E :=
  {e | x (e,false) ∈ rootHalfEdgeVertices x root}

theorem mem_rootHalfEdgeVertices_iff (x : E × Bool → V) (root v : V) :
    v ∈ rootHalfEdgeVertices x root ↔ (labelledHalfEdgeSupport x).Reachable root v := by
  simp only [rootHalfEdgeVertices, SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq]
  exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

theorem root_mem_rootHalfEdgeVertices (x : E × Bool → V) (root : V) :
    root ∈ rootHalfEdgeVertices x root := by
  rw [mem_rootHalfEdgeVertices_iff]

theorem halfEdge_sides_reachable (x : E × Bool → V) (e : E) :
    (labelledHalfEdgeSupport x).Reachable (x (e,false)) (x (e,true)) := by
  by_cases h : x (e,false) = x (e,true)
  · rw [h]
  · exact (show (labelledHalfEdgeSupport x).Adj (x (e,false)) (x (e,true)) from
      ⟨⟨e,rfl⟩,h⟩).reachable

theorem rootHalfEdge_side_mem_iff (x : E × Bool → V) (root : V) (e : E) (b : Bool) :
    x (e,b) ∈ rootHalfEdgeVertices x root ↔ e ∈ rootHalfEdgeEdges x root := by
  cases b
  · rfl
  · change x (e,true) ∈ rootHalfEdgeVertices x root ↔
      x (e,false) ∈ rootHalfEdgeVertices x root
    simp only [mem_rootHalfEdgeVertices_iff]
    exact ⟨fun h ↦ h.trans (halfEdge_sides_reachable x e).symm,
      fun h ↦ h.trans (halfEdge_sides_reachable x e)⟩

/-- The canonical cut is an actual table satisfying the no-crossing property. -/
def rootCutHalfEdgeTable (x : E × Bool → V) (root : V) :
    CutHalfEdgeTable (rootHalfEdgeVertices x root) (rootHalfEdgeEdges x root) :=
  ⟨x,rootHalfEdge_side_mem_iff x root⟩

theorem rootCutHalfEdgeTable_inside_connected (x : E × Bool → V) (root : V) :
    (labelledHalfEdgeSupport (cutTableInside (rootCutHalfEdgeTable x root))).Connected := by
  rw [cutTableInside_support_eq_induce]
  exact ((labelledHalfEdgeSupport x).connectedComponentMk root).connected_toSimpleGraph

theorem rootCutHalfEdgeTable_reassemble (x : E × Bool → V) (root : V) :
    assembleCutHalfEdges (cutTableInside (rootCutHalfEdgeTable x root),
      cutTableOutside (rootCutHalfEdgeTable x root)) = x := by
  exact congrArg Subtype.val
    ((cutHalfEdgeTableEquivPair (rootHalfEdgeVertices x root)
      (rootHalfEdgeEdges x root)).left_inv (rootCutHalfEdgeTable x root))

theorem rootHalfEdgeVertices_of_connected_cut {A : Set V} {B : Set E}
    (x : CutHalfEdgeTable A B) (root : V) (hr : root ∈ A)
    (hc : (labelledHalfEdgeSupport (cutTableInside x)).Connected) :
    rootHalfEdgeVertices x.val root = A := by
  ext v
  rw [mem_rootHalfEdgeVertices_iff, cutTable_reachable_iff_mem x root hr hc]

theorem rootHalfEdgeEdges_of_connected_cut {A : Set V} {B : Set E}
    (x : CutHalfEdgeTable A B) (root : V) (hr : root ∈ A)
    (hc : (labelledHalfEdgeSupport (cutTableInside x)).Connected) :
    rootHalfEdgeEdges x.val root = B := by
  ext e
  change x.val (e,false) ∈ rootHalfEdgeVertices x.val root ↔ e ∈ B
  rw [rootHalfEdgeVertices_of_connected_cut x root hr hc]
  exact x.property e false

theorem uniform_halfEdge_degree_card [Fintype V] [Fintype E]
    (x : E × Bool → V) (d : ℕ)
    (hx : ∀ v, Nat.card {i : E × Bool // x i = v} = d) :
    d * Fintype.card V = 2 * Fintype.card E := by
  have he := Nat.card_congr (Equiv.sigmaFiberEquiv x)
  rw [Nat.card_sigma] at he
  simp_rw [hx] at he
  simpa [Nat.card_eq_fintype_card, mul_comm] using he

/-- The actual cubic root component has an even nonzero number of vertices
and three times its half-order many edge labels. -/
theorem cubic_root_component_cardinalities {ell : ℕ}
    (x : UniformHalfEdgeAssignment (CubicHalfEdgeSlot ell) (Fin (2 * ell)) 3)
    (root : Fin (2 * ell)) :
    ∃ j : ℕ, 0 < j ∧ j ≤ ell ∧
      Nat.card (rootHalfEdgeVertices x.val root) = 2 * j ∧
      Nat.card (rootHalfEdgeEdges x.val root) = 3 * j := by
  let A := rootHalfEdgeVertices x.val root
  let B := rootHalfEdgeEdges x.val root
  let t := rootCutHalfEdgeTable x.val root
  have hi : ∀ v : A,
      Nat.card {i : B × Bool // cutTableInside t i = v} = 3 := by
    intro v
    rw [cutTableInside_degree]
    exact x.property v.val
  have hc := uniform_halfEdge_degree_card (cutTableInside t) 3 hi
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hc
  change 3 * Nat.card A = 2 * Nat.card B at hc
  have hpos : 0 < Nat.card A := by
    letI : Nonempty A := ⟨⟨root,root_mem_rootHalfEdgeVertices x.val root⟩⟩
    exact Nat.card_pos
  have hle : Nat.card A ≤ 2 * ell := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      (Finite.card_subtype_le (fun v ↦ v ∈ A))
  change ∃ j : ℕ, 0 < j ∧ j ≤ ell ∧ Nat.card A = 2 * j ∧ Nat.card B = 3 * j
  refine ⟨Nat.card A / 2, ?_⟩
  omega

end PerronWright.GraphCore
