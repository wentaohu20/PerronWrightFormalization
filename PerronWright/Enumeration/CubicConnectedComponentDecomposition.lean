import PerronWright.Enumeration.CubicConnectedComponentRoot

/-!
# Actual rooted cubic component decomposition

The inside component is connected and contains the distinguished vertex;
the complement is an arbitrary cubic table.  This module proves the finite
split/assembly equivalence from the actual support graph.  There is no
component-factorization premise.
-/

noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

namespace PerronWright.GraphCore

variable {V E : Type*} [Fintype E]

theorem orderedPresentationHalfEdges_support {v e : ℕ}
    (H : PerronWright.FiniteMultiGraph v e) (p : OrderedMultiGraphPresentation H) :
    labelledHalfEdgeSupport (orderedPresentationHalfEdges p) =
      finiteMultiGraphSupportGraph H := by
  change finiteMultiGraphSupportGraph (halfEdgeMultiGraph (orderedPresentationHalfEdges p)) = _
  rw [halfEdgeMultiGraph_orderedPresentation H p]

/-- A literal root component and its complement, retaining the original
vertex and edge subsets as labels. -/
structure CubicRootSplit (root : V) where
  vertices : Set V
  edges : Set E
  inside : UniformHalfEdgeAssignment (edges × Bool) vertices 3
  outside : UniformHalfEdgeAssignment ((edgesᶜ : Set E) × Bool) (verticesᶜ : Set V) 3
  root_mem : root ∈ vertices
  connected : (labelledHalfEdgeSupport inside.val).Connected

def CubicRootSplit.cutTable {root : V} (D : CubicRootSplit (E := E) root) :
    CutHalfEdgeTable D.vertices D.edges :=
  assembledCutTable (D.inside.val,D.outside.val)

theorem CubicRootSplit.cutTable_inside {root : V} (D : CubicRootSplit (E := E) root) :
    cutTableInside D.cutTable = D.inside.val := by
  exact congrArg Prod.fst ((cutHalfEdgeTableEquivPair D.vertices D.edges).right_inv
    (D.inside.val,D.outside.val))

theorem CubicRootSplit.cutTable_outside {root : V} (D : CubicRootSplit (E := E) root) :
    cutTableOutside D.cutTable = D.outside.val := by
  exact congrArg Prod.snd ((cutHalfEdgeTableEquivPair D.vertices D.edges).right_inv
    (D.inside.val,D.outside.val))

def assembleCubicRootSplit {root : V} (D : CubicRootSplit (E := E) root) :
    UniformHalfEdgeAssignment (E × Bool) V 3 := by
  refine ⟨D.cutTable.val, (cutTable_uniform_degree_iff D.cutTable 3).2 ?_⟩
  rw [D.cutTable_inside, D.cutTable_outside]
  exact ⟨D.inside.property,D.outside.property⟩

theorem CubicRootSplit.vertices_recovered {root : V}
    (D : CubicRootSplit (E := E) root) :
    rootHalfEdgeVertices (assembleCubicRootSplit D).val root = D.vertices := by
  apply rootHalfEdgeVertices_of_connected_cut D.cutTable root D.root_mem
  rw [D.cutTable_inside]
  exact D.connected

theorem CubicRootSplit.edges_recovered {root : V}
    (D : CubicRootSplit (E := E) root) :
    rootHalfEdgeEdges (assembleCubicRootSplit D).val root = D.edges := by
  apply rootHalfEdgeEdges_of_connected_cut D.cutTable root D.root_mem
  rw [D.cutTable_inside]
  exact D.connected

/-- Extract the actual connected component containing the root. -/
def splitCubicRootComponent (root : V)
    (x : UniformHalfEdgeAssignment (E × Bool) V 3) : CubicRootSplit (E := E) root where
  vertices := rootHalfEdgeVertices x.val root
  edges := rootHalfEdgeEdges x.val root
  inside := ⟨cutTableInside (rootCutHalfEdgeTable x.val root), fun v ↦ by
    rw [cutTableInside_degree]
    exact x.property v.val⟩
  outside := ⟨cutTableOutside (rootCutHalfEdgeTable x.val root), fun v ↦ by
    rw [cutTableOutside_degree]
    exact x.property v.val⟩
  root_mem := root_mem_rootHalfEdgeVertices x.val root
  connected := rootCutHalfEdgeTable_inside_connected x.val root

theorem assemble_splitCubicRootComponent (root : V)
    (x : UniformHalfEdgeAssignment (E × Bool) V 3) :
    assembleCubicRootSplit (splitCubicRootComponent root x) = x := by
  apply Subtype.ext
  exact rootCutHalfEdgeTable_reassemble x.val root

omit [Fintype E] in
theorem assembleCutHalfEdges_injective {A : Set V} {B : Set E} :
    Function.Injective (assembleCutHalfEdges : CutHalfEdgePair A B → E × Bool → V) := by
  intro p q h
  exact (cutHalfEdgeTableEquivPair A B).symm.injective (Subtype.ext h)

theorem assembleCubicRootSplit_injective (root : V) :
    Function.Injective (assembleCubicRootSplit : CubicRootSplit (E := E) root →
      UniformHalfEdgeAssignment (E × Bool) V 3) := by
  intro D D' h
  have hx := congrArg Subtype.val h
  have hv : D.vertices = D'.vertices := by
    rw [← D.vertices_recovered, ← D'.vertices_recovered, h]
  have he : D.edges = D'.edges := by
    rw [← D.edges_recovered, ← D'.edges_recovered, h]
  cases D with
  | mk A B inside outside hr hc =>
    cases D' with
    | mk A' B' inside' outside' hr' hc' =>
      dsimp only at hv he
      cases hv
      cases he
      have hp : (inside.val,outside.val) = (inside'.val,outside'.val) :=
        assembleCutHalfEdges_injective hx
      have hi : inside = inside' := Subtype.ext (congrArg Prod.fst hp)
      have ho : outside = outside' := Subtype.ext (congrArg Prod.snd hp)
      cases hi
      cases ho
      rfl

/-- Actual finite decomposition into the root connected component and an
arbitrary cubic remainder. -/
def cubicHalfEdgeRootDecompositionEquiv (root : V) :
    UniformHalfEdgeAssignment (E × Bool) V 3 ≃ CubicRootSplit (E := E) root :=
  (Equiv.ofBijective assembleCubicRootSplit
    ⟨assembleCubicRootSplit_injective root,
      fun x ↦ ⟨splitCubicRootComponent root x,assemble_splitCubicRootComponent root x⟩⟩).symm

@[instance_reducible] noncomputable def cubicRootSplitFintype [Fintype V] (root : V) :
    Fintype (CubicRootSplit (E := E) root) :=
  Fintype.ofEquiv (UniformHalfEdgeAssignment (E × Bool) V 3)
    (cubicHalfEdgeRootDecompositionEquiv root)

theorem card_cubicHalfEdgeRootDecomposition (root : V) :
    Nat.card (UniformHalfEdgeAssignment (E × Bool) V 3) =
      Nat.card (CubicRootSplit (E := E) root) :=
  Nat.card_congr (cubicHalfEdgeRootDecompositionEquiv root)

/-- The endpoint tables appearing in the unchanged compensation formula
have this same genuine root decomposition. -/
def cubicOrderedRootDecompositionEquiv (ell : ℕ) (root : Fin (2 * ell)) :
    CubicOrderedPresentation ell ≃ CubicRootSplit (E := Fin (3 * ell)) root :=
  (cubicOrderedPresentationEquivHalfEdges ell).trans
    (cubicHalfEdgeRootDecompositionEquiv root)

theorem CubicRootSplit.cardinalities {ell : ℕ} {root : Fin (2 * ell)}
    (D : CubicRootSplit (E := Fin (3 * ell)) root) :
    ∃ j : ℕ, 0 < j ∧ j ≤ ell ∧ Nat.card D.vertices = 2 * j ∧ Nat.card D.edges = 3 * j := by
  have h := cubic_root_component_cardinalities (assembleCubicRootSplit D) root
  rw [D.vertices_recovered,D.edges_recovered] at h
  exact h

end PerronWright.GraphCore
