import PerronWright.Enumeration.TreeRootComponents
import Mathlib.Order.Partition.Finpartition

/-!
# Finite blocks after deleting a tree root

The root neighbors index exactly the connected blocks left by deleting the
root. For a finite vertex type, these blocks form a `Finpartition`, and each
block's induced graph is again a tree.
-/

open scoped Classical

namespace PerronWright

noncomputable def treeRootNeighborEquivComponents
    {V : Type*} (H : SimpleGraph V) (hT : H.IsTree) (r : V) :
    H.neighborSet r ≃ (H.induce {r}ᶜ).ConnectedComponent := by
  let f : H.neighborSet r → (H.induce {r}ᶜ).ConnectedComponent :=
    fun u => (H.induce {r}ᶜ).connectedComponentMk
      ⟨u.1, u.property.ne.symm⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    by_contra hne
    exact tree_root_neighbors_distinct_components H hT r u.1 v.1
      u.property v.property hne huv
  · intro c
    obtain ⟨u, hru, hu⟩ := tree_root_component_has_neighbor H hT r c
    exact ⟨⟨u, hru⟩, hu⟩

theorem tree_root_component_isTree
    {V : Type*} (H : SimpleGraph V) (hT : H.IsTree)
    (r : V) (c : (H.induce {r}ᶜ).ConnectedComponent) :
    c.toSimpleGraph.IsTree :=
  (hT.isAcyclic.induce {r}ᶜ).isTree_connectedComponent c

noncomputable def treeRootFinpartition
    {V : Type*} [Fintype V] (H : SimpleGraph V) (r : V) :
    Finpartition (Finset.univ : Finset ({r}ᶜ : Set V)) :=
  Finpartition.ofSetoid (H.induce {r}ᶜ).reachableSetoid

theorem treeRootFinpartition_mem_part_iff
    {V : Type*} [Fintype V] (H : SimpleGraph V) (r : V)
    (x y : ({r}ᶜ : Set V)) :
    y ∈ (treeRootFinpartition H r).part x ↔
      (H.induce {r}ᶜ).connectedComponentMk x =
        (H.induce {r}ᶜ).connectedComponentMk y := by
  rw [treeRootFinpartition, Finpartition.mem_part_ofSetoid_iff_rel]
  exact (SimpleGraph.ConnectedComponent.eq (G := H.induce {r}ᶜ)
    (v := x) (w := y)).symm

end PerronWright
