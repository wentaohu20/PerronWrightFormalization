import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Connected components as isolated vertex blocks

This identifies the actual connected components with nonempty isolated
connected vertex sets.  It is the combinatorial step behind summing
component indicators over candidate blocks.
-/

open scoped Classical

noncomputable section

namespace PerronWright.ComponentBlocks

variable {V : Type*} (G : SimpleGraph V)

/-- A vertex block has no edge to its complement. -/
def Isolated (B : Set V) : Prop :=
  ∀ u ∈ B, ∀ v, G.Adj u v → v ∈ B

theorem Isolated.walk_mem {B : Set V} (hB : Isolated G B)
    {u v : V} (p : G.Walk u v) (hu : u ∈ B) : v ∈ B := by
  revert hu
  induction p with
  | nil => exact id
  | @cons u v w huv p ih =>
      intro hu
      exact ih (hB u hu v huv)

theorem Isolated.reachable_mem {B : Set V} (hB : Isolated G B)
    {u v : V} (hu : u ∈ B) (huv : G.Reachable u v) : v ∈ B :=
  hB.walk_mem G huv.some hu

theorem component_isolated (C : G.ConnectedComponent) : Isolated G C.supp := by
  intro u hu v huv
  exact C.mem_supp_of_adj_mem_supp hu huv

/-- Connectivity and isolation characterize the support of one component. -/
theorem connected_isolated_iff_component (B : Set V) :
    (G.induce B).Connected ∧ Isolated G B ↔
      ∃ C : G.ConnectedComponent, C.supp = B := by
  constructor
  · rintro ⟨hconn, hiso⟩
    obtain ⟨⟨b, hb⟩⟩ := hconn.nonempty
    refine ⟨G.connectedComponentMk b, ?_⟩
    ext v
    constructor
    · intro hv
      exact hiso.reachable_mem G hb
        ((G.connectedComponentMk b).reachable_of_mem_supp
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem hv)
    · intro hv
      exact SimpleGraph.ConnectedComponent.sound
        ((hconn.preconnected ⟨v, hv⟩ ⟨b, hb⟩).map
          (SimpleGraph.Embedding.induce B).toHom)
  · rintro ⟨C, rfl⟩
    exact ⟨C.connected_toSimpleGraph, component_isolated G C⟩

variable [Fintype V]

/-- Finite candidate blocks that are actual isolated connected components. -/
def Block : Type _ :=
  {B : Finset V // (G.induce (B : Set V)).Connected ∧ Isolated G (B : Set V)}

/-- The support of a component, viewed as a finite candidate block. -/
def blockOfComponent (C : G.ConnectedComponent) : Block G :=
  ⟨C.supp.toFinset, by
    exact (connected_isolated_iff_component G (C.supp.toFinset : Set V)).mpr
      ⟨C, (Set.coe_toFinset C.supp).symm⟩⟩

/-- Recover the unique component belonging to an isolated connected block. -/
def componentOfBlock (B : Block G) : G.ConnectedComponent :=
  Classical.choose ((connected_isolated_iff_component G (B.val : Set V)).mp B.property)

omit [Fintype V] in
theorem componentOfBlock_supp (B : Block G) :
    (componentOfBlock G B).supp = (B.val : Set V) :=
  Classical.choose_spec
    ((connected_isolated_iff_component G (B.val : Set V)).mp B.property)

/-- Exact correspondence between genuine components and candidate blocks. -/
def componentBlockEquiv : G.ConnectedComponent ≃ Block G where
  toFun := blockOfComponent G
  invFun := componentOfBlock G
  left_inv C := by
    apply SimpleGraph.ConnectedComponent.supp_injective
    simpa only [blockOfComponent, Set.coe_toFinset] using
      componentOfBlock_supp G (blockOfComponent G C)
  right_inv B := by
    apply Subtype.ext
    apply Finset.coe_injective
    simpa only [blockOfComponent, Set.coe_toFinset] using componentOfBlock_supp G B

end PerronWright.ComponentBlocks
