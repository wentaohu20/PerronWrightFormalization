import PerronWright.Enumeration.ConnectedWeight
import PerronWright.Enumeration.KernelShapes
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
Structural starting point for the exact core--kernel decomposition.  Deleting
a degree-one vertex of a connected finite graph retains connectivity and the
exact edge-minus-vertex surplus, not merely an asymptotic estimate.
-/

noncomputable section

namespace PerronWright.GraphCore

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Pruning a leaf removes precisely one edge. -/
theorem leaf_prune_edge_count {v : V} (hv : G.degree v = 1) :
    (G.induce ({v}ᶜ : Set V)).edgeFinset.card + 1 = G.edgeFinset.card := by
  rw [G.card_edgeFinset_induce_compl_singleton,
    G.card_edgeFinset_deleteIncidenceSet, hv]
  have hle : 1 ≤ G.edgeFinset.card := by
    calc
      1 = G.degree v := hv.symm
      _ ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset v
  omega

/-- Pruning a vertex removes precisely one vertex. -/
theorem prune_vertex_count (v : V) :
    Fintype.card ({v}ᶜ : Set V) + 1 = Fintype.card V := by
  have hcard : Fintype.card ({v} : Set V) = 1 := by
    exact Fintype.card_subtype_eq v
  rw [Fintype.card_compl_set]
  rw [hcard]
  have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

/-- A genuine exact graph invariant used in connected-graph core pruning:
the nonnegative surplus `edges + 1 - vertices` is preserved at each leaf
deletion, with the induced graph retaining connectivity. -/
theorem leaf_prune_preserves_connected_surplus {v : V}
    (hc : G.Connected) (hv : G.degree v = 1) (ell : ℕ)
    (hsurplus : G.edgeFinset.card + 1 = Fintype.card V + ell) :
    (G.induce ({v}ᶜ : Set V)).Connected ∧
    (G.induce ({v}ᶜ : Set V)).edgeFinset.card + 1 =
      Fintype.card ({v}ᶜ : Set V) + ell := by
  constructor
  · exact hc.induce_compl_singleton_of_degree_eq_one hv
  · have he := leaf_prune_edge_count G hv
    have hv' := prune_vertex_count v
    omega

/-- A vertex set has internal minimum degree at least two, stated without
choosing any auxiliary finite enumeration of its vertices. -/
def IsTwoCore (s : Set V) : Prop :=
  ∀ v ∈ s, ∃ w ∈ s, ∃ z ∈ s,
    w ≠ z ∧ G.Adj v w ∧ G.Adj v z

/-- The union of *all* degree-at-least-two induced vertex sets.  This
existential definition does not depend on a leaf-pruning order. -/
def greatestTwoCore : Set V :=
  {v | ∃ s : Set V, IsTwoCore G s ∧ v ∈ s}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem isTwoCore_greatest : IsTwoCore G (greatestTwoCore G) := by
  intro v hv
  obtain ⟨s, hs, hvs⟩ := hv
  obtain ⟨w, hws, z, hzs, hwz, hvw, hvz⟩ := hs v hvs
  exact ⟨w, ⟨s, hs, hws⟩, z, ⟨s, hs, hzs⟩, hwz, hvw, hvz⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem isTwoCore_subset_greatest {s : Set V} (hs : IsTwoCore G s) :
    s ⊆ greatestTwoCore G := by
  intro v hv
  exact ⟨s, hs, hv⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Characterization of the unique largest induced 2-core. -/
theorem is_greatestTwoCore_iff {s : Set V} :
    s = greatestTwoCore G ↔
      IsTwoCore G s ∧ ∀ t : Set V, IsTwoCore G t → t ⊆ s := by
  constructor
  · rintro rfl
    exact ⟨isTwoCore_greatest G, fun _ ht => isTwoCore_subset_greatest G ht⟩
  · rintro ⟨hs, hmax⟩
    exact Set.Subset.antisymm (isTwoCore_subset_greatest G hs)
      (hmax _ (isTwoCore_greatest G))

omit [DecidableEq V] in
/-- A degree-one vertex cannot occur in the unique maximal 2-core.
This does not by itself prove invariance of the full core under pruning. -/
theorem leaf_not_mem_greatestTwoCore {v : V} (hv : G.degree v = 1) :
    v ∉ greatestTwoCore G := by
  intro hmem
  obtain ⟨w, -, z, -, hwz, hvw, hvz⟩ := isTwoCore_greatest G v hmem
  obtain ⟨u, hu, hunique⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hv
  have hwu : w = u := hunique w hvw
  have hzu : z = u := hunique z hvz
  exact hwz (hwu.trans hzu.symm)

/-- The exact fixed-size and fixed-surplus predicate used by
`CompactBJRModel.connectedWeight` is stable under deleting a leaf.  The
remaining graph is on its literal surviving label subtype; no relabelling
or asymptotic equivalence is hidden in this statement. -/
theorem paper_surplus_leaf_prune {k r : ℕ} (H : SimpleGraph (Fin k))
    [DecidableRel H.Adj]
    {v : Fin k} (hc : H.Connected) (hv : H.degree v = 1)
    (hsize : H.edgeFinset.card = k + r - 1) :
    (H.induce ({v}ᶜ : Set (Fin k))).Connected ∧
    (H.induce ({v}ᶜ : Set (Fin k))).edgeFinset.card =
      Fintype.card ({v}ᶜ : Set (Fin k)) + r - 1 := by
  classical
  have hk : 1 ≤ k := by
    have hpos : 0 < Fintype.card (Fin k) := Fintype.card_pos_iff.mpr ⟨v⟩
    simp only [Fintype.card_fin] at hpos
    omega
  have hs : H.edgeFinset.card + 1 = Fintype.card (Fin k) + r := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨hconn', hsurplus'⟩ := leaf_prune_preserves_connected_surplus H hc hv r hs
  constructor
  · exact hconn'
  · omega

end PerronWright.GraphCore
