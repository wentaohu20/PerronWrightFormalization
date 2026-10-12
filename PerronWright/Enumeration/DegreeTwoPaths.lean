import PerronWright.Enumeration.CoreBranching
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- In a minimum-degree-two graph of strictly positive excess,
the set of degree-at-least-three branch vertices is nonempty. -/
theorem branchingVertices_nonempty_of_positive_surplus
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell) :
    (branchingVertices G).Nonempty := by
  by_contra h
  have hzero : branchingVertices G = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hsum := branchingVertices_degree_excess_eq_two_surplus G hmin hs
  rw [hzero] at hsum
  simp at hsum
  omega

open scoped Classical in
/-- If every vertex of a two-core subset has *full-graph* degree two,
then no edge can leave that subset. -/
theorem isTwoCore_closed_of_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : Set V} (hs : IsTwoCore G s)
    (hdeg : ∀ v ∈ s, G.degree v = 2) :
    ∀ v ∈ s, ∀ w, G.Adj v w → w ∈ s := by
  intro v hv w hvw
  obtain ⟨a, ha, b, hb, hab, hva, hvb⟩ := hs v hv
  have hpair : ({a, b} : Finset V) = G.neighborFinset v := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      have hcases : x = a ∨ x = b := by simpa using hx
      rcases hcases with hxa | hxb
      · rw [hxa]
        exact (G.mem_neighborFinset v a).mpr hva
      · rw [hxb]
        exact (G.mem_neighborFinset v b).mpr hvb
    · rw [G.card_neighborFinset_eq_degree, hdeg v hv]
      simp [Finset.card_pair hab]
  have hw : w ∈ ({a, b} : Finset V) := by
    rw [hpair]
    exact (G.mem_neighborFinset v w).mpr hvw
  have hcases : w = a ∨ w = b := by simpa using hw
  rcases hcases with rfl | rfl
  · exact ha
  · exact hb

open scoped Classical in
/-- In a connected graph, a nonempty vertex set closed under adjacency
is the entire vertex set. -/
theorem closed_nonempty_eq_univ_of_connected
    {V : Type*} (G : SimpleGraph V) (hconn : G.Connected)
    {s : Set V} (hnonempty : s.Nonempty)
    (hclosed : ∀ v ∈ s, ∀ w, G.Adj v w → w ∈ s) :
    s = Set.univ := by
  obtain ⟨x, hx⟩ := hnonempty
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨p⟩ := hconn x y
  have walk_closed {a b : V} (q : G.Walk a b) (ha : a ∈ s) : b ∈ s := by
    induction q with
    | nil => exact ha
    | cons hadj tail ih => exact ih (hclosed _ ha _ hadj)
  exact walk_closed p hx

open scoped Classical in
/-- A connected finite graph with positive excess cannot contain a
cycle wholly inside its degree-two vertices.  Thus the induced
degree-two subgraph is a forest, the first structural step toward
organizing its connected components as subdivided kernel edges. -/
theorem degreeTwo_induced_isAcyclic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell) :
    (G.induce {v | G.degree v = 2}).IsAcyclic := by
  intro v c hc
  let D : Set V := {v | G.degree v = 2}
  let n := c.length
  have hn : 3 ≤ n := hc.three_le_length
  have hcopy : SimpleGraph.IsContained (SimpleGraph.cycleGraph n) (G.induce D) :=
    (SimpleGraph.cycleGraph_isContained_iff hn).mpr ⟨v, c, hc, rfl⟩
  obtain ⟨f⟩ := hcopy
  let F : SimpleGraph.Copy (SimpleGraph.cycleGraph n) G :=
    (SimpleGraph.Copy.induce G D).comp f
  have htwo : IsTwoCore G (Set.range F) :=
    isTwoCore_copy_range G (SimpleGraph.cycleGraph n) F
      (cycleGraph_isTwoCore n hn)
  have hdeg : ∀ x ∈ Set.range F, G.degree x = 2 := by
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact (f i).property
  have hclosed := isTwoCore_closed_of_degree_two G htwo hdeg
  have hnonempty : (Set.range F).Nonempty := by
    exact ⟨F ⟨0, by omega⟩, ⟨⟨0, by omega⟩, rfl⟩⟩
  have hfull : Set.range F = Set.univ :=
    closed_nonempty_eq_univ_of_connected G hconn hnonempty hclosed
  obtain ⟨b, hb⟩ := branchingVertices_nonempty_of_positive_surplus G hmin hell hs
  have hbdegree : 3 ≤ G.degree b := by
    simpa only [branchingVertices, Finset.mem_filter,
      Finset.mem_univ, true_and] using hb
  have hbmem : b ∈ Set.range F := by rw [hfull]; trivial
  have hbdeg := hdeg b hbmem
  omega

open scoped Classical in
/-- Every vertex in the induced degree-two subgraph has induced
degree at most two. -/
theorem degreeTwo_induced_degree_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : {v : V | G.degree v = 2}) :
    (G.induce {v | G.degree v = 2}).degree x ≤ 2 := by
  have h := (SimpleGraph.Copy.induce G {v | G.degree v = 2}).degree_le x
  change (G.induce {v | G.degree v = 2}).degree x ≤ G.degree x.val at h
  rw [x.property] at h
  exact h

/-- The total degree deficit inside the induced degree-two subgraph is
exactly the number of incidences toward branch vertices.  The displayed
identity is the finite handshaking formula in a form that does not yet
require choosing path endpoints or orientations. -/
theorem degreeTwo_induced_deficit_identity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ x : {v : V | G.degree v = 2},
        (2 - (G.induce {v | G.degree v = 2}).degree x)) +
      2 * (G.induce {v | G.degree v = 2}).edgeFinset.card =
      2 * Fintype.card {v : V | G.degree v = 2} := by
  let D : Set V := {v | G.degree v = 2}
  let H := G.induce D
  have hsum : (∑ x : D, (2 - H.degree x)) +
      (∑ x : D, H.degree x) = ∑ _x : D, (2 : ℕ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    have hx := degreeTwo_induced_degree_le_two G x
    change H.degree x ≤ 2 at hx
    omega
  change (∑ x : D, (2 - H.degree x)) + 2 * H.edgeFinset.card =
    2 * Fintype.card D
  rw [← H.sum_degrees_eq_twice_card_edges]
  rw [hsum]
  simp [Finset.sum_const, mul_comm]

open scoped Classical in
/-- Boundary incidences are directed from a degree-two vertex to one
of its neighbors outside the degree-two set.  These are the endpoint
stubs that a path-suppression operation must pair. -/
def degreeTwoBoundaryIncidences
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ∑ x : {v : V | G.degree v = 2},
    ((G.neighborFinset x.val).filter (fun y => G.degree y ≠ 2)).card

open scoped Classical in
theorem degreeTwo_external_neighbors_eq_deficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : {v : V | G.degree v = 2}) :
    ((G.neighborFinset x.val).filter (fun y => G.degree y ≠ 2)).card =
      2 - (G.induce {v | G.degree v = 2}).degree x := by
  let D : Set V := {v | G.degree v = 2}
  let H := G.induce D
  have hin : H.degree x =
      ((G.neighborFinset x.val).filter (fun y => G.degree y = 2)).card := by
    calc
      H.degree x = (H.neighborFinset x).card :=
        (H.card_neighborFinset_eq_degree x).symm
      _ = ((H.neighborFinset x).map (.subtype (· ∈ D))).card :=
        (Finset.card_map _).symm
      _ = (G.neighborFinset x.val ∩ D.toFinset).card := by
        exact congrArg Finset.card (G.map_neighborFinset_induce x)
      _ = ((G.neighborFinset x.val).filter (fun y => G.degree y = 2)).card := by
        congr 1
        ext y
        simp [D]
  have hpartition := (G.neighborFinset x.val).card_filter_add_card_filter_not
    (fun y => G.degree y = 2)
  have htotal :
      ((G.neighborFinset x.val).filter (fun y => G.degree y = 2)).card +
        ((G.neighborFinset x.val).filter (fun y => G.degree y ≠ 2)).card = 2 := by
    calc
      _ = (G.neighborFinset x.val).card := hpartition
      _ = G.degree x.val := G.card_neighborFinset_eq_degree x.val
      _ = 2 := x.property
  change ((G.neighborFinset x.val).filter (fun y => G.degree y ≠ 2)).card =
    2 - H.degree x
  rw [hin]
  omega

open scoped Classical in
/-- The degree deficits in the induced degree-two forest count actual
boundary incidences, without an abstract or assumed endpoint map. -/
theorem degreeTwoBoundaryIncidences_eq_deficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    degreeTwoBoundaryIncidences G =
      ∑ x : {v : V | G.degree v = 2},
        (2 - (G.induce {v | G.degree v = 2}).degree x) := by
  unfold degreeTwoBoundaryIncidences
  apply Finset.sum_congr rfl
  intro x _
  exact degreeTwo_external_neighbors_eq_deficit G x

open scoped Classical in
/-- Exact boundary/internal-edge accounting for the degree-two
subgraph.  In the connected positive-excess case, the preceding
acyclicity theorem says this subgraph is a forest of path components. -/
theorem degreeTwoBoundaryIncidences_add_twice_internalEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    degreeTwoBoundaryIncidences G +
      2 * (G.induce {v | G.degree v = 2}).edgeFinset.card =
      2 * Fintype.card {v : V | G.degree v = 2} := by
  rw [degreeTwoBoundaryIncidences_eq_deficit]
  exact degreeTwo_induced_deficit_identity G

/-- The actual number of boundary stubs is twice the Euler deficit of
the induced degree-two graph.  In the connected positive-surplus case
that graph is a forest, so this deficit is the number of path
components to be represented by subdivided kernel edges. -/
theorem degreeTwoBoundaryIncidences_eq_twice_eulerDeficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    degreeTwoBoundaryIncidences G =
      2 * (Fintype.card {v : V | G.degree v = 2} -
        (G.induce {v | G.degree v = 2}).edgeFinset.card) := by
  have h := degreeTwoBoundaryIncidences_add_twice_internalEdges G
  omega

/-- In a finite path-shaped tree (including the singleton), exactly
two endpoint stubs remain after accounting for internal edges. -/
theorem isTree_degreeDeficit_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (htree : H.IsTree) (hdeg : ∀ v, H.degree v ≤ 2) :
    (∑ v : V, (2 - H.degree v)) = 2 := by
  have hsum : (∑ v : V, (2 - H.degree v)) +
      (∑ v : V, H.degree v) = ∑ _v : V, (2 : ℕ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    have hv := hdeg v
    omega
  rw [H.sum_degrees_eq_twice_card_edges] at hsum
  have hedges := htree.card_edgeFinset
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  norm_num at hsum
  omega

/-- Passing to a connected component does not discard any neighbor
of one of its vertices. -/
theorem connectedComponent_degree_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (C : H.ConnectedComponent) (x : C) :
    C.toSimpleGraph.degree x = H.degree x.val := by
  rw [← C.toSimpleGraph.card_neighborFinset_eq_degree,
    ← H.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    apply (H.mem_neighborFinset x.val y.val).mpr
    exact (C.toSimpleGraph.mem_neighborFinset x y).mp hy
  · intro y₁ _ y₂ _ h
    exact Subtype.ext h
  · intro y hy
    have hxy : H.Adj x.val y :=
      (H.mem_neighborFinset x.val y).mp hy
    have hyC : y ∈ C := C.mem_supp_of_adj_mem_supp x.property hxy
    refine ⟨⟨y, hyC⟩, ?_, rfl⟩
    exact (C.toSimpleGraph.mem_neighborFinset x ⟨y, hyC⟩).mpr hxy

/-- Every connected component of the actual induced degree-two forest
has precisely two stubs.  This is the componentwise numerical content
of pairing boundary incidences into subdivided kernel edges. -/
theorem degreeTwo_component_deficit_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (C : (G.induce {v | G.degree v = 2}).ConnectedComponent) :
    (∑ x : C, (2 - C.toSimpleGraph.degree x)) = 2 := by
  let H := G.induce {v | G.degree v = 2}
  have htree : C.toSimpleGraph.IsTree :=
    ⟨C.connected_toSimpleGraph, hacyc.induce C.supp⟩
  have hdeg : ∀ x : C, C.toSimpleGraph.degree x ≤ 2 := by
    intro x
    let f : SimpleGraph.Copy C.toSimpleGraph H :=
      ⟨C.toSimpleGraph_hom, Subtype.val_injective⟩
    have hle : C.toSimpleGraph.degree x ≤ H.degree x.val := by
      exact f.degree_le x
    have hx := degreeTwo_induced_degree_le_two G x.val
    exact hle.trans hx
  exact isTree_degreeDeficit_eq_two C.toSimpleGraph htree hdeg

/-- Each connected component of the degree-two forest has exactly
two *actual* incidences leaving it toward branch vertices.  This
remains true for a singleton component, whose one vertex contributes
both stubs. -/
theorem degreeTwo_component_boundary_stubs_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (C : (G.induce {v | G.degree v = 2}).ConnectedComponent) :
    (∑ x : C,
      ((G.neighborFinset x.val.val).filter
        (fun y => G.degree y ≠ 2)).card) = 2 := by
  calc
    _ = ∑ x : C, (2 - C.toSimpleGraph.degree x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [degreeTwo_external_neighbors_eq_deficit G x.val,
        connectedComponent_degree_eq (G.induce {v | G.degree v = 2}) C x]
    _ = 2 := degreeTwo_component_deficit_eq_two G hacyc C

open scoped Classical in
/-- After exact leaf pruning, the degree-two vertices of a connected
graph with positive kernel excess form an acyclic graph of maximum
degree two.  Thus no degree-two-only cycle can survive to the kernel;
the remaining components are precisely the candidates for subdivided
kernel edges. -/
theorem pruneAll_degreeTwo_forest_maxDegree_two
    {k : ℕ} (G : SimpleGraph (Fin k)) (hconn : G.Connected)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + (ell + 1)) :
    ((LeafPruning.pruneAll k G).terminalGraph.induce
      {v | (LeafPruning.pruneAll k G).terminalGraph.degree v = 2}).IsAcyclic ∧
    (∀ x : {v | (LeafPruning.pruneAll k G).terminalGraph.degree v = 2},
      ((LeafPruning.pruneAll k G).terminalGraph.induce
        {v | (LeafPruning.pruneAll k G).terminalGraph.degree v = 2}).degree x ≤ 2) := by
  let p := LeafPruning.pruneAll k G
  have hconn' : p.terminalGraph.Connected := p.terminal_connected hconn
  have hcore : (greatestTwoCore G).Nonempty :=
    greatestTwoCore_nonempty_of_positive_surplus G hconn (by omega) hs
  have hterm : (greatestTwoCore p.terminalGraph).Nonempty :=
    p.terminal_core_nonempty hcore
  have hfull : greatestTwoCore p.terminalGraph = Set.univ :=
    greatestTwoCore_eq_univ_of_connected_noLeaf p.terminalGraph
      hconn' hterm p.terminal_noLeaf
  have hmin := min_degree_two_of_greatestTwoCore_eq_univ p.terminalGraph hfull
  have hsurplus := p.terminal_surplus hs
  have hs' : p.terminalGraph.edgeFinset.card =
      Fintype.card (Fin p.terminalCount) + ell := by
    apply Nat.add_right_cancel (m := 1)
    simpa only [Nat.add_assoc] using hsurplus
  change (p.terminalGraph.induce {v | p.terminalGraph.degree v = 2}).IsAcyclic ∧
    (∀ x : {v | p.terminalGraph.degree v = 2},
      (p.terminalGraph.induce {v | p.terminalGraph.degree v = 2}).degree x ≤ 2)
  exact ⟨degreeTwo_induced_isAcyclic p.terminalGraph hconn' hmin hell hs',
    degreeTwo_induced_degree_le_two p.terminalGraph⟩

#print axioms PerronWright.GraphCore.branchingVertices_nonempty_of_positive_surplus
#print axioms PerronWright.GraphCore.isTwoCore_closed_of_degree_two
#print axioms PerronWright.GraphCore.degreeTwo_induced_isAcyclic
#print axioms PerronWright.GraphCore.degreeTwo_induced_deficit_identity
#print axioms PerronWright.GraphCore.degreeTwoBoundaryIncidences_add_twice_internalEdges
#print axioms PerronWright.GraphCore.degreeTwoBoundaryIncidences_eq_twice_eulerDeficit
#print axioms PerronWright.GraphCore.degreeTwo_component_boundary_stubs_eq_two
#print axioms PerronWright.GraphCore.pruneAll_degreeTwo_forest_maxDegree_two

end PerronWright.GraphCore

