import PerronWright.Enumeration.FiniteKernelGeneral

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Multiplicity of a branch vertex in one suppressed path edge is
the number of its actual boundary stubs.  In particular a path
returning to the same branch vertex contributes two, not one. -/
theorem degreeTwoPathEndpoints_count_eq_boundaryStubs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (C : (G.induce {v | G.degree v = 2}).ConnectedComponent)
    (b : V) :
    (degreeTwoPathEndpoints G hacyc C).toMultiset.count b =
      ((componentBoundaryStubs G C).filter (fun s => s.2 = b)).card := by
  rw [degreeTwoPathEndpoints_toMultiset, Multiset.count_map]
  rw [← Finset.filter_val]
  congr 1
  ext s
  simp only [eq_comm (a := b)]

/-- For a branch endpoint, stubs of one path component ending at it
are precisely its adjacent internal vertices, counted one each. -/
theorem componentBoundaryStubs_at_branch_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (G.induce {v | G.degree v = 2}).ConnectedComponent)
    (b : V) (hb : G.degree b ≠ 2) :
    ((componentBoundaryStubs G C).filter (fun s => s.2 = b)).card =
      ∑ x : C, if G.Adj x.val.val b then (1 : ℕ) else 0 := by
  unfold componentBoundaryStubs
  rw [Finset.filter_sigma, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hadj : G.Adj x.val.val b
  · have hsingle :
        ((G.neighborFinset x.val.val).filter
          (fun y => G.degree y ≠ 2)).filter (fun y => y = b) = {b} := by
      ext y
      by_cases hy : y = b
      · subst y
        simp [G.mem_neighborFinset, hadj]
        exact hb
      · simp [G.mem_neighborFinset, hy]
    rw [hsingle]
    simp [hadj]
  · have hempty :
        ((G.neighborFinset x.val.val).filter
          (fun y => G.degree y ≠ 2)).filter (fun y => y = b) = ∅ := by
      ext y
      by_cases hy : y = b
      · subst y
        simp [G.mem_neighborFinset, hadj]
      · simp [G.mem_neighborFinset, hy]
    rw [hempty]
    simp [hadj]

set_option linter.style.haveILetI false in
/-- Summing the path-endpoint multiplicities over all degree-two
components gives exactly the number of original edges from `b`
into the degree-two set. -/
theorem sum_degreeTwoPathEndpoints_count_eq_cross_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (G.induce {v | G.degree v = 2}).ConnectedComponent]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (b : V) (hb : G.degree b ≠ 2) :
    (∑ C : (G.induce {v | G.degree v = 2}).ConnectedComponent,
      (degreeTwoPathEndpoints G hacyc C).toMultiset.count b) =
      ((G.neighborFinset b).filter (fun v => G.degree v = 2)).card := by
  let D : Set V := {v | G.degree v = 2}
  let H := G.induce D
  let Dfin : Finset V := Finset.univ.filter (fun v => G.degree v = 2)
  have hD (v : V) : v ∈ Dfin ↔ G.degree v = 2 := by simp [Dfin]
  have hsub := Finset.sum_subtype
    (F := Fintype.ofFinite D) Dfin hD
    (fun v => if G.Adj v b then (1 : ℕ) else 0)
  calc
    (∑ C : H.ConnectedComponent,
        (degreeTwoPathEndpoints G hacyc C).toMultiset.count b) =
        ∑ C : H.ConnectedComponent,
          ∑ x : C, if G.Adj x.val.val b then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      rw [degreeTwoPathEndpoints_count_eq_boundaryStubs]
      exact componentBoundaryStubs_at_branch_card G C b hb
    _ = ∑ x : D, if G.Adj x.val b then (1 : ℕ) else 0 := by
      exact sum_over_connected_components H
        (fun x => if G.Adj x.val b then (1 : ℕ) else 0)
    _ = ∑ v ∈ Dfin, if G.Adj v b then (1 : ℕ) else 0 := by
      convert hsub.symm using 1
      congr 1
      ext x
      simp
    _ = ((G.neighborFinset b).filter
          (fun v => G.degree v = 2)).card := by
      calc
        _ = (Dfin.filter (fun v => G.Adj v b)).card := by
          rw [← Finset.sum_filter]
          simp
        _ = _ := by
          congr 1
          ext v
          simp [Dfin, G.mem_neighborFinset, and_comm, G.adj_comm]

/-- Direct branch-to-branch kernel edges incident to `b` correspond
bijectively to original neighbors of `b` that are branch vertices. -/
theorem directBranchEdges_incident_card_eq_branch_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V) (hb : b ∈ branchingVertices G) :
    ((directBranchEdges G).filter (fun e => b ∈ e)).card =
      ((G.neighborFinset b).filter
        (fun v => v ∈ branchingVertices G)).card := by
  let B := branchingVertices G
  symm
  apply Finset.card_bij (fun y _ => s(b, y))
  · intro y hy
    have hadj : G.Adj b y :=
      (G.mem_neighborFinset b y).mp (Finset.mem_filter.mp hy).1
    have hyB : y ∈ B := (Finset.mem_filter.mp hy).2
    have hedge : s(b, y) ∈ G.edgeFinset := by
      exact G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hadj)
    have hall : ∀ v ∈ s(b, y), v ∈ B := by
      intro v hv
      rcases (Sym2.mem_iff.mp hv) with rfl | rfl
      · exact hb
      · exact hyB
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hedge, hall⟩, Sym2.mem_mk_left b y⟩
  · intro y₁ _ y₂ _ h
    exact Sym2.congr_right.mp h
  · intro e he
    have heD : e ∈ directBranchEdges G := (Finset.mem_filter.mp he).1
    have hbe : b ∈ e := (Finset.mem_filter.mp he).2
    let y := Sym2.Mem.other hbe
    have hpair : s(b, y) = e := Sym2.other_spec hbe
    have hyB : y ∈ B :=
      (Finset.mem_filter.mp heD).2 y (Sym2.other_mem hbe)
    have hadj : G.Adj b y := by
      have hedge : e ∈ G.edgeFinset := (Finset.mem_filter.mp heD).1
      rw [← hpair] at hedge
      exact G.mem_edgeSet.mp (G.mem_edgeFinset.mp hedge)
    refine ⟨y, ?_, hpair⟩
    exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset b y).mpr hadj, hyB⟩

/-- Pointwise degree of the edge-labelled suppressed multigraph.
Every path edge contributes its endpoint multiplicity, so a loop
contributes two; every original direct branch edge contributes one
at each incident branch vertex. -/
def kernelValence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (G.induce {v | G.degree v = 2}).ConnectedComponent]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (b : V) : ℕ :=
  (∑ C : (G.induce {v | G.degree v = 2}).ConnectedComponent,
    (degreeTwoPathEndpoints G hacyc C).toMultiset.count b) +
      ((directBranchEdges G).filter (fun e => b ∈ e)).card

/-- Suppressing degree-two paths preserves the degree of each branch
vertex exactly, with loops counted twice.  Thus the endpoint table
of a cubic core is genuinely cubic, not only of cubic total size. -/
theorem kernelValence_eq_original_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (G.induce {v | G.degree v = 2}).ConnectedComponent]
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (b : V) (hb : b ∈ branchingVertices G) :
    kernelValence G hacyc b = G.degree b := by
  let B := branchingVertices G
  have hbne : G.degree b ≠ 2 :=
    (mem_branchingVertices_iff_degree_ne_two G hmin b).mp hb
  have hB (v : V) : v ∈ B ↔ G.degree v ≠ 2 :=
    mem_branchingVertices_iff_degree_ne_two G hmin v
  have hfilter : (G.neighborFinset b).filter (· ∉ B) =
      (G.neighborFinset b).filter (fun v => G.degree v = 2) := by
    ext v
    simp only [Finset.mem_filter]
    rw [hB v]
    simp
  have hsplit : G.degree b =
      ((G.neighborFinset b).filter (· ∈ B)).card +
        ((G.neighborFinset b).filter
          (fun v => G.degree v = 2)).card := by
    calc
      G.degree b = (G.neighborFinset b).card :=
        (G.card_neighborFinset_eq_degree b).symm
      _ = ((G.neighborFinset b).filter (· ∈ B)).card +
          ((G.neighborFinset b).filter (· ∉ B)).card :=
        ((G.neighborFinset b).card_filter_add_card_filter_not (· ∈ B)).symm
      _ = _ := by rw [hfilter]
  unfold kernelValence
  rw [sum_degreeTwoPathEndpoints_count_eq_cross_neighbors G hacyc b hbne,
    directBranchEdges_incident_card_eq_branch_neighbors G b hb]
  simp only [B] at hsplit
  omega


#print axioms PerronWright.GraphCore.degreeTwoPathEndpoints_count_eq_boundaryStubs
#print axioms PerronWright.GraphCore.componentBoundaryStubs_at_branch_card
#print axioms PerronWright.GraphCore.sum_degreeTwoPathEndpoints_count_eq_cross_neighbors
#print axioms PerronWright.GraphCore.directBranchEdges_incident_card_eq_branch_neighbors
#print axioms PerronWright.GraphCore.kernelValence_eq_original_degree

end PerronWright.GraphCore
