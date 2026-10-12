import PerronWright.Enumeration.DegreeTwoPaths

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Actual boundary incidences of one degree-two component.  A stub
retains both its internal vertex and its outside endpoint, so two
stubs ending at the same branch vertex remain distinct. -/
def componentBoundaryStubs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : (G.induce {v | G.degree v = 2}).ConnectedComponent) :
    Finset (Σ _x : C, V) :=
  (Finset.univ : Finset C).sigma (fun x =>
    (G.neighborFinset x.val.val).filter (fun y => G.degree y ≠ 2))

/-- A component of the actual degree-two forest has precisely two
boundary stubs, counted with multiplicity at their outside endpoints. -/
theorem componentBoundaryStubs_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (C : (G.induce {v | G.degree v = 2}).ConnectedComponent) :
    (componentBoundaryStubs G C).card = 2 := by
  rw [componentBoundaryStubs, Finset.card_sigma]
  exact degreeTwo_component_boundary_stubs_eq_two G hacyc C

/-- The canonical (unordered) pair of outside endpoints of a
degree-two path component.  Using a multiset before converting to
`Sym2` preserves loops: both stubs may end at the same branch vertex. -/
def degreeTwoPathEndpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (C : (G.induce {v | G.degree v = 2}).ConnectedComponent) : Sym2 V :=
  (Sym2.equivMultiset V).symm
    ⟨(componentBoundaryStubs G C).val.map Sigma.snd,
      by simpa using componentBoundaryStubs_card_eq_two G hacyc C⟩

set_option maxHeartbeats 1000000 in
private theorem equivMultiset_val_eq_toMultiset
    {V : Type*} (e : Sym2 V) :
    (Sym2.equivMultiset V e).val = e.toMultiset := by
  induction e using Sym2.inductionOn with
  | _ a b => rfl

set_option maxHeartbeats 1000000 in
theorem degreeTwoPathEndpoints_toMultiset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (C : (G.induce {v | G.degree v = 2}).ConnectedComponent) :
    (degreeTwoPathEndpoints G hacyc C).toMultiset =
      (componentBoundaryStubs G C).val.map Sigma.snd := by
  rw [← equivMultiset_val_eq_toMultiset]
  unfold degreeTwoPathEndpoints
  simp

/-- Every endpoint of the canonical kernel edge is witnessed by an
actual incidence from its degree-two component. -/
theorem degreeTwoPathEndpoints_mem_has_stub
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (C : (G.induce {v | G.degree v = 2}).ConnectedComponent)
    {b : V} (hb : b ∈ degreeTwoPathEndpoints G hacyc C) :
    ∃ x : C, G.Adj x.val.val b ∧ G.degree b ≠ 2 := by
  rw [← Sym2.mem_toMultiset, degreeTwoPathEndpoints_toMultiset] at hb
  obtain ⟨s, hs, hsb⟩ := Multiset.mem_map.mp hb
  have hs' : s ∈ componentBoundaryStubs G C := hs
  rcases s with ⟨x, y⟩
  simp only [componentBoundaryStubs, Finset.mem_sigma, Finset.mem_univ,
    true_and, Finset.mem_filter, G.mem_neighborFinset] at hs'
  change y = b at hsb
  subst b
  exact ⟨x, hs'.1, hs'.2⟩

/-- In a minimum-degree-two core, both outside endpoints of a
subdivided-path kernel edge are genuine branch vertices. -/
theorem degreeTwoPathEndpoints_mem_branchingVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (C : (G.induce {v | G.degree v = 2}).ConnectedComponent)
    {b : V} (hb : b ∈ degreeTwoPathEndpoints G hacyc C) :
    b ∈ branchingVertices G := by
  obtain ⟨_, _, hne⟩ := degreeTwoPathEndpoints_mem_has_stub G hacyc C hb
  have hthree : 3 ≤ G.degree b := by
    have htwo := hmin b
    omega
  simpa [branchingVertices] using hthree

/-- The direct kernel edges are exactly the original edges whose two
endpoints are already branch vertices. -/
def directBranchEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ b ∈ e, b ∈ branchingVertices G)

/-- Edge labels of the finite suppressed kernel: each degree-two
component contributes one new edge, while every direct branch edge
keeps its original distinct label.  The sum type preserves parallel
edges and loops created by the path-edge endpoints. -/
def KernelEdgeLabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Type _ :=
  Sum (G.induce {v | G.degree v = 2}).ConnectedComponent
    {e : Sym2 V // e ∈ directBranchEdges G}

/-- The actual endpoint map of the suppressed finite multigraph. -/
def kernelEdgeEndpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic) :
    KernelEdgeLabel G → Sym2 V
  | .inl C => degreeTwoPathEndpoints G hacyc C
  | .inr e => e.val

/-- Both ends of every labelled suppressed-kernel edge are genuine
branch vertices. -/
theorem kernelEdgeEndpoints_mem_branchingVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (e : KernelEdgeLabel G) {b : V}
    (hb : b ∈ kernelEdgeEndpoints G hacyc e) :
    b ∈ branchingVertices G := by
  cases e with
  | inl C =>
      exact degreeTwoPathEndpoints_mem_branchingVertices G hmin hacyc C hb
  | inr e =>
      exact (Finset.mem_filter.mp e.property).2 b hb

#print axioms PerronWright.GraphCore.componentBoundaryStubs_card_eq_two
#print axioms PerronWright.GraphCore.degreeTwoPathEndpoints
#print axioms PerronWright.GraphCore.degreeTwoPathEndpoints_mem_branchingVertices
#print axioms PerronWright.GraphCore.kernelEdgeEndpoints_mem_branchingVertices

end PerronWright.GraphCore

