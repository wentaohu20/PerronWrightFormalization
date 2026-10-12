import PerronWright.Enumeration.KernelValence

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- A direct branch edge of the original simple graph contributes
exactly one endpoint incidence at each of its two distinct ends. -/
theorem simpleEdge_toMultiset_count_eq_ite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Sym2 V} (he : e ∈ G.edgeFinset) (b : V) :
    e.toMultiset.count b = if b ∈ e then 1 else 0 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : x ≠ y := (G.mem_edgeSet.mp (G.mem_edgeFinset.mp he)).ne
      by_cases hbx : b = x
      · subst b
        simp [Sym2.toMultiset, Sym2.mem_iff, hxy]
      · by_cases hby : b = y
        · subst b
          simp [Sym2.toMultiset, Sym2.mem_iff, hbx, hxy]
        · simp [Sym2.toMultiset, Sym2.mem_iff, hbx, hby]

/-- Sum of literal endpoint multiplicities over direct branch edges
equals the number of such edges incident to `b`. -/
theorem sum_directBranchEdges_endpoint_count_eq_incident_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : V) :
    (∑ e ∈ directBranchEdges G, e.toMultiset.count b) =
      ((directBranchEdges G).filter (fun e => b ∈ e)).card := by
  calc
    (∑ e ∈ directBranchEdges G, e.toMultiset.count b) =
        ∑ e ∈ directBranchEdges G, if b ∈ e then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      exact simpleEdge_toMultiset_count_eq_ite G
        (Finset.mem_filter.mp he).1 b
    _ = _ := by
      rw [← Finset.sum_filter]
      simp

/-- Literal endpoint-multiplicity sum over all labelled kernel edges,
split into path-component labels and direct original-edge labels. -/
def kernelEndpointValence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (G.induce {v | G.degree v = 2}).ConnectedComponent]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (b : V) : ℕ :=
  (∑ C : (G.induce {v | G.degree v = 2}).ConnectedComponent,
    (degreeTwoPathEndpoints G hacyc C).toMultiset.count b) +
      (∑ e ∈ directBranchEdges G, e.toMultiset.count b)

theorem kernelEndpointValence_eq_kernelValence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (G.induce {v | G.degree v = 2}).ConnectedComponent]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (b : V) :
    kernelEndpointValence G hacyc b = kernelValence G hacyc b := by
  unfold kernelEndpointValence kernelValence
  rw [sum_directBranchEdges_endpoint_count_eq_incident_card]

/-- The total literal endpoint multiplicity at any branch vertex
equals its degree in the original core graph. -/
theorem kernelEndpointValence_eq_original_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (G.induce {v | G.degree v = 2}).ConnectedComponent]
    (hmin : ∀ v, 2 ≤ G.degree v)
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (b : V) (hb : b ∈ branchingVertices G) :
    kernelEndpointValence G hacyc b = G.degree b := by
  rw [kernelEndpointValence_eq_kernelValence]
  exact kernelValence_eq_original_degree G hmin hacyc b hb

set_option linter.style.haveILetI false in
/-- The endpoint multiplicity definition agrees with a single sum
over the actual sum-type labels of the suppressed multigraph. -/
theorem kernelEndpointValence_eq_sum_edgeLabels
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (G.induce {v | G.degree v = 2}).ConnectedComponent]
    [instE : Fintype (KernelEdgeLabel G)]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic)
    (b : V) :
    kernelEndpointValence G hacyc b =
      ∑ e : KernelEdgeLabel G,
        (kernelEdgeEndpoints G hacyc e).toMultiset.count b := by
  let B := directBranchEdges G
  letI : Fintype {e : Sym2 V // e ∈ B} := FinsetCoe.fintype B
  have hsub := Finset.sum_subtype (F := FinsetCoe.fintype B)
    B (fun e => Iff.rfl) (fun e => e.toMultiset.count b)
  calc
    kernelEndpointValence G hacyc b =
        (∑ C : (G.induce {v | G.degree v = 2}).ConnectedComponent,
          (degreeTwoPathEndpoints G hacyc C).toMultiset.count b) +
        (∑ e : {e : Sym2 V // e ∈ B}, e.val.toMultiset.count b) := by
      unfold kernelEndpointValence
      change (∑ C : (G.induce {v | G.degree v = 2}).ConnectedComponent,
        (degreeTwoPathEndpoints G hacyc C).toMultiset.count b) +
        (∑ e ∈ B, e.toMultiset.count b) = _
      rw [hsub]
      rfl
    _ = _ := by
      calc
        _ = ∑ e : Sum
            (G.induce {v | G.degree v = 2}).ConnectedComponent
            {e : Sym2 V // e ∈ B},
            (kernelEdgeEndpoints G hacyc e).toMultiset.count b := by
          rw [Fintype.sum_sum_type]
          rfl
        _ = _ := by
          refine Finset.sum_congr (by
            ext e
            exact ⟨fun _ => @Finset.mem_univ (KernelEdgeLabel G) instE e,
              fun _ => Finset.mem_univ e⟩) ?_
          intro e _
          rfl

#print axioms PerronWright.GraphCore.simpleEdge_toMultiset_count_eq_ite
#print axioms PerronWright.GraphCore.sum_directBranchEdges_endpoint_count_eq_incident_card
#print axioms PerronWright.GraphCore.kernelEndpointValence_eq_original_degree
#print axioms PerronWright.GraphCore.kernelEndpointValence_eq_sum_edgeLabels

end PerronWright.GraphCore
