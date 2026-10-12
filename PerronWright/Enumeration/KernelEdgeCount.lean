import PerronWright.Enumeration.KernelEdges

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- The vertex set is the disjoint union of its connected components. -/
def componentVertexEquiv
    {V : Type*} (H : SimpleGraph V) :
    (Σ C : H.ConnectedComponent, C) ≃ V where
  toFun s := s.2.val
  invFun v := ⟨H.connectedComponentMk v,
    ⟨v, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩⟩
  left_inv := by
    rintro ⟨C, ⟨v, hv⟩⟩
    have heq : H.connectedComponentMk v = C := hv
    cases heq
    rfl
  right_inv := by intro v; rfl

theorem sum_over_connected_components
    {V : Type*} [Fintype V] (H : SimpleGraph V)
    [Fintype H.ConnectedComponent]
    (f : V → ℕ) :
    (∑ C : H.ConnectedComponent, ∑ x : C, f x.val) =
      ∑ v : V, f v := by
  calc
    _ = ∑ s : (Σ C : H.ConnectedComponent, C), f s.2.val := by
      rw [Fintype.sum_sigma]
    _ = ∑ v : V, f v :=
      Fintype.sum_equiv (componentVertexEquiv H)
        (fun s => f s.2.val) f (by intro s; rfl)

set_option linter.style.haveILetI false in
/-- The number of path components of the actual degree-two forest is
its Euler deficit: number of degree-two vertices minus internal edges. -/
theorem degreeTwo_components_eq_eulerDeficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic) :
    Nat.card (G.induce {v | G.degree v = 2}).ConnectedComponent =
      Fintype.card {v : V | G.degree v = 2} -
        (G.induce {v | G.degree v = 2}).edgeFinset.card := by
  let H := G.induce {v | G.degree v = 2}
  haveI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have hsum :
      2 * Fintype.card H.ConnectedComponent =
        degreeTwoBoundaryIncidences G := by
    calc
      2 * Fintype.card H.ConnectedComponent =
          ∑ C : H.ConnectedComponent, (2 : ℕ) := by simp [Finset.sum_const, mul_comm]
      _ = ∑ C : H.ConnectedComponent,
            ∑ x : C,
              ((G.neighborFinset x.val.val).filter
                (fun y => G.degree y ≠ 2)).card := by
          apply Finset.sum_congr rfl
          intro C _
          exact (degreeTwo_component_boundary_stubs_eq_two G hacyc C).symm
      _ = ∑ x : {v : V | G.degree v = 2},
            ((G.neighborFinset x.val).filter
              (fun y => G.degree y ≠ 2)).card := by
          exact sum_over_connected_components H
            (fun x => ((G.neighborFinset x.val).filter
              (fun y => G.degree y ≠ 2)).card)
      _ = degreeTwoBoundaryIncidences G := rfl
  rw [degreeTwoBoundaryIncidences_eq_twice_eulerDeficit] at hsum
  rw [Nat.card_eq_fintype_card]
  change 2 * Fintype.card H.ConnectedComponent =
    2 * (Fintype.card {v : V | G.degree v = 2} - H.edgeFinset.card) at hsum
  have hcount : Fintype.card H.ConnectedComponent =
      Fintype.card {v : V | G.degree v = 2} - H.edgeFinset.card := by
    omega
  simpa only [H] using hcount

#print axioms PerronWright.GraphCore.componentVertexEquiv
#print axioms PerronWright.GraphCore.degreeTwo_components_eq_eulerDeficit

end PerronWright.GraphCore
