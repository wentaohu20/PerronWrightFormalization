import PerronWright.Enumeration.FiniteKernelShape

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- A finite ambient collection of all edge-labelled endpoint tables
that can occur at fixed positive surplus.  The two `Fin` coordinates
record the actual numbers of branch vertices and kernel edge labels. -/
abbrev BoundedKernelShape (ell : ℕ) :=
  Σ nv : Fin (2 * ell + 1),
    Σ ne : Fin (3 * ell + 1),
      Fin ne.val → Sym2 (Fin nv.val)

theorem boundedKernelShape_finite (ell : ℕ) :
    Finite (BoundedKernelShape ell) := inferInstance

/-- Every actual connected positive-surplus two-core, with no
cubic restriction, has a genuinely bounded finite labelled endpoint
table.  In particular there are only finitely many such tables at
each fixed surplus before one imposes connectivity or valence. -/
def normalizedBoundedKernelShape
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell) :
    BoundedKernelShape ell := by
  let B := branchingVertices G
  let E := KernelEdgeLabel G
  let hacyc := degreeTwo_induced_isAcyclic G hconn hmin hell hs
  have hb : B.card ≤ 2 * ell :=
    branchingVertices_card_le_two_surplus G hmin hs
  have he : Nat.card E ≤ 3 * ell :=
    kernelEdgeLabel_card_le_three_surplus G hconn hmin hell hs
  let nv : Fin (2 * ell + 1) := ⟨B.card, by omega⟩
  let ne : Fin (3 * ell + 1) := ⟨Nat.card E, by omega⟩
  letI : Fintype (G.induce {v | G.degree v = 2}).ConnectedComponent :=
    Fintype.ofFinite _
  letI : Fintype {e : Sym2 V // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype E := by
    dsimp only [E, KernelEdgeLabel]
    infer_instance
  let eB : B ≃ Fin nv.val := Finset.equivFin B
  let eE : E ≃ Fin ne.val := by
    apply Fintype.equivFinOfCardEq
    simp only [ne, Nat.card_eq_fintype_card]
  exact ⟨nv, ne, fun i => Sym2.map eB
    (kernelBranchEndpoints G hmin hacyc (eE.symm i))⟩

set_option linter.style.haveILetI false in
/-- The bounded finite table is not merely a coarse invariant: the
original branch vertices and original kernel-edge labels have
equivalences to its finite coordinates, and every endpoint pair is
transported exactly by those equivalences. -/
theorem exists_exact_bounded_kernel_relabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell) :
    ∃ (nv : Fin (2 * ell + 1)) (ne : Fin (3 * ell + 1))
      (eB : (branchingVertices G : Set V) ≃ Fin nv.val)
      (eE : KernelEdgeLabel G ≃ Fin ne.val)
      (table : Fin ne.val → Sym2 (Fin nv.val)),
      ∀ e : KernelEdgeLabel G,
        table (eE e) =
          Sym2.map eB
            (kernelBranchEndpoints G hmin
              (degreeTwo_induced_isAcyclic G hconn hmin hell hs) e) := by
  let B := branchingVertices G
  let E := KernelEdgeLabel G
  let hacyc := degreeTwo_induced_isAcyclic G hconn hmin hell hs
  have hb : B.card ≤ 2 * ell :=
    branchingVertices_card_le_two_surplus G hmin hs
  have he : Nat.card E ≤ 3 * ell :=
    kernelEdgeLabel_card_le_three_surplus G hconn hmin hell hs
  let nv : Fin (2 * ell + 1) := ⟨B.card, by omega⟩
  let ne : Fin (3 * ell + 1) := ⟨Nat.card E, by omega⟩
  letI : Fintype (G.induce {v | G.degree v = 2}).ConnectedComponent :=
    Fintype.ofFinite _
  letI : Fintype {e : Sym2 V // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  letI : Fintype E := by
    dsimp only [E, KernelEdgeLabel]
    infer_instance
  let eB : B ≃ Fin nv.val := Finset.equivFin B
  let eE : E ≃ Fin ne.val := by
    apply Fintype.equivFinOfCardEq
    simp only [ne, Nat.card_eq_fintype_card]
  refine ⟨nv, ne, eB, eE,
    (fun i => Sym2.map eB
      (kernelBranchEndpoints G hmin hacyc (eE.symm i))), ?_⟩
  intro e
  simp only [Equiv.symm_apply_apply]

#print axioms PerronWright.GraphCore.boundedKernelShape_finite
#print axioms PerronWright.GraphCore.normalizedBoundedKernelShape
#print axioms PerronWright.GraphCore.exists_exact_bounded_kernel_relabeling

end PerronWright.GraphCore
